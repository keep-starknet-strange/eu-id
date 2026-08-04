use blake2::{Blake2s256, Digest};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use crate::Fp;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MerkleCommitment {
    root: [u8; 32],
    columns: Vec<Vec<Fp>>,
    levels: Vec<Vec<[u8; 32]>>,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ColumnOpening {
    pub index: usize,
    pub column: Vec<Fp>,
    pub path: Vec<MerkleSibling>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct MerkleSibling {
    pub hash: [u8; 32],
    pub is_right: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MerkleError {
    EmptyMatrix,
    RaggedMatrix,
    ColumnOutOfRange,
}

pub fn commit_columns(rows: &[Vec<Fp>]) -> Result<MerkleCommitment, MerkleError> {
    if rows.is_empty() || rows[0].is_empty() {
        return Err(MerkleError::EmptyMatrix);
    }
    let width = rows[0].len();
    if rows.iter().any(|row| row.len() != width) {
        return Err(MerkleError::RaggedMatrix);
    }

    let columns = (0..width)
        .into_par_iter()
        .map(|column| rows.iter().map(|row| row[column]).collect::<Vec<_>>())
        .collect::<Vec<_>>();

    let leaves = columns
        .par_iter()
        .enumerate()
        .map(|(index, column)| leaf_hash(index, column))
        .collect::<Vec<_>>();
    let levels = build_levels(leaves);
    let root = levels.last().expect("has root")[0];
    Ok(MerkleCommitment {
        root,
        columns,
        levels,
    })
}

impl MerkleCommitment {
    pub fn root(&self) -> [u8; 32] {
        self.root
    }

    /// Number of `Fp` values held in the transposed column copy of the
    /// committed matrix. This copy lives alongside the caller's row-major
    /// matrix for the whole life of the commitment, so it counts twice
    /// towards prover peak memory.
    pub fn column_values(&self) -> usize {
        self.columns.iter().map(Vec::len).sum()
    }

    /// Number of 32-byte digests retained across every tree level.
    pub fn node_count(&self) -> usize {
        self.levels.iter().map(Vec::len).sum()
    }

    pub fn open(&self, index: usize) -> Result<ColumnOpening, MerkleError> {
        if index >= self.columns.len() {
            return Err(MerkleError::ColumnOutOfRange);
        }
        let mut path = Vec::new();
        let mut cursor = index;
        for level in &self.levels[..self.levels.len() - 1] {
            let sibling_index = if cursor % 2 == 0 {
                cursor + 1
            } else {
                cursor - 1
            };
            let sibling = level
                .get(sibling_index)
                .copied()
                .unwrap_or_else(|| level[cursor]);
            path.push(MerkleSibling {
                hash: sibling,
                is_right: cursor % 2 == 0,
            });
            cursor /= 2;
        }
        Ok(ColumnOpening {
            index,
            column: self.columns[index].clone(),
            path,
        })
    }
}

pub fn verify_column(root: [u8; 32], opening: &ColumnOpening) -> Result<bool, MerkleError> {
    let mut hash = leaf_hash(opening.index, &opening.column);
    for sibling in &opening.path {
        hash = if sibling.is_right {
            node_hash(hash, sibling.hash)
        } else {
            node_hash(sibling.hash, hash)
        };
    }
    Ok(hash == root)
}

fn build_levels(mut current: Vec<[u8; 32]>) -> Vec<Vec<[u8; 32]>> {
    let mut levels = vec![current.clone()];
    while current.len() > 1 {
        let next = current
            .par_chunks(2)
            .map(|pair| {
                let right = if pair.len() == 2 { pair[1] } else { pair[0] };
                node_hash(pair[0], right)
            })
            .collect::<Vec<_>>();
        current = next;
        levels.push(current.clone());
    }
    levels
}

fn leaf_hash(index: usize, column: &[Fp]) -> [u8; 32] {
    let mut hasher = Blake2s256::new();
    hasher.update(b"eu-id-s4-ligero-leaf-v1");
    hasher.update((index as u64).to_be_bytes());
    hasher.update((column.len() as u64).to_be_bytes());
    for value in column {
        hasher.update(value.to_bytes_be());
    }
    finalize_hash(hasher)
}

fn node_hash(left: [u8; 32], right: [u8; 32]) -> [u8; 32] {
    let mut hasher = Blake2s256::new();
    hasher.update(b"eu-id-s4-ligero-node-v1");
    hasher.update(left);
    hasher.update(right);
    finalize_hash(hasher)
}

fn finalize_hash(hasher: Blake2s256) -> [u8; 32] {
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}
