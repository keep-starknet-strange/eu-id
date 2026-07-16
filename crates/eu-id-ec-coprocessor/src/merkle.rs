use blake2::{Blake2s256, Digest};
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

    let mut columns = vec![Vec::with_capacity(rows.len()); width];
    for row in rows {
        for (i, value) in row.iter().copied().enumerate() {
            columns[i].push(value);
        }
    }

    let leaves = columns
        .iter()
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
        let mut next = Vec::with_capacity(current.len().div_ceil(2));
        for pair in current.chunks(2) {
            let right = if pair.len() == 2 { pair[1] } else { pair[0] };
            next.push(node_hash(pair[0], right));
        }
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
