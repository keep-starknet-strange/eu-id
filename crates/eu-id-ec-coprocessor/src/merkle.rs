use blake2::{Blake2s256, Digest};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

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

/// Canonical authentication of several transcript-selected columns.
///
/// Columns are concatenated in the caller-supplied index order. The indices
/// themselves are transcript-derived and therefore are not serialized.
/// `frontier` contains only missing siblings, in level/index order.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ColumnBatchOpening {
    pub columns: Vec<Fp>,
    pub frontier: Vec<[u8; 32]>,
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
    DuplicateColumn,
    ZeroColumnLength,
    WrongBatchLength,
    InvalidBatchProof,
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

    pub fn open_batch(&self, indices: &[usize]) -> Result<ColumnBatchOpening, MerkleError> {
        validate_indices(indices, self.columns.len())?;

        let mut columns = Vec::with_capacity(indices.len() * self.columns[0].len());
        for &index in indices {
            columns.extend_from_slice(&self.columns[index]);
        }

        let mut frontier = Vec::new();
        let mut known = indices.iter().copied().collect::<BTreeSet<_>>();
        let mut width = self.columns.len();
        for level in &self.levels[..self.levels.len() - 1] {
            for &index in &known {
                let sibling = index ^ 1;
                if sibling < width && !known.contains(&sibling) {
                    frontier.push(level[sibling]);
                }
            }
            known = known.into_iter().map(|index| index / 2).collect();
            width = width.div_ceil(2);
        }

        Ok(ColumnBatchOpening { columns, frontier })
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

/// Verifies a canonical batch opening.
///
/// Every frontier hash must be consumed exactly once. Missing, extra, or
/// reordered columns/frontier hashes therefore fail closed.
pub fn verify_batch(
    root: [u8; 32],
    width: usize,
    indices: &[usize],
    column_len: usize,
    opening: &ColumnBatchOpening,
) -> Result<bool, MerkleError> {
    validate_indices(indices, width)?;
    if column_len == 0 {
        return Err(MerkleError::ZeroColumnLength);
    }
    let expected_values = indices
        .len()
        .checked_mul(column_len)
        .ok_or(MerkleError::WrongBatchLength)?;
    if opening.columns.len() != expected_values {
        return Err(MerkleError::WrongBatchLength);
    }

    let mut known = BTreeMap::new();
    for (&index, column) in indices.iter().zip(opening.columns.chunks_exact(column_len)) {
        known.insert(index, leaf_hash(index, column));
    }

    let mut frontier = opening.frontier.iter().copied();
    let mut level_width = width;
    while level_width > 1 {
        let mut parents = BTreeMap::new();
        for (&index, &hash) in &known {
            let sibling_index = index ^ 1;
            if index & 1 == 1 && known.contains_key(&sibling_index) {
                continue;
            }
            let sibling = if sibling_index >= level_width {
                hash
            } else if let Some(&sibling) = known.get(&sibling_index) {
                sibling
            } else {
                frontier.next().ok_or(MerkleError::InvalidBatchProof)?
            };
            let parent = if index & 1 == 0 {
                node_hash(hash, sibling)
            } else {
                node_hash(sibling, hash)
            };
            if parents.insert(index / 2, parent).is_some() {
                return Err(MerkleError::InvalidBatchProof);
            }
        }
        known = parents;
        level_width = level_width.div_ceil(2);
    }

    if frontier.next().is_some() || known.len() != 1 {
        return Err(MerkleError::InvalidBatchProof);
    }
    Ok(known.get(&0) == Some(&root))
}

fn validate_indices(indices: &[usize], width: usize) -> Result<(), MerkleError> {
    if width == 0 || indices.is_empty() {
        return Err(MerkleError::EmptyMatrix);
    }
    let mut unique = BTreeSet::new();
    for &index in indices {
        if index >= width {
            return Err(MerkleError::ColumnOutOfRange);
        }
        if !unique.insert(index) {
            return Err(MerkleError::DuplicateColumn);
        }
    }
    Ok(())
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
