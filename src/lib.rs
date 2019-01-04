//! Generetes complete merkle tree root.
//!
//! This module should be used to generate complete merkle tree root hash.

use std::cmp::PartialEq;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct Tree<T, M> {
    nodes: Vec<T>,
    leaf_size: usize,
    phanton: PhantomData<M>,
}

#[derive(Debug, Clone)]
pub struct ProofNode<T> {
    pub is_right: bool,
    pub hash: T,
}

#[derive(Debug, Clone)]
pub struct Proof<T>(pub Vec<ProofNode<T>>);

impl<T, M> Tree<T, M>
where
    T: Default + Clone + PartialEq,
    M: Fn(&T, &T) -> T,
{
    // For example, there is 11 hashes [A..K] are used to generate a merkle tree:
    //
    //                     0
    //                     |
    //             1---------------2
    //             |               |
    //         3-------4       5-------6
    //         |       |       |       |
    //       7---8   9---A   B---C   D---E
    //       |   |   |
    //      F-G H-I J-K
    //
    // The algorithm is:
    //
    //      1. Create a vec:    [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _]
    //      2. Insert A..K:     [_, _, _, _, _, _, _, _, _, _, A, B, C, D, E, F, G, H, I, J, K]
    //      3. Update for 7..9: [_, _, _, _, _, _, _, 7, 8, 9, A, B, C, D, E, F, G, H, I, J, K]
    //      4. Update for 3..6: [_, _, _, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F, G, H, I, J, K]
    //      5. Update for 1..2: [_, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F, G, H, I, J, K]
    //      6. Update for 0:    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F, G, H, I, J, K]
    pub fn from_hashes(input: Vec<T>, merge: M) -> Self {
        let leaf_size = input.len();

        let nodes = match leaf_size {
            0 => vec![],

            // If only one input.
            1 => input,

            _ => {
                let nodes_number = get_number_of_nodes(leaf_size);
                let mut nodes = vec![T::default(); nodes_number];

                let depth = get_depth(leaf_size);

                let first_input_node_index = nodes_number - leaf_size;
                let first_index_in_lowest_row = (1 << depth) - 1;
                let nodes_number_of_lowest_row = nodes_number - first_index_in_lowest_row;

                // Insert the input into the merkle tree.
                nodes[first_input_node_index..nodes_number].clone_from_slice(&input);

                let max_nodes_number_of_lowest_row = 1 << depth;
                // Calc hash for the lowest row
                if max_nodes_number_of_lowest_row == leaf_size {
                    // The lowest row is full.
                    calc_tree_at_row(&mut nodes, depth, 0, &merge)
                } else {
                    calc_tree_at_row(&mut nodes, depth, nodes_number_of_lowest_row >> 1, &merge);
                }

                // From the second row from the bottom to the second row from the top.
                for i in 1..depth {
                    let row_index = depth - i;
                    calc_tree_at_row(&mut nodes, row_index, 0, &merge);
                }

                nodes
            }
        };

        Self {
            nodes,
            leaf_size,
            phanton: PhantomData,
        }
    }

    pub fn get_root_hash(&self) -> Option<&T> {
        self.nodes.get(0)
    }

    pub fn get_proof_by_input_index(&self, input_index: usize) -> Option<Proof<T>> {
        get_proof_indexes(input_index, self.leaf_size).map(|indexes| {
            Proof::<T>(
                indexes
                    .into_iter()
                    .map(|i| ProofNode::<T> {
                        is_right: (i & 1) == 0,
                        hash: self.nodes[i].clone(),
                    })
                    .collect(),
            )
        })
    }
}

impl<T> Proof<T>
where
    T: Default + Clone + PartialEq,
{
    pub fn verify<M>(&self, root: &T, data: T, merge: M) -> bool
    where
        M: Fn(&T, &T) -> T,
    {
        &self.0.iter().fold(data, |h, ref x| {
            if x.is_right {
                merge(&h, &x.hash)
            } else {
                merge(&x.hash, &h)
            }
        }) == root
    }
}

// Calc hash for one row in merkle tree.
// If break_cnt > 0, just calc break_cnt hash for that row.
fn calc_tree_at_row<T, M>(nodes: &mut Vec<T>, row_index: usize, break_cnt: usize, merge: M)
where
    M: Fn(&T, &T) -> T,
{
    // The first index in the row which above the row_index row.
    let index_update = (1 << (row_index - 1)) - 1;
    let size_max = 1 << (row_index - 1);
    let size_update = if break_cnt > 0 && break_cnt < size_max {
        break_cnt
    } else {
        size_max
    };
    for i in 0..size_update {
        let j = index_update + i;
        nodes[j] = merge(&nodes[j * 2 + 1], &nodes[j * 2 + 2]);
    }
}

#[inline]
fn get_depth(m: usize) -> usize {
    let mut x: usize = 1;
    let mut y: usize = 0;
    while x < m {
        x <<= 1;
        y += 1;
    }
    y
}

#[inline]
fn get_number_of_nodes(m: usize) -> usize {
    // The depth for m:
    //      depth = get_depth(m);
    // The second row from the bottom (math index):
    //      y = depth;
    // Number of nodes for the second row from the bottom:
    //      z = 2 ^ (y - 1);
    // Number of nodes above the lowest row:
    //      n1 = 2 ^ y - 1;
    // Number of nodes in the lowest row:
    //      n2 = (m - z) * 2;
    // Returns:
    //      n1 + n2
    //      = (2 ^ y - 1) + ((m - z) * 2)
    //      = m * 2  - 1
    if m == 0 {
        1
    } else {
        m * 2 - 1
    }
}

#[inline]
fn get_index_of_brother_and_father(index: usize) -> (usize, usize) {
    // Convert computer index (start from 0) to math index (start from 1).
    let math_index = index + 1;
    // The only one difference between brother math indexes in binary tree is the last bit.
    let math_index_for_brother = (math_index & ((!0) - 1)) + ((!math_index) & 1);
    let math_index_for_father = math_index >> 1;
    // Convert back to computer index.
    (math_index_for_brother - 1, math_index_for_father - 1)
}

#[inline]
fn get_proof_indexes(input_index: usize, leaf_size: usize) -> Option<Vec<usize>> {
    if input_index == 0 && leaf_size < 2 {
        Some(vec![])
    } else if leaf_size != 0 && input_index < leaf_size {
        let mut ret = Vec::new();
        let nodes_number = get_number_of_nodes(leaf_size);
        let mut index = nodes_number - leaf_size + input_index;
        while index > 0 {
            let (brother_index, parent_index) = get_index_of_brother_and_father(index);
            ret.push(brother_index);
            index = parent_index;
        }
        Some(ret)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    #[derive(Default, Clone, PartialEq, Debug)]
    struct Node(Vec<u32>);

    fn merge(left: &Node, right: &Node) -> Node {
        let mut root: Vec<u32> = vec![];
        root.extend_from_slice(&left.0);
        root.extend_from_slice(&right.0);
        Node(root)
    }

    #[test]
    fn test_depth() {
        let check = vec![
            (0, 0),
            (1, 0),
            (2, 1),
            (3, 2),
            (4, 2),
            (5, 3),
            (8, 3),
            (9, 4),
            (16, 4),
            (17, 5),
        ];
        for (x, y) in check {
            assert_eq!(y, super::get_depth(x));
        }
    }

    #[test]
    fn test_number_of_nodes() {
        let check = vec![
            (0, 1),
            (1, 1),
            (2, 3),
            (3, 5),
            (4, 7),
            (5, 9),
            (8, 15),
            (9, 17),
            (16, 31),
            (20, 39),
        ];
        for (x, y) in check {
            assert_eq!(y, super::get_number_of_nodes(x));
        }
    }

    #[test]
    fn test_index_of_brother_and_father() {
        let check = vec![
            (1, (2, 0)),
            (2, (1, 0)),
            (11, (12, 5)),
            (12, (11, 5)),
            (21, (22, 10)),
            (22, (21, 10)),
            (31, (32, 15)),
            (32, (31, 15)),
        ];
        for (x, y) in check {
            assert_eq!(y, super::get_index_of_brother_and_father(x));
        }
    }

    #[test]
    fn test_proof_indexes() {
        let check = vec![
            ((1, 0), None),
            ((1, 1), None),
            ((2, 1), None),
            ((2, 2), None),
            ((0, 0), Some(vec![])),
            ((0, 1), Some(vec![])),
            ((0, 11), Some(vec![9, 3, 2])),
            ((10, 11), Some(vec![19, 10, 3, 2])),
            ((9, 11), Some(vec![20, 10, 3, 2])),
            ((8, 11), Some(vec![17, 7, 4, 2])),
        ];
        for ((x1, x2), y) in check {
            assert_eq!(y, super::get_proof_indexes(x1, x2));
        }
    }

    #[test]
    fn test_proof() {
        let inputs = vec![
            vec![Node(vec![1u32])],
            (1u32..26u32).map(|i| Node(vec![i])).collect(),
        ];
        for input in inputs {
            let tree = super::Tree::from_hashes(input.clone(), merge);
            let root_hash = tree.get_root_hash().unwrap().clone();
            let leaf_size = input.len();
            let loop_size = if leaf_size == 0 { 1 } else { leaf_size };
            for (index, item) in input.into_iter().enumerate().take(loop_size) {
                let proof = tree
                    .get_proof_by_input_index(index)
                    .expect("proof is not none");
                assert!(proof.verify(&root_hash, item, merge));
            }
        }
    }

    #[test]
    fn test_root() {
        assert_root(&(0u32..12u32).collect::<Vec<u32>>());
        assert_root(&(0u32..11u32).collect::<Vec<u32>>());
        assert_root(&[1u32, 5u32, 100u32, 4u32, 7u32, 9u32, 11u32]);
        assert_root(&(0u32..27u32).collect::<Vec<u32>>());
    }

    fn assert_root(raw: &[u32]) {
        let leaves: Vec<Node> = raw.iter().map(|i| Node(vec![*i])).collect();
        let leaves_len = leaves.len();
        let tree = super::Tree::from_hashes(leaves, merge);
        let root = tree.get_root_hash().unwrap();
        let depth = super::get_depth(leaves_len);
        let nodes_number = super::get_number_of_nodes(leaves_len);
        let last_row_number = nodes_number - 2usize.pow(depth as u32) + 1;
        let first_part_index = leaves_len - last_row_number;
        let mut first_part = raw[first_part_index..leaves_len]
            .iter()
            .cloned()
            .map(|i| i)
            .collect::<Vec<u32>>();
        let second_part = raw[0..first_part_index]
            .iter()
            .cloned()
            .map(|i| i)
            .collect::<Vec<u32>>();
        first_part.extend_from_slice(&second_part);
        assert_eq!(root, &Node(first_part));
    }
}
