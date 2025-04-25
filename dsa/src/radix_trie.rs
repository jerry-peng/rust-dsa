//! Radix tree implementation (with unicode support)

use std::collections::HashMap;
use std::mem;
use std::str::Bytes;

#[derive(Debug, PartialEq)]
pub struct RadixTree {
    root: Node,
    size: usize,
}

#[derive(Debug, PartialEq)]
struct Node {
    nodes: HashMap<u8, Node>,
    chunk: Vec<u8>,
    is_end: bool,
}

#[derive(PartialEq, Debug)]
pub struct DuplicateItemErr;

enum ChunkCmpStatus {
    Identical,
    WordInChunk {
        key: u8,
        chunk_remain: Vec<u8>,
    },
    ChunkInWord {
        key: u8,
    },
    Mismatch {
        word_key: u8,
        chunk_key: u8,
        chunk_remain: Vec<u8>,
    },
}

impl Node {
    fn split(&mut self, key: u8, child_chunk: Vec<u8>, is_end: bool) {
        let new_node = Node {
            nodes: mem::take(&mut self.nodes),
            chunk: child_chunk,
            is_end: self.is_end,
        };

        self.chunk
            .truncate(self.chunk.len() - new_node.chunk.len() - 1);
        self.is_end = is_end;
        self.nodes.insert(key, new_node);
    }

    fn extend(&mut self, key: u8, chunk: Vec<u8>) {
        self.nodes.insert(
            key,
            Node {
                nodes: HashMap::new(),
                chunk,
                is_end: true,
            },
        );
    }

    fn merge(&mut self) {
        assert!(self.nodes.len() == 1 && !self.is_end);
        let (key, node) = &mut mem::take(&mut self.nodes).into_iter().collect::<Vec<_>>()[0];
        self.chunk.push(*key);
        self.chunk.append(&mut mem::take(&mut node.chunk));
        mem::swap(&mut self.nodes, &mut node.nodes);
        self.is_end = node.is_end;
    }

    pub fn cmp_chunk(word_iter: &mut Bytes<'_>, chunk: &[u8]) -> ChunkCmpStatus {
        let mut chunk_iter = chunk.iter();
        loop {
            let word_byte_opt = word_iter.next();
            let chunk_byte_opt = chunk_iter.next();

            match (word_byte_opt, chunk_byte_opt) {
                (None, None) => return ChunkCmpStatus::Identical,
                (None, Some(chunk_byte)) => {
                    return ChunkCmpStatus::WordInChunk {
                        key: *chunk_byte,
                        chunk_remain: chunk_iter.copied().collect(),
                    };
                }
                (Some(word_byte), None) => {
                    return ChunkCmpStatus::ChunkInWord { key: word_byte };
                }
                (Some(word_byte), Some(chunk_byte)) if word_byte != *chunk_byte => {
                    return ChunkCmpStatus::Mismatch {
                        word_key: word_byte,
                        chunk_key: *chunk_byte,
                        chunk_remain: chunk_iter.copied().collect(),
                    };
                }
                (Some(_), Some(_)) => {}
            }
        }
    }
}

impl RadixTree {
    pub fn new() -> RadixTree {
        RadixTree {
            root: Node {
                nodes: HashMap::new(),
                chunk: Vec::new(),
                is_end: false,
            },
            size: 0,
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn insert(&mut self, word: &str) -> Result<(), DuplicateItemErr> {
        let mut curr_node = &mut self.root;
        let mut word_iter = word.bytes();

        loop {
            let chunk = &curr_node.chunk;
            match Node::cmp_chunk(&mut word_iter, chunk) {
                ChunkCmpStatus::Identical => {
                    return match curr_node.is_end {
                        true => Err(DuplicateItemErr),
                        false => {
                            curr_node.is_end = true;
                            break;
                        }
                    };
                }
                ChunkCmpStatus::WordInChunk { key, chunk_remain } => {
                    curr_node.split(key, chunk_remain, true);
                    break;
                }
                ChunkCmpStatus::ChunkInWord { key } => {
                    if curr_node.nodes.contains_key(&key) {
                        curr_node = curr_node.nodes.get_mut(&key).unwrap();
                    } else if curr_node.nodes.is_empty() && !curr_node.is_end {
                        // for empty tree
                        curr_node.is_end = true;
                        curr_node.chunk.push(key);
                        curr_node.chunk.append(&mut word_iter.collect());
                        break;
                    } else {
                        curr_node.extend(key, word_iter.collect());
                        break;
                    }
                }
                ChunkCmpStatus::Mismatch {
                    word_key,
                    chunk_key,
                    chunk_remain,
                } => {
                    curr_node.split(chunk_key, chunk_remain, false);
                    curr_node.extend(word_key, word_iter.collect());
                    break;
                }
            };
        }

        self.size += 1;
        Ok(())
    }

    pub fn remove(&mut self, word: &str) -> bool {
        let mut curr_node = &mut self.root;
        let mut word_iter = word.bytes();

        let chunk = &curr_node.chunk;
        let mut key = match Node::cmp_chunk(&mut word_iter, chunk) {
            ChunkCmpStatus::Identical => {
                return match curr_node.is_end {
                    true => {
                        curr_node.is_end = false;
                        match curr_node.nodes.len() {
                            0 => {
                                curr_node.chunk = Vec::new();
                            }
                            1 => curr_node.merge(),
                            _ => {}
                        }
                        self.size -= 1;
                        true
                    }
                    false => false,
                };
            }
            ChunkCmpStatus::WordInChunk { .. } | ChunkCmpStatus::Mismatch { .. } => {
                return false;
            }
            ChunkCmpStatus::ChunkInWord { key } => key,
        };

        loop {
            let Some(next_node) = curr_node.nodes.get(&key) else {
                return false;
            };
            let chunk = &next_node.chunk;
            let status = Node::cmp_chunk(&mut word_iter, chunk);

            match status {
                ChunkCmpStatus::Identical => {
                    let next_node = curr_node.nodes.get_mut(&key).unwrap();
                    return match next_node.is_end {
                        true => {
                            match next_node.nodes.len() {
                                0 => {
                                    curr_node.nodes.remove(&key);
                                    if !curr_node.is_end && curr_node.nodes.len() == 1 {
                                        curr_node.merge();
                                    }
                                }
                                1 => {
                                    next_node.is_end = false;
                                    next_node.merge()
                                }
                                _ => next_node.is_end = false,
                            }
                            self.size -= 1;
                            true
                        }
                        false => false,
                    };
                }
                ChunkCmpStatus::WordInChunk { .. } | ChunkCmpStatus::Mismatch { .. } => {
                    return false;
                }
                ChunkCmpStatus::ChunkInWord { key: word_key } => {
                    curr_node = curr_node.nodes.get_mut(&key).unwrap();
                    key = word_key
                }
            };
        }
    }

    pub fn contains_exact(&self, word: &str) -> bool {
        let mut curr_node = &self.root;
        let mut word_iter = word.bytes();

        loop {
            let chunk = &curr_node.chunk;
            let status = Node::cmp_chunk(&mut word_iter, chunk);

            match status {
                ChunkCmpStatus::Identical => return curr_node.is_end,
                ChunkCmpStatus::WordInChunk { .. } | ChunkCmpStatus::Mismatch { .. } => {
                    return false;
                }
                ChunkCmpStatus::ChunkInWord { key } => match curr_node.nodes.get(&key) {
                    Some(node) => curr_node = node,
                    None => return false,
                },
            }
        }
    }

    pub fn contains_prefix(&self, word: &str) -> bool {
        let mut curr_node = &self.root;
        let mut word_iter = word.bytes();

        loop {
            let chunk = &curr_node.chunk;
            let status = Node::cmp_chunk(&mut word_iter, chunk);

            match status {
                ChunkCmpStatus::Identical => {
                    // if word is empty and tree is empty, it matches identical but there should be
                    // no string that matches prefix
                    return !self.is_empty();
                }
                ChunkCmpStatus::WordInChunk { .. } => {
                    return true;
                }
                ChunkCmpStatus::Mismatch { .. } => {
                    return false;
                }
                ChunkCmpStatus::ChunkInWord { key } => match curr_node.nodes.get(&key) {
                    Some(node) => curr_node = node,
                    None => return false,
                },
            }
        }
    }

    pub fn iter(&self) -> Iter {
        self.iter_prefix("")
    }

    pub fn iter_prefix(&self, prefix: &str) -> Iter {
        let mut curr_node = &self.root;
        let mut word_iter = prefix.bytes();

        let tail_trunc_len = loop {
            let chunk = &curr_node.chunk;
            let status = Node::cmp_chunk(&mut word_iter, chunk);

            match status {
                ChunkCmpStatus::Identical => {
                    // len still include node key
                    let tail_trunc_len = curr_node.chunk.len();
                    break tail_trunc_len;
                }
                ChunkCmpStatus::WordInChunk {
                    key: _,
                    chunk_remain,
                } => {
                    // len still include node key, -1 is for accounting key being consumed from chunk iter
                    let tail_trunc_len = curr_node.chunk.len() - chunk_remain.len() - 1;
                    break tail_trunc_len;
                }
                ChunkCmpStatus::Mismatch { .. } => {
                    return Iter {
                        prefix: Vec::new(),
                        nodes: Vec::new(),
                    };
                }
                ChunkCmpStatus::ChunkInWord { key } => match curr_node.nodes.get(&key) {
                    Some(node) => curr_node = node,
                    None => {
                        return Iter {
                            prefix: Vec::new(),
                            nodes: Vec::new(),
                        };
                    }
                },
            }
        };

        // truncate to parent prefix byte len
        let mut prefix_bytes = prefix.as_bytes().to_vec();
        prefix_bytes.truncate(prefix_bytes.len() - tail_trunc_len);

        let key = prefix_bytes.pop();
        let parent_prefix_len = prefix_bytes.len();

        Iter {
            prefix: prefix_bytes,
            nodes: vec![IterNode {
                parent_prefix_len,
                key,
                node: curr_node,
            }],
        }
    }
}

impl Default for RadixTree {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
struct IterNode<'a> {
    parent_prefix_len: usize,
    // root does not have key
    key: Option<u8>,
    node: &'a Node,
}

pub struct Iter<'a> {
    prefix: Vec<u8>,
    nodes: Vec<IterNode<'a>>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(iter_node) = self.nodes.pop() {
                let IterNode {
                    parent_prefix_len,
                    key,
                    node,
                } = iter_node;

                self.prefix.truncate(parent_prefix_len);
                if let Some(key) = key {
                    self.prefix.push(key);
                }
                self.prefix.extend(node.chunk.iter());

                for (child_key, child_node) in node.nodes.iter() {
                    self.nodes.push(IterNode {
                        parent_prefix_len: self.prefix.len(),
                        key: Some(*child_key),
                        node: child_node,
                    })
                }

                if node.is_end {
                    return Some(unsafe { String::from_utf8_unchecked(self.prefix.clone()) });
                }
            } else {
                return None;
            }
        }
    }
}

impl Drop for RadixTree {
    fn drop(&mut self) {
        let curr_node = mem::replace(
            &mut self.root,
            Node {
                chunk: Vec::new(),
                nodes: HashMap::new(),
                is_end: false,
            },
        );

        let mut stack: Vec<Node> = vec![curr_node];
        while let Some(node) = stack.pop() {
            for (_key, child_node) in node.nodes.into_iter() {
                stack.push(child_node);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, vec};

    use super::*;

    #[test]
    fn test_new() {
        // new()
        let tree = RadixTree::new();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        // default()
        let tree = RadixTree::default();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
    }

    #[test]
    fn test_empty_tree() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: Vec::new(),
                is_end: false,
                nodes: HashMap::new(),
            },
            size: 0,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 98, 99],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };

        let mut tree = RadixTree::new();
        let word = "abc";

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_empty_string_empty_tree() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: Vec::new(),
                is_end: false,
                nodes: HashMap::new(),
            },
            size: 0,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: Vec::new(),
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };

        let mut tree = RadixTree::new();

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(""));
        assert!(!tree.contains_prefix(""));

        // insert and validate
        assert_eq!(tree.insert(""), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(""));
        assert!(tree.contains_prefix(""));

        // remove and validate
        assert!(tree.remove(""));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(""));
        assert!(!tree.contains_prefix(""));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_empty_string_non_empty_tree() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 98, 99],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: Vec::new(),
                is_end: true,
                nodes: [(
                    97,
                    Node {
                        chunk: vec![98, 99],
                        is_end: true,
                        nodes: HashMap::new(),
                    },
                )]
                .into_iter()
                .collect(),
            },
            size: 2,
        };

        let mut tree = RadixTree::new();
        assert_eq!(tree.insert("abc"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(""));
        assert!(tree.contains_prefix(""));

        // insert and validate
        assert_eq!(tree.insert(""), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(""));
        assert!(tree.contains_prefix(""));

        // remove and validate
        assert!(tree.remove(""));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(""));
        assert!(tree.contains_prefix(""));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_unicode_chunk_split() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![240, 159, 142, 140],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![240, 159, 142],
                is_end: false,
                nodes: [
                    (
                        137,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        140,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 2,
        };

        let mut tree = RadixTree::new();
        let word = "🎉";
        assert_eq!(tree.insert("🎌"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_mark_common_substring_is_end() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97],
                is_end: false,
                nodes: [
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        99,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 2,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97],
                is_end: true,
                nodes: [
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        99,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 3,
        };

        let mut tree = RadixTree::new();
        let word = "aa";
        assert_eq!(tree.insert("aab"), Ok(()));
        assert_eq!(tree.insert("aac"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_word_in_chunk_old_node_is_end() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97, 98],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97],
                is_end: true,
                nodes: [(
                    98,
                    Node {
                        chunk: Vec::new(),
                        is_end: true,
                        nodes: HashMap::new(),
                    },
                )]
                .into_iter()
                .collect(),
            },

            size: 2,
        };

        let mut tree = RadixTree::new();
        let word = "aa";
        assert_eq!(tree.insert("aab"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_word_in_chunk_old_node_is_not_end() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97],
                is_end: false,
                nodes: [
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        99,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 2,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97],
                is_end: true,
                nodes: [(
                    97,
                    Node {
                        chunk: Vec::new(),
                        is_end: false,
                        nodes: [
                            (
                                98,
                                Node {
                                    chunk: Vec::new(),
                                    is_end: true,
                                    nodes: HashMap::new(),
                                },
                            ),
                            (
                                99,
                                Node {
                                    chunk: Vec::new(),
                                    is_end: true,
                                    nodes: HashMap::new(),
                                },
                            ),
                        ]
                        .into_iter()
                        .collect(),
                    },
                )]
                .into_iter()
                .collect(),
            },

            size: 3,
        };

        let mut tree = RadixTree::new();
        let word = "a";
        assert_eq!(tree.insert("aab"), Ok(()));
        assert_eq!(tree.insert("aac"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_chunk_in_word() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97],
                is_end: false,
                nodes: [
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        99,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 2,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97],
                is_end: false,
                nodes: [
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: [(
                                100,
                                Node {
                                    chunk: Vec::new(),
                                    is_end: true,
                                    nodes: HashMap::new(),
                                },
                            )]
                            .into_iter()
                            .collect(),
                        },
                    ),
                    (
                        99,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 3,
        };

        let mut tree = RadixTree::new();
        let word = "aabd";
        assert_eq!(tree.insert("aab"), Ok(()));
        assert_eq!(tree.insert("aac"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_mismatch() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97, 98],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 97],
                is_end: false,
                nodes: [
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        99,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 2,
        };

        let mut tree = RadixTree::new();
        let word = "aac";
        assert_eq!(tree.insert("aab"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(!tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_remove_identical_chunk_with_one_child_node() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97],
                is_end: false,
                nodes: [
                    (
                        97,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        98,
                        Node {
                            chunk: vec![99],
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 2,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97],
                is_end: false,
                nodes: [
                    (
                        97,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: [(
                                99,
                                Node {
                                    chunk: Vec::new(),
                                    is_end: true,
                                    nodes: HashMap::new(),
                                },
                            )]
                            .into_iter()
                            .collect(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 3,
        };

        let mut tree = RadixTree::new();
        let word = "ab";
        assert_eq!(tree.insert("aa"), Ok(()));
        assert_eq!(tree.insert("abc"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_remove_identical_chunk_with_two_child_node() {
        let old_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97],
                is_end: false,
                nodes: [
                    (
                        97,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: false,
                            nodes: [
                                (
                                    99,
                                    Node {
                                        chunk: Vec::new(),
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                                (
                                    100,
                                    Node {
                                        chunk: Vec::new(),
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                            ]
                            .into_iter()
                            .collect(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 3,
        };
        let new_expected_tree = RadixTree {
            root: Node {
                chunk: vec![97],
                is_end: false,
                nodes: [
                    (
                        97,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        98,
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: [
                                (
                                    99,
                                    Node {
                                        chunk: Vec::new(),
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                                (
                                    100,
                                    Node {
                                        chunk: Vec::new(),
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                            ]
                            .into_iter()
                            .collect(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 4,
        };

        let mut tree = RadixTree::new();
        let word = "ab";
        assert_eq!(tree.insert("aa"), Ok(()));
        assert_eq!(tree.insert("abc"), Ok(()));
        assert_eq!(tree.insert("abd"), Ok(()));

        // validate before mutate
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // insert and validate
        assert_eq!(tree.insert(word), Ok(()));
        assert_eq!(tree, new_expected_tree);
        assert!(tree.contains_exact(word));
        assert!(tree.contains_prefix(word));

        // remove and validate
        assert!(tree.remove(word));
        assert_eq!(tree, old_expected_tree);
        assert!(!tree.contains_exact(word));
        assert!(tree.contains_prefix(word));
        assert!(!tree.remove(""));
    }

    #[test]
    fn test_remove_negative() {
        let expected_tree = RadixTree {
            root: Node {
                chunk: vec![97, 98, 99],
                is_end: false,
                nodes: [
                    (
                        100,
                        Node {
                            chunk: vec![101],
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        102,
                        Node {
                            chunk: vec![103],
                            is_end: false,
                            nodes: [
                                (
                                    104,
                                    Node {
                                        chunk: vec![105],
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                                (
                                    106,
                                    Node {
                                        chunk: vec![107],
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                            ]
                            .into_iter()
                            .collect(),
                        },
                    ),
                ]
                .into_iter()
                .collect(),
            },
            size: 3,
        };

        let mut tree = RadixTree::new();
        assert_eq!(tree.insert("abcde"), Ok(()));
        assert_eq!(tree.insert("abcfghi"), Ok(()));
        assert_eq!(tree.insert("abcfgjk"), Ok(()));

        // validate tree shape
        assert_eq!(tree, expected_tree);

        // false if root chunk has identical word but is not word end
        assert!(!tree.remove("abc"));
        // false if word in root chunk
        assert!(!tree.remove("ab"));
        // false if root chunk and word mismatches
        assert!(!tree.remove("abh"));

        // false if next node does not exist
        assert!(!tree.remove("abch"));
        // false if next node chunk has identical word but is not word end
        assert!(!tree.remove("abcfg"));
        // false if word in next node chunk
        assert!(!tree.remove("abcf"));
        // false if root chunk and word mismatches
        assert!(!tree.remove("abcfh"));
    }

    fn get_unicode_words() -> Vec<String> {
        let words = vec![
            "你好",
            "🥢",
            "Hi, 🥢",
            "hello",
            "我好嗎",
            "🍣",
            "すしや",
            "hello, world",
            "你好，世界",
            "🥷",
            "すし",
            "你很好",
            "Hello,你很好",
            "hell",
            "🍜",
            "すしづめ",
            "我好吗",
            "🥷🍜🐔🍣",
            "すしだね",
            "🐔🍣",
            "hello!",
            "すしめし",
            "hey! すしめし",
            "🥷🍜",
            "你好吗",
            "🥢🍜🍣",
            "Hey",
            "🥢🍣🍜",
            "すしをにぎる",
            "🐔",
            "你好嗎",
        ];

        words.iter().map(|word| word.to_string()).collect()
    }

    #[test]
    fn test_many_insert_removes() {
        let mut tree = RadixTree::new();
        let words = get_unicode_words();

        for (index, word) in words.iter().enumerate() {
            assert_eq!(tree.insert(word), Ok(()));
            assert_eq!(tree.size(), index + 1);
            assert!(!tree.is_empty());
            assert_eq!(tree.insert(word), Err(DuplicateItemErr));
            assert_eq!(tree.size(), index + 1);
        }

        for (index, word) in words.iter().enumerate() {
            assert!(!tree.is_empty());
            assert!(tree.remove(word));
            assert_eq!(tree.size(), words.len() - index - 1);
            assert!(!tree.remove(word));
            assert_eq!(tree.size(), words.len() - index - 1);
        }
    }

    fn get_prefixes(word: &str) -> Vec<String> {
        let mut chars = word.chars();
        let mut prefixes = vec![chars.as_str().to_string()];
        while chars.next_back().is_some() {
            prefixes.push(chars.as_str().to_string());
        }
        prefixes
    }

    #[test]
    fn test_contains_prefix() {
        let mut tree = RadixTree::new();

        let mut words = get_unicode_words();
        let mut inserted_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            assert_eq!(tree.insert(&word), Ok(()));
            inserted_words.push(word);

            let inserted_prefixes: Vec<String> = inserted_words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .collect();
            let inserted_prefixes_set: HashSet<String> = HashSet::from_iter(inserted_prefixes);
            let prefixes_to_insert: Vec<String> = words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .filter(|word| !inserted_prefixes_set.contains(word))
                .collect();
            let prefixes_to_insert_set: HashSet<String> = HashSet::from_iter(prefixes_to_insert);

            for prefix in inserted_prefixes_set.iter() {
                assert!(tree.contains_prefix(prefix));
            }

            for prefix in prefixes_to_insert_set.iter() {
                assert!(!tree.contains_prefix(prefix));
            }
        }

        let mut words = get_unicode_words();
        let mut removed_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            assert!(tree.remove(&word));
            removed_words.push(word);

            let prefixes: Vec<String> = words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .collect();
            let prefixes_set: HashSet<String> = HashSet::from_iter(prefixes);
            let removed_prefixes: Vec<String> = removed_words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .filter(|word| !prefixes_set.contains(word))
                .collect();
            let removed_prefixes_set: HashSet<String> = HashSet::from_iter(removed_prefixes);

            for prefix in prefixes_set.iter() {
                assert!(tree.contains_prefix(prefix));
            }

            for prefix in removed_prefixes_set.iter() {
                assert!(!tree.contains_prefix(prefix));
            }
        }
    }

    #[test]
    fn test_iter() {
        let mut tree = RadixTree::new();
        assert_eq!(tree.iter().next(), None);

        let mut words = get_unicode_words();
        let mut inserted_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            assert_eq!(tree.insert(&word), Ok(()));
            inserted_words.push(word);

            for word in tree.iter() {
                assert!(inserted_words.contains(&word));
                assert!(!words.contains(&word));
            }
        }

        let mut words = get_unicode_words();
        let mut removed_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            assert!(tree.remove(&word));
            removed_words.push(word);

            for word in tree.iter() {
                assert!(words.contains(&word));
                assert!(!removed_words.contains(&word));
            }
        }
    }

    #[test]
    fn test_iter_prefix() {
        let mut tree = RadixTree::new();

        let mut words = get_unicode_words();
        let mut inserted_words: Vec<String> = Vec::new();

        for _i in 0..25 {
            let word = words.pop().unwrap();
            assert_eq!(tree.insert(&word), Ok(()));
            inserted_words.push(word);
        }

        let inserted_prefixes: Vec<String> = inserted_words
            .iter()
            .map(|str| str.as_str())
            .flat_map(get_prefixes)
            .collect();
        let inserted_prefixes_set: HashSet<String> = HashSet::from_iter(inserted_prefixes);
        let non_inserted_prefixes: Vec<String> = words
            .iter()
            .map(|str| str.as_str())
            .flat_map(get_prefixes)
            .filter(|word| !inserted_prefixes_set.contains(word))
            .collect();
        let non_inserted_prefixes_set: HashSet<String> = HashSet::from_iter(non_inserted_prefixes);

        for prefix in inserted_prefixes_set {
            let words_with_prefix: Vec<String> = inserted_words
                .iter()
                .filter(|word| word.starts_with(prefix.as_str()))
                .cloned()
                .collect();
            let tree_iter_prefix_words: Vec<String> = tree.iter_prefix(&prefix).collect();
            assert_eq!(
                HashSet::from_iter(words_with_prefix) as HashSet<String>,
                HashSet::from_iter(tree_iter_prefix_words) as HashSet<String>
            );
        }

        for prefix in non_inserted_prefixes_set {
            assert_eq!(tree.iter_prefix(&prefix).next(), None);
        }
        assert_eq!(tree.iter_prefix("hello, world!!!").next(), None);
    }
}
