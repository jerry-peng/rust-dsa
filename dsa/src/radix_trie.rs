//! Radix trie implementation (with unicode support)

use std::collections::HashMap;
use std::mem;
use std::str::Bytes;

/// Thrown during attempts to insert duplicate words
#[derive(PartialEq, Debug)]
pub struct DuplicateItemErr;

#[derive(Debug, PartialEq)]
/// Radix trie structure
///
/// * `root`: root node
/// * `size`: tree size
pub struct RadixTrie {
    root: Node,
    size: usize,
}

/// radix trie node structure
///
/// * `nodes`: child nodes
/// * `chunk`: word chunk in current node
/// * `is_end`: if current node denotes end of word
#[derive(Debug, PartialEq)]
struct Node {
    nodes: HashMap<u8, Node>,
    chunk: Vec<u8>,
    is_end: bool,
}

enum ChunkCmpStatus {
    // * `Identical`: word chunk and node chunk are identical
    Identical,
    // * `WordInChunk`: word chunk is substring of node chunk
    //   * `key`: first byte in remaining node chunk
    //   * `chunk_remain`: remaining node chunk excluding key
    WordInChunk {
        key: u8,
        chunk_remain: Vec<u8>,
    },
    // * `ChunkInWord`: node chunk is substring of word chunk
    //   * `key`: first byte in remaining word chunk
    ChunkInWord {
        key: u8,
    },
    // * `Mismatch`: mismatch in node chunk/word chunk
    //   * `word_key`: first byte in remaining word chunk
    //   * `chunk_key`: first byte in remaining node chunk
    //   * `chunk_remain`: remaining node chunk excluding key
    Mismatch {
        word_key: u8,
        chunk_key: u8,
        chunk_remain: Vec<u8>,
    },
}

impl Node {
    /// Splits child chunk off of node chunk into new child node
    ///
    /// ### Warning
    ///
    /// This function will panic if key + child chunk length is longer than
    /// node's chunk.
    ///
    /// * `key`: key to child node
    /// * `child_chunk`: child node chunk
    /// * `is_end`: whether self node will be end of word
    fn split(&mut self, key: u8, child_chunk: Vec<u8>, is_end: bool) {
        // new child node inherits current node's child nodes and `is_end`
        let new_child_node = Node {
            nodes: mem::take(&mut self.nodes),
            chunk: child_chunk,
            is_end: self.is_end,
        };

        // truncate current node chunk; -1 accounts for key to child node
        self.chunk
            .truncate(self.chunk.len() - new_child_node.chunk.len() - 1);
        self.is_end = is_end;
        self.nodes.insert(key, new_child_node);
    }

    /// Extends new child node
    ///
    /// * `key`: key to child node
    /// * `chunk`: child node chunk
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

    /// Merge child node back into parent
    ///
    /// ### Warning
    ///
    /// This function will panic if self node does not have exactly 1 child node,
    /// or if self node is not end-of-word.
    fn merge(&mut self) {
        // assert function preconditions
        assert!(self.nodes.len() == 1 && !self.is_end);

        // get key and child node, then merge key and child chunk back into self chunk
        let (key, node) = &mut mem::take(&mut self.nodes).into_iter().collect::<Vec<_>>()[0];
        self.chunk.push(*key);
        self.chunk.append(&mut node.chunk);

        // self node inherits child node's child nodes and `is_end`
        mem::swap(&mut self.nodes, &mut node.nodes);
        self.is_end = node.is_end;
    }

    /// Util function to compares word chunk with node chunk,
    /// and returns status
    ///
    /// * `word_iter`: word byte iterator
    /// * `chunk`: node chunk
    pub fn cmp_chunk(word_iter: &mut Bytes<'_>, chunk: &[u8]) -> ChunkCmpStatus {
        let mut chunk_iter = chunk.iter();
        loop {
            // walk word chunk and node chunk iterators
            let word_byte_opt = word_iter.next();
            let chunk_byte_opt = chunk_iter.next();

            match (word_byte_opt, chunk_byte_opt) {
                // If both iterators are exhausted, word chunk and node chunk are identical.
                (None, None) => return ChunkCmpStatus::Identical,

                // If word chunk exhausts first, word chunk is substring of node chunk.
                // First byte after substring in node chunk is assigned key, and remaining
                // bytes are collected.
                (None, Some(chunk_byte)) => {
                    return ChunkCmpStatus::WordInChunk {
                        key: *chunk_byte,
                        // remain chunk excludes key
                        chunk_remain: chunk_iter.copied().collect(),
                    };
                }

                // If word chunk exhausts first, node chunk is substring of word byte chunk.
                // First byte after substring in word chunk is assigned key.
                (Some(word_byte), None) => {
                    return ChunkCmpStatus::ChunkInWord { key: word_byte };
                }

                // If word byte and chunk byte are different, mismatch in node chunk and word byte
                // chunk.
                (Some(word_byte), Some(chunk_byte)) if word_byte != *chunk_byte => {
                    return ChunkCmpStatus::Mismatch {
                        word_key: word_byte,
                        chunk_key: *chunk_byte,
                        chunk_remain: chunk_iter.copied().collect(),
                    };
                }
                // word byte and chunk byte are equal, continue iterator walks
                (Some(_), Some(_)) => {}
            }
        }
    }
}

impl RadixTrie {
    /// Creates new empty radix trie
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert_eq!(tree.size(), 0);
    /// assert!(tree.is_empty());
    /// ```
    pub fn new() -> RadixTrie {
        RadixTrie {
            root: Node {
                nodes: HashMap::new(),
                chunk: Vec::new(),
                is_end: false,
            },
            size: 0,
        }
    }

    /// Get number of words stored in radix trie
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert_eq!(tree.size(), 0);
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert_eq!(tree.size(), 1);
    /// assert!(tree.remove("abc"));
    /// assert_eq!(tree.size(), 0);
    /// ```
    pub fn size(&self) -> usize {
        self.size
    }

    /// Get whether tree is empty
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert!(tree.is_empty());
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert!(!tree.is_empty());
    /// assert!(tree.remove("abc"));
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Insert word to tree
    ///
    /// * `word`: reference to word to insert
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::radix_trie::{RadixTrie, DuplicateItemErr};
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert!(!tree.contains_exact("abc"));
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert!(tree.contains_exact("abc"));
    /// assert_eq!(tree.insert("abc"), Err(DuplicateItemErr));
    /// assert!(tree.contains_exact("abc"));
    /// ```
    pub fn insert(&mut self, word: &str) -> Result<(), DuplicateItemErr> {
        let tree_is_empty = self.is_empty();
        let mut curr_node = &mut self.root;
        let mut word_iter = word.bytes();

        loop {
            // walk word chunk/node chunk and compare byte
            match Node::cmp_chunk(&mut word_iter, &curr_node.chunk) {
                // When word chunk and node chunk are identical, if word already exists in tree,
                // return duplicate error, otherwise insert by marking node as end of word and
                // break.
                ChunkCmpStatus::Identical => {
                    return match curr_node.is_end {
                        true => Err(DuplicateItemErr),
                        false => {
                            curr_node.is_end = true;
                            break;
                        }
                    };
                }

                // If word chunk is substring of node chunk, split current node and current node as
                // end of word.
                ChunkCmpStatus::WordInChunk { key, chunk_remain } => {
                    curr_node.split(key, chunk_remain, true);
                    break;
                }

                // If node chunk is substring of word chunk, 3 cases:
                // - if key to next child node exists, assign child node as current node and
                //   continue walking word iterator.
                // - if key does not exist:
                //   - if tree is empty, just append entire word chunk into root node chunk
                //   - if tree is not empty, extend current node to have a new child node
                ChunkCmpStatus::ChunkInWord { key } => {
                    if curr_node.nodes.contains_key(&key) {
                        curr_node = curr_node.nodes.get_mut(&key).unwrap();
                    } else if !tree_is_empty {
                        curr_node.extend(key, word_iter.collect());
                        break;
                    } else {
                        curr_node.is_end = true;
                        curr_node.chunk.push(key);
                        curr_node.chunk.append(&mut word_iter.collect());
                        break;
                    }
                }

                // If there is mismatch in word chunk and node chunk, truncate current node chunk
                // into common substring, and spawn child nodes for remaining node/word chunks.
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

        // increment tree size
        self.size += 1;
        Ok(())
    }

    /// Remove word from tree
    ///
    /// * `word`: reference to word to insert
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert!(!tree.contains_exact("abc"));
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert!(tree.contains_exact("abc"));
    /// assert!(tree.remove("abc"));
    /// assert!(!tree.contains_exact("abc"));
    /// ```
    pub fn remove(&mut self, word: &str) -> bool {
        let mut curr_node = &mut self.root;
        let mut word_iter = word.bytes();

        // NOTE: why compare chunk on root node first before loop?
        // Removing child node requires keeping track of reference to parent node. This is done by
        // assigning parent node to current node, and child node to next node, compare chunk on
        // next node, and traverse current node to next node when necessary. Since root node has no
        // parent, we'd need to compare its chunk first before traversal loop.

        // check root node chunk compare status
        let mut key = match Node::cmp_chunk(&mut word_iter, &curr_node.chunk) {
            // Word chunk and node chunk are identical. Scenarios:
            // - if current node is not end of word, word to remove does not exist, return false
            // - if current node is end of word, mark end of word as false, and:
            //   - if current node has more than 1 child, no-op
            //   - if current node has 1 child, merge child node back to parent
            //   - if current node has 0 child, set chunk to empty vec
            //   finally, return true after word is removed from tree
            ChunkCmpStatus::Identical => {
                return match curr_node.is_end {
                    true => {
                        curr_node.is_end = false;
                        match curr_node.nodes.len() {
                            0 => curr_node.chunk = Vec::new(),
                            1 => curr_node.merge(),
                            _ => {}
                        }
                        // decrement tree size and return true
                        self.size -= 1;
                        true
                    }
                    // word does not exist in tree
                    false => false,
                };
            }

            // If word chunk is substring of node chunk, or if chunks mismatch, word does not
            // exist in tree, return false.
            ChunkCmpStatus::WordInChunk { .. } | ChunkCmpStatus::Mismatch { .. } => {
                return false;
            }

            // Continue tree traversal loop only if node chunk is substring of word chunk,
            // capture key to child node.
            ChunkCmpStatus::ChunkInWord { key } => key,
        };

        loop {
            // Get next child node if it exists, otherwise, word does not exist in tree,
            // return false.
            let Some(next_node) = curr_node.nodes.get(&key) else {
                return false;
            };

            // compare word chunk and next node chunk
            key = match Node::cmp_chunk(&mut word_iter, &next_node.chunk) {
                // Word chunk and next node chunk are identical. Scenarios:
                // - if next node is not end of word, word to remove does not exist, return false
                // - if next node is end of word, mark end of word as false, and:
                //   - if next node has more than 1 child, no-op
                //   - if next node has 1 child, merge child node back to next node
                //   - if next node has 0 child, remove next node from its parent (current node).
                //     - if current node is not end of word, and has 1 child as a result of child
                //     removal, merge current node.
                //   finally, return true after word is removed from tree
                ChunkCmpStatus::Identical => {
                    // next child node is verified to exist at the start of the loop, safe to
                    // unwrap
                    let next_node = curr_node.nodes.get_mut(&key).unwrap();
                    return match next_node.is_end {
                        true => {
                            next_node.is_end = false;
                            match next_node.nodes.len() {
                                0 => {
                                    curr_node.nodes.remove(&key);
                                    if !curr_node.is_end && curr_node.nodes.len() == 1 {
                                        curr_node.merge();
                                    }
                                }
                                1 => next_node.merge(),
                                _ => {}
                            }

                            // decrement tree size and return true
                            self.size -= 1;
                            true
                        }
                        // word does not exist in tree
                        false => false,
                    };
                }

                // If word chunk is substring of node chunk, or if chunks mismatch, word does not
                // exist in tree, return false.
                ChunkCmpStatus::WordInChunk { .. } | ChunkCmpStatus::Mismatch { .. } => {
                    return false;
                }

                // Continue tree traversal loop only if node chunk is substring of word chunk,
                // update current node to next node, and capture key to next next child node
                ChunkCmpStatus::ChunkInWord { key: word_key } => {
                    curr_node = curr_node.nodes.get_mut(&key).unwrap();
                    word_key
                }
            };
        }
    }

    /// Check if radix trie contains exact word
    ///
    /// * `word`: reference to word to search
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert!(tree.contains_exact("abc"));
    /// assert!(!tree.contains_exact("abe"));
    /// assert!(!tree.contains_exact("ab"));
    /// assert!(!tree.contains_exact("abcc"));
    /// ```
    pub fn contains_exact(&self, word: &str) -> bool {
        let mut curr_node = &self.root;
        let mut word_iter = word.bytes();

        loop {
            // compare word chunk and next node chunk
            match Node::cmp_chunk(&mut word_iter, &curr_node.chunk) {
                // If word chunk and node chunk are identical, return whether whether node is end
                // of word.
                ChunkCmpStatus::Identical => return curr_node.is_end,

                // If word chunk is substring of node chunk, or if chunks mismatch, word does not
                // exist in tree, return false.
                ChunkCmpStatus::WordInChunk { .. } | ChunkCmpStatus::Mismatch { .. } => {
                    return false;
                }

                // Continue tree traversal loop only if node chunk is substring of word chunk,
                // if child node does not exist, return false.
                ChunkCmpStatus::ChunkInWord { key } => match curr_node.nodes.get(&key) {
                    Some(node) => curr_node = node,
                    None => return false,
                },
            }
        }
    }

    /// Check if radix trie contains word with prefix
    ///
    /// * `word`: reference to prefix to search
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert!(!tree.contains_prefix(""));
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert!(tree.contains_prefix(""));
    /// assert!(tree.contains_prefix("a"));
    /// assert!(tree.contains_prefix("ab"));
    /// assert!(tree.contains_prefix("abc"));
    /// assert!(!tree.contains_prefix("abcd"));
    /// ```
    pub fn contains_prefix(&self, prefix: &str) -> bool {
        let mut curr_node = &self.root;
        let mut prefix_iter = prefix.bytes();

        loop {
            // compare word chunk and next node chunk
            match Node::cmp_chunk(&mut prefix_iter, &curr_node.chunk) {
                // If word chunk and node chunk are identical, word with prefix exists.
                // However, if tree is empty, empty prefix should not match.
                ChunkCmpStatus::Identical => {
                    return !self.is_empty();
                }

                // If word chunk is substring of node chunk, word with prefix exists, return true.
                ChunkCmpStatus::WordInChunk { .. } => {
                    return true;
                }

                // If chunks mismatch, word does not exist, return false.
                ChunkCmpStatus::Mismatch { .. } => {
                    return false;
                }

                // Continue tree traversal loop only if node chunk is substring of word chunk,
                // if child node does not exist, return false.
                ChunkCmpStatus::ChunkInWord { key } => match curr_node.nodes.get(&key) {
                    Some(node) => curr_node = node,
                    None => return false,
                },
            }
        }
    }

    /// Create iterator for radix trie
    ///
    /// # Example
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert_eq!(tree.insert("abe"), Ok(()));
    /// assert_eq!(tree.insert("abcd"), Ok(()));
    /// assert_eq!(tree.insert("aa"), Ok(()));
    /// let words: HashSet<String> = HashSet::from_iter(tree.iter());
    /// let expected_words: HashSet<String> = HashSet::from_iter(
    ///     vec!["aa", "abc", "abe", "abcd"].into_iter().map(|word| word.to_string())
    /// );
    /// assert_eq!(words, expected_words);
    /// ```
    pub fn iter(&self) -> Iter {
        // delegate default iterator to prefix iterator with empty prefix
        self.iter_prefix("")
    }

    /// Create prefix iterator for radix trie
    ///
    /// * `prefix`: reference to prefix
    ///
    /// # Example
    ///
    /// ```
    /// use std::collections::HashSet;
    /// use dsa::radix_trie::RadixTrie;
    /// let mut tree: RadixTrie = RadixTrie::new();
    /// assert_eq!(tree.insert("abc"), Ok(()));
    /// assert_eq!(tree.insert("abe"), Ok(()));
    /// assert_eq!(tree.insert("abcd"), Ok(()));
    /// assert_eq!(tree.insert("aa"), Ok(()));
    /// let words: HashSet<String> = HashSet::from_iter(tree.iter_prefix("ab"));
    /// let expected_words: HashSet<String> = HashSet::from_iter(
    ///     vec!["abc", "abe", "abcd"].into_iter().map(|word| word.to_string())
    /// );
    /// assert_eq!(words, expected_words);
    /// ```
    pub fn iter_prefix(&self, prefix: &str) -> Iter {
        let mut curr_node = &self.root;
        let mut word_iter = prefix.bytes();
        let prefix_len = prefix.len();

        // traverse tree using prefix, if node found, find prefix truncate length.
        // The truncate length should exclude chunks in current node. (include key to current
        // node if parent exists)
        let trunc_len = loop {
            // compare word chunk and next node chunk
            match Node::cmp_chunk(&mut word_iter, &curr_node.chunk) {
                // If word chunk and node chunk are identical, assign current node as starting
                // node, and return truncate length to exclude current node chunk.
                ChunkCmpStatus::Identical => {
                    break prefix_len - curr_node.chunk.len();
                }

                // If word chunk is substring of node chunk, assign current node as starting
                // node, and return truncate length to exclude current node chunk.
                ChunkCmpStatus::WordInChunk {
                    key: _,
                    chunk_remain,
                } => {
                    // `+1` accounts for key to next child node
                    break prefix_len + chunk_remain.len() + 1 - curr_node.chunk.len();
                }

                // If chunks mismatch, no word with prefix exists in tree, return empty iterator
                ChunkCmpStatus::Mismatch { .. } => {
                    return Iter {
                        prefix: Vec::new(),
                        nodes: Vec::new(),
                    };
                }

                // If node chunk is substring of word chunk:
                // - If key to next child node exists, traverse to next child node.
                // - If key to next child node does not exist, no word with prefix exists in tree,
                //   return empty iterator
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

        // truncate prefix to not include node chunk
        let mut prefix_bytes = prefix.as_bytes().to_vec();
        prefix_bytes.truncate(trunc_len);
        // pop key to current node from prefix byte
        let key = prefix_bytes.pop();
        // get parent prefix length
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

impl Default for RadixTrie {
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator node struct
///
/// * `parent_prefix_len`: parent node's prefix length
/// * `key`: parent node's key to current node; optional since
///   root node does not have parent
/// * `node`: reference to node
#[derive(Debug)]
struct IterNode<'a> {
    parent_prefix_len: usize,
    key: Option<u8>,
    node: &'a Node,
}

/// Iterator struct
///
/// * `prefix`: current iterator prefix
/// * `nodes`: `IterNode` stack
pub struct Iter<'a> {
    prefix: Vec<u8>,
    nodes: Vec<IterNode<'a>>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // `IterNode` stack has item
            if let Some(iter_node) = self.nodes.pop() {
                // destruct node
                let IterNode {
                    parent_prefix_len,
                    key,
                    node,
                } = iter_node;

                // reconstruct prefix:
                // - truncate prefix back to parent prefix length
                // - push key to prefix if exists
                // - append node chunk from popped node to prefix
                self.prefix.truncate(parent_prefix_len);
                if let Some(key) = key {
                    self.prefix.push(key);
                }
                self.prefix.extend(node.chunk.iter());

                // for each child node in popped node, construct `IterNode` and push it to stack
                for (child_key, child_node) in node.nodes.iter() {
                    self.nodes.push(IterNode {
                        parent_prefix_len: self.prefix.len(),
                        key: Some(*child_key),
                        node: child_node,
                    })
                }

                // if popped node is end of word, construct utf8 string from chunk bytes and return
                if node.is_end {
                    return Some(unsafe { String::from_utf8_unchecked(self.prefix.clone()) });
                }
            } else {
                // `IterNode` stack is empty, return None
                return None;
            }
        }
    }
}

impl Drop for RadixTrie {
    /// Manual `drop` implementation to prevent stack overflow
    fn drop(&mut self) {
        // get root node
        let root_node = mem::replace(
            &mut self.root,
            Node {
                chunk: Vec::new(),
                nodes: HashMap::new(),
                is_end: false,
            },
        );

        // new stack with root node
        let mut stack: Vec<Node> = vec![root_node];
        // pop node from stack, then push each child node onto stack
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
        let tree = RadixTrie::new();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        // default()
        let tree = RadixTrie::default();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
    }

    #[test]
    fn test_empty_tree() {
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: Vec::new(),
                is_end: false,
                nodes: HashMap::new(),
            },
            size: 0,
        };
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'b', b'c'],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: Vec::new(),
                is_end: false,
                nodes: HashMap::new(),
            },
            size: 0,
        };
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: Vec::new(),
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };

        let mut tree = RadixTrie::new();

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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'b', b'c'],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: Vec::new(),
                is_end: true,
                nodes: [(
                    b'a',
                    Node {
                        chunk: vec![b'b', b'c'],
                        is_end: true,
                        nodes: HashMap::new(),
                    },
                )]
                .into_iter()
                .collect(),
            },
            size: 2,
        };

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![240, 159, 142, 140],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTrie {
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

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a'],
                is_end: false,
                nodes: [
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'c',
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
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a'],
                is_end: true,
                nodes: [
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'c',
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

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a', b'b'],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a'],
                is_end: true,
                nodes: [(
                    b'b',
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

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a'],
                is_end: false,
                nodes: [
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'c',
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
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a'],
                is_end: true,
                nodes: [(
                    b'a',
                    Node {
                        chunk: Vec::new(),
                        is_end: false,
                        nodes: [
                            (
                                b'b',
                                Node {
                                    chunk: Vec::new(),
                                    is_end: true,
                                    nodes: HashMap::new(),
                                },
                            ),
                            (
                                b'c',
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

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a'],
                is_end: false,
                nodes: [
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'c',
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
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a'],
                is_end: false,
                nodes: [
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: [(
                                b'd',
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
                        b'c',
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

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a', b'b'],
                is_end: true,
                nodes: HashMap::new(),
            },
            size: 1,
        };
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'a'],
                is_end: false,
                nodes: [
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'c',
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

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a'],
                is_end: false,
                nodes: [
                    (
                        b'a',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'b',
                        Node {
                            chunk: vec![b'c'],
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
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a'],
                is_end: false,
                nodes: [
                    (
                        b'a',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: [(
                                b'c',
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

        let mut tree = RadixTrie::new();
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
        let old_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a'],
                is_end: false,
                nodes: [
                    (
                        b'a',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: false,
                            nodes: [
                                (
                                    b'c',
                                    Node {
                                        chunk: Vec::new(),
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                                (
                                    b'd',
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
        let new_expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a'],
                is_end: false,
                nodes: [
                    (
                        b'a',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'b',
                        Node {
                            chunk: Vec::new(),
                            is_end: true,
                            nodes: [
                                (
                                    b'c',
                                    Node {
                                        chunk: Vec::new(),
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                                (
                                    b'd',
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

        let mut tree = RadixTrie::new();
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
        let expected_tree = RadixTrie {
            root: Node {
                chunk: vec![b'a', b'b', b'c'],
                is_end: false,
                nodes: [
                    (
                        b'd',
                        Node {
                            chunk: vec![b'e'],
                            is_end: true,
                            nodes: HashMap::new(),
                        },
                    ),
                    (
                        b'f',
                        Node {
                            chunk: vec![b'g'],
                            is_end: false,
                            nodes: [
                                (
                                    b'h',
                                    Node {
                                        chunk: vec![b'i'],
                                        is_end: true,
                                        nodes: HashMap::new(),
                                    },
                                ),
                                (
                                    b'j',
                                    Node {
                                        chunk: vec![b'k'],
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

        let mut tree = RadixTrie::new();
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
        let mut tree = RadixTrie::new();
        let words = get_unicode_words();

        // for each word, insert, verify, insert again and verify duplicate item error
        for (index, word) in words.iter().enumerate() {
            assert_eq!(tree.insert(word), Ok(()));
            assert_eq!(tree.size(), index + 1);
            assert!(tree.contains_exact(word));
            assert!(!tree.is_empty());
            assert_eq!(tree.insert(word), Err(DuplicateItemErr));
            assert_eq!(tree.size(), index + 1);
            assert!(tree.contains_exact(word));
        }

        // for each word, remove word, verify, remove again and verify nothing is removed
        for (index, word) in words.iter().enumerate() {
            assert!(!tree.is_empty());
            assert!(tree.remove(word));
            assert_eq!(tree.size(), words.len() - index - 1);
            assert!(!tree.contains_exact(word));
            assert!(!tree.remove(word));
            assert_eq!(tree.size(), words.len() - index - 1);
            assert!(!tree.contains_exact(word));
        }
    }

    fn get_prefixes(word: &str) -> Vec<String> {
        // given a word, return all prefixes
        let mut chars = word.chars();
        let mut prefixes = vec![chars.as_str().to_string()];
        while chars.next_back().is_some() {
            prefixes.push(chars.as_str().to_string());
        }
        prefixes
    }

    #[test]
    fn test_contains_prefix() {
        let mut tree = RadixTrie::new();

        let mut words = get_unicode_words();
        let mut inserted_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            // insert word to tree, then move word to `inserted_words`
            assert_eq!(tree.insert(&word), Ok(()));
            inserted_words.push(word);

            // get hash set of prefixes of all inserted words
            let inserted_prefixes: Vec<String> = inserted_words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .collect();
            let inserted_prefixes_set: HashSet<String> = HashSet::from_iter(inserted_prefixes);

            // get hash set of prefixes of words to insert, excluding prefixes of inserted words
            let prefixes_to_insert: Vec<String> = words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .filter(|word| !inserted_prefixes_set.contains(word))
                .collect();
            let prefixes_to_insert_set: HashSet<String> = HashSet::from_iter(prefixes_to_insert);

            // for each prefix of inserted words, assert contain prefix
            for prefix in inserted_prefixes_set.iter() {
                assert!(tree.contains_prefix(prefix));
            }
            // for each prefix of words to be inserted, assert not contain prefix
            for prefix in prefixes_to_insert_set.iter() {
                assert!(!tree.contains_prefix(prefix));
            }
        }

        let mut words = get_unicode_words();
        let mut removed_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            // remove word from tree, then move word to `removed_words`
            assert!(tree.remove(&word));
            removed_words.push(word);

            // get hash set of prefixes of all remaining words in tree
            let prefixes: Vec<String> = words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .collect();
            let prefixes_set: HashSet<String> = HashSet::from_iter(prefixes);

            // get hash set of prefixes of removed words, excluding prefixes of remaining words in
            // tree
            let removed_prefixes: Vec<String> = removed_words
                .iter()
                .map(|str| str.as_str())
                .flat_map(get_prefixes)
                .filter(|word| !prefixes_set.contains(word))
                .collect();
            let removed_prefixes_set: HashSet<String> = HashSet::from_iter(removed_prefixes);

            // for each prefix of remaining words, assert contain prefix
            for prefix in prefixes_set.iter() {
                assert!(tree.contains_prefix(prefix));
            }
            // for each prefix of removed words, assert not contain prefix
            for prefix in removed_prefixes_set.iter() {
                assert!(!tree.contains_prefix(prefix));
            }
        }
    }

    #[test]
    fn test_iter() {
        let mut tree = RadixTrie::new();
        assert_eq!(tree.iter().next(), None);

        let mut words = get_unicode_words();
        let mut inserted_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            // insert word to tree, then move word to `inserted_words`
            assert_eq!(tree.insert(&word), Ok(()));
            inserted_words.push(word);

            // for each word returned by iterator, assert it's contained in inserted words,
            // and not words to be inserted
            for word in tree.iter() {
                assert!(inserted_words.contains(&word));
                assert!(!words.contains(&word));
            }
        }

        let mut words = get_unicode_words();
        let mut removed_words: Vec<String> = Vec::new();

        while let Some(word) = words.pop() {
            // remove word from tree, then move word to `removed_words`
            assert!(tree.remove(&word));
            removed_words.push(word);

            // for each word returned by iterator, assert it's contained in inserted words,
            // and not removed words
            for word in tree.iter() {
                assert!(words.contains(&word));
                assert!(!removed_words.contains(&word));
            }
        }
    }

    #[test]
    fn test_iter_prefix() {
        let mut tree = RadixTrie::new();

        let mut words = get_unicode_words();
        let mut inserted_words: Vec<String> = Vec::new();

        // only insert 25 words
        for _i in 0..25 {
            let word = words.pop().unwrap();
            assert_eq!(tree.insert(&word), Ok(()));
            inserted_words.push(word);
        }

        // get hash set of prefixes of all inserted words
        let inserted_prefixes: Vec<String> = inserted_words
            .iter()
            .map(|str| str.as_str())
            .flat_map(get_prefixes)
            .collect();
        let inserted_prefixes_set: HashSet<String> = HashSet::from_iter(inserted_prefixes);

        // get hash set of prefixes of all non-inserted words excluding prefixes of inserted words
        let non_inserted_prefixes: Vec<String> = words
            .iter()
            .map(|str| str.as_str())
            .flat_map(get_prefixes)
            .filter(|word| !inserted_prefixes_set.contains(word))
            .collect();
        let non_inserted_prefixes_set: HashSet<String> = HashSet::from_iter(non_inserted_prefixes);

        // for each prefix of inserted words, verify words with such prefix are returned by the
        // iterator
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

        // for each prefix of non-inserted words, verify iterator returns None
        for prefix in non_inserted_prefixes_set {
            assert_eq!(tree.iter_prefix(&prefix).next(), None);
        }

        // verify prefix that does not match any node returns None
        assert_eq!(tree.iter_prefix("hello, world!!!").next(), None);
    }
}
