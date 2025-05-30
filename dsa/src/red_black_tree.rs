//! Red-black tree implementation

use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::mem;
use std::ptr::NonNull;
use std::{alloc, vec};

/// Thrown after attempts to insert duplicate item
#[derive(Debug, PartialEq)]
pub struct DuplicateItemErr;

/// Iterator traversal order
#[derive(Debug)]
pub enum TraversalOrder {
    Level,
    Pre,
    In,
    Post,
}

/// Tree node color
#[derive(Debug, PartialEq)]
enum Color {
    Red,
    Black,
}

/// Node type in relation to parent.
/// A node can be left child node, right child node,
/// or root node with no parent node
#[derive(Debug, PartialEq)]
enum NodeType {
    Left,
    Right,
    Root,
}

#[derive(Debug)]
pub struct RedBlackTree<T> {
    root: Option<NonNull<Node<T>>>,
    size: usize,
}

#[derive(Debug, PartialEq)]
/// Tree node structure
///
/// * `color`: node color (red/black)
/// * `parent`: optional pointer to parent node, parent is None for root node
/// * `item`: node item
/// * `left`: optional pointer to left child node
/// * `right`: optional pointer to right child node
pub struct Node<T> {
    color: Color,
    parent: Option<NonNull<Node<T>>>,
    item: T,
    left: Option<NonNull<Node<T>>>,
    right: Option<NonNull<Node<T>>>,
}

/// Black token state for removal operation.
/// If black token is on a node, save node type and pointer to node
/// else, black token is on a null node, save null node type and pointer to parent node
#[derive(Debug, PartialEq)]
enum BlackTokenState<T> {
    SomeNode {
        node_ptr: NonNull<Node<T>>,
        node_type: NodeType,
    },
    Null {
        parent_ptr: NonNull<Node<T>>,
        node_type: NodeType,
    },
}

impl<T> Node<T>
where
    T: Debug + PartialEq,
{
    /// Create new node with heap allocation
    ///
    /// * `parent_ptr`: optional pointer to parent node for the new node
    /// * `item`: item in new node
    fn new_node(parent_ptr: Option<NonNull<Node<T>>>, item: T) -> NonNull<Node<T>> {
        // create memory layout for a single node
        let layout = alloc::Layout::new::<Node<T>>();
        // allocate memory
        let raw_ptr = unsafe { alloc::alloc(layout) };
        // if memory allocation fails, signal error
        if raw_ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }
        // create non-null pointer
        let non_null_ptr = unsafe { NonNull::new_unchecked(raw_ptr as *mut Node<T>) };

        // new nodes are red except for root node
        let color = if parent_ptr.is_some() {
            Color::Red
        } else {
            Color::Black
        };

        // write node and return pointer
        let node = Node {
            color,
            parent: parent_ptr,
            item,
            left: None,
            right: None,
        };
        unsafe { non_null_ptr.write(node) };
        non_null_ptr
    }

    /// Check if node is root node
    ///
    /// * `node_ptr`: pointer to node
    fn is_root(node_ptr: NonNull<Node<T>>) -> bool {
        // only root node's parent is None
        unsafe { node_ptr.read() }.parent.is_none()
    }

    /// Get node type (Left/Right/Root)
    ///
    /// * `node_ptr`: pointer to node
    fn get_node_type(node_ptr: NonNull<Node<T>>) -> NodeType {
        let node = unsafe { node_ptr.read() };
        match node.parent {
            Some(parent_ptr) => {
                // return node type depending on whether node
                // is parent's left or right child node
                let parent = unsafe { parent_ptr.read() };
                if let Some(left) = parent.left
                    && node_ptr == left
                {
                    NodeType::Left
                } else if let Some(right) = parent.right
                    && node_ptr == right
                {
                    NodeType::Right
                } else {
                    unreachable!(
                        "Node mislink with parent; node: [{:?}]; parent: [{:?}]",
                        node, parent
                    );
                }
            }
            // only root node's parent is None
            None => NodeType::Root,
        }
    }

    /// Get optional pointer to left child node
    ///
    /// * `node_ptr`: pointer to node
    fn get_left_ptr(node_ptr: NonNull<Node<T>>) -> Option<NonNull<Node<T>>> {
        unsafe { node_ptr.read() }.left
    }

    /// Get optional pointer to right child node
    ///
    /// * `node_ptr`: pointer to node
    fn get_right_ptr(node_ptr: NonNull<Node<T>>) -> Option<NonNull<Node<T>>> {
        unsafe { node_ptr.read() }.right
    }

    /// Get optional pointer to parent node
    ///
    /// * `node_ptr`: pointer to node
    fn get_parent_ptr(node_ptr: NonNull<Node<T>>) -> Option<NonNull<Node<T>>> {
        unsafe { node_ptr.read() }.parent
    }

    /// Get optional pointer to sibling node
    ///
    /// * `parent_node_ptr`: pointer to parent node
    /// * `child_node_type`: node type of current child node, can only be Left/Right node type.
    fn get_sibling_ptr(
        parent_node_ptr: NonNull<Node<T>>,
        child_node_type: &NodeType,
    ) -> Option<NonNull<Node<T>>> {
        match child_node_type {
            NodeType::Left => Node::get_right_ptr(parent_node_ptr),
            NodeType::Right => Node::get_left_ptr(parent_node_ptr),
            NodeType::Root => unreachable!("Child node type cannot be root"),
        }
    }

    /// Get pointer to min node within subtree
    ///
    /// * `subtree_root_ptr`: pointer to subtree root
    fn get_subtree_min_ptr(subtree_root_ptr: NonNull<Node<T>>) -> NonNull<Node<T>> {
        let mut curr_ptr = subtree_root_ptr;
        while let Some(left_ptr) = unsafe { curr_ptr.read() }.left {
            curr_ptr = left_ptr;
        }
        curr_ptr
    }

    /// Get pointer to max node within subtree
    ///
    /// * `subtree_root_ptr`: pointer to subtree root
    fn get_subtree_max_ptr(subtree_root_ptr: NonNull<Node<T>>) -> NonNull<Node<T>> {
        let mut curr_ptr = subtree_root_ptr;
        while let Some(right_ptr) = unsafe { curr_ptr.read() }.right {
            curr_ptr = right_ptr;
        }
        curr_ptr
    }

    /// Get color of node; null node is black
    ///
    /// * `node_ptr`: pointer to node
    fn get_node_color(node_ptr: Option<NonNull<Node<T>>>) -> Color {
        match node_ptr {
            Some(ptr) => unsafe { ptr.read() }.color,
            None => Color::Black,
        }
    }
}

impl<T> RedBlackTree<T>
where
    T: Ord + Debug,
{
    /// Create new empty red-black tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// assert_eq!(tree.size(), 0);
    /// assert!(tree.is_empty());
    /// ```
    pub fn new() -> RedBlackTree<T> {
        RedBlackTree {
            root: None,
            size: 0,
        }
    }

    /// Get number of nodes in red-black tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// assert_eq!(tree.size(), 0);
    /// tree.insert(5);
    /// assert_eq!(tree.size(), 1);
    /// tree.remove(&5);
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
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// assert!(tree.is_empty());
    /// tree.insert(5);
    /// assert!(!tree.is_empty());
    /// tree.remove(&5);
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Insert item to tree
    ///
    /// * `item`: item to insert
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::{RedBlackTree, DuplicateItemErr};
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// assert!(!tree.contains(&5));
    /// assert_eq!(tree.insert(5), Ok(()));
    /// assert!(tree.contains(&5));
    /// assert_eq!(tree.insert(5), Err(DuplicateItemErr));
    /// ```
    pub fn insert(&mut self, item: T) -> Result<(), DuplicateItemErr> {
        let mut curr_ptr = match self.root {
            Some(root_ptr) => root_ptr,
            None => {
                // if tree is empty, assign root to new node and return
                self.root = Some(Node::new_node(None, item));
                // increment tree size
                self.size = 1;
                return Ok(());
            }
        };

        // traverse to leaf node and insert new node
        loop {
            let mut curr_node = unsafe { curr_ptr.read() };
            match curr_node.item.cmp(&item) {
                Ordering::Greater => {
                    if let Some(left_ptr) = curr_node.left {
                        // continue traversal if there is left child node
                        curr_ptr = left_ptr;
                    } else {
                        // attach new node as left child
                        let new_node_ptr = Node::new_node(Some(curr_ptr), item);
                        curr_node.left = Some(new_node_ptr);
                        unsafe { curr_ptr.write(curr_node) };
                        curr_ptr = new_node_ptr;
                        break;
                    }
                }
                Ordering::Less => {
                    if let Some(right_ptr) = curr_node.right {
                        // continue traversal if there is right child node
                        curr_ptr = right_ptr;
                    } else {
                        // attach new node as right child
                        let new_node_ptr = Node::new_node(Some(curr_ptr), item);
                        curr_node.right = Some(new_node_ptr);
                        unsafe { curr_ptr.write(curr_node) };
                        curr_ptr = new_node_ptr;
                        break;
                    }
                }
                // return duplicate item error since it's not allowed
                Ordering::Equal => return Err(DuplicateItemErr),
            }
        }

        // rebalance after insert item;
        // current node pointer should point to new node, and new node cannot be root
        self.insertion_rebalance(curr_ptr);
        // increment tree size
        self.size += 1;
        Ok(())
    }

    /// rebalance tree after insertion
    ///
    /// * `curr_ptr`: pointer to newly inserted node
    fn insertion_rebalance(&mut self, mut curr_ptr: NonNull<Node<T>>) {
        // rebalance stops when current node pointer points to root
        while !Node::is_root(curr_ptr) {
            // NOTE: - current node is not root, therefore:
            //       - parent node must exist
            //
            // We can safely unwrap parent.
            let parent_ptr = Node::get_parent_ptr(curr_ptr).unwrap();
            let mut parent = unsafe { parent_ptr.read() };
            let parent_node_type = Node::get_node_type(parent_ptr);

            // NOTE: current node is RED
            //
            // There are 2 scenarios, either current node is newly-inserted,
            // or current node is previous loop iteration's grandparent node
            // due to re-paint. In both cases, current node is red.
            // If parent node is black, there is no red-black violation,
            // rebalance is complete.
            if parent.color == Color::Black {
                break;
            }

            // NOTE: - parent node must be RED; so parent cannot be root node
            //       - grandparent node must exist and must be black
            //
            // we can unwrap grandparent node safely
            let grandparent_ptr = Node::get_parent_ptr(parent_ptr).unwrap();

            // NOTE: uncle node can be null
            let uncle_ptr_opt = Node::get_sibling_ptr(grandparent_ptr, &parent_node_type);

            match Node::get_node_color(uncle_ptr_opt) {
                Color::Red => {
                    // NOTE: - uncle node is RED, therefore
                    //       - uncle node is not null, and
                    //       - grandparent must be black
                    let uncle_ptr = uncle_ptr_opt.unwrap();
                    let mut uncle = unsafe { uncle_ptr.read() };

                    // repaint uncle and parent node to black
                    uncle.color = Color::Black;
                    unsafe { uncle_ptr.write(uncle) };
                    parent.color = Color::Black;
                    unsafe { parent_ptr.write(parent) };

                    // if grandparent is not root, re-paint it red
                    if !Node::is_root(grandparent_ptr) {
                        let mut grandparent = unsafe { grandparent_ptr.read() };
                        grandparent.color = Color::Red;
                        unsafe { grandparent_ptr.write(grandparent) };
                    }

                    // resume rebalancing at grandparent node;
                    // loop will halt of grandparent node is root
                    curr_ptr = grandparent_ptr;
                }
                Color::Black => {
                    // uncle is black, rotate/swap color to rebalance
                    let curr_node_type = Node::get_node_type(curr_ptr);
                    match (&curr_node_type, &parent_node_type) {
                        (NodeType::Left, NodeType::Left) => {
                            self.subtree_rotate_right(grandparent_ptr, true)
                        }
                        (NodeType::Right, NodeType::Right) => {
                            self.subtree_rotate_left(grandparent_ptr, true)
                        }
                        (NodeType::Left, NodeType::Right) => {
                            self.subtree_rotate_right(parent_ptr, false);
                            self.subtree_rotate_left(grandparent_ptr, true);
                        }
                        (NodeType::Right, NodeType::Left) => {
                            self.subtree_rotate_left(parent_ptr, false);
                            self.subtree_rotate_right(grandparent_ptr, true);
                        }
                        _ => unreachable!(
                            "Current node and parent node cannot be root node; \
                                current node type: [{:?}]; parent node type: [{:?}]; \
                                current node [{:?}]; parent node [{:?}]",
                            curr_node_type,
                            parent_node_type,
                            unsafe { curr_ptr.read() },
                            parent
                        ),
                    };
                    break;
                }
            }
        }
    }

    /// Remove node with item, and return item
    ///
    /// * `item`: item to remove
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::{RedBlackTree, DuplicateItemErr};
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// tree.insert(5);
    /// assert!(tree.contains(&5));
    /// tree.remove(&5);
    /// assert!(!tree.contains(&5));
    /// ```
    pub fn remove(&mut self, item: &T) -> Option<T> {
        // if tree is empty, return None
        let mut curr_ptr = self.root?;

        // find node with same item;
        // if leaf node is reached but no node with item found, return None
        loop {
            let curr_node = unsafe { curr_ptr.read() };
            match curr_node.item.cmp(item) {
                Ordering::Greater => {
                    if let Some(left_ptr) = curr_node.left {
                        curr_ptr = left_ptr;
                    } else {
                        return None;
                    }
                }
                Ordering::Less => {
                    if let Some(right_ptr) = curr_node.right {
                        curr_ptr = right_ptr;
                    } else {
                        return None;
                    }
                }
                Ordering::Equal => break,
            }
        }

        // remove node, and receive contained item, and optional black token
        let (black_token_state_opt, item) = self.remove_node(curr_ptr);
        // decrement tree size
        self.size -= 1;
        // if black token is present, rebalance the tree
        if let Some(black_token_state) = black_token_state_opt {
            self.removal_rebalance(black_token_state);
        }
        Some(item)
    }

    /// Remove node, and reconnect child/parent node of removed node.
    ///
    /// * `node_ptr`: pointer to node to be removed
    fn remove_node(
        &mut self,
        mut removal_node_ptr: NonNull<Node<T>>,
    ) -> (Option<BlackTokenState<T>>, T) {
        let right_ptr_opt = Node::get_right_ptr(removal_node_ptr);
        let left_ptr_opt = Node::get_left_ptr(removal_node_ptr);

        // Similar to removal operation in BST, when the node to remove has 0 or 1
        // child node, just reconnect removal node's parent and child;
        // if removal node has 2 child, swap node item with its predecessor (max node
        // in subtree with left child as root), and remove the predecessor node instead.
        let (removal_ptr, child_ptr_opt) = match (left_ptr_opt, right_ptr_opt) {
            (None, None) => (removal_node_ptr, None),
            (None, Some(right_ptr)) => (removal_node_ptr, Some(right_ptr)),
            (Some(left_ptr), None) => (removal_node_ptr, Some(left_ptr)),
            (Some(left_ptr), Some(_)) => {
                let mut predecessor_ptr = Node::get_subtree_max_ptr(left_ptr);
                let predecessor_item = &mut unsafe { predecessor_ptr.as_mut() }.item;
                let removal_node_item = &mut unsafe { removal_node_ptr.as_mut() }.item;
                mem::swap(predecessor_item, removal_node_item);
                // Predecessor should be the right-most child of subtree,
                // so it should only have left child.
                (predecessor_ptr, unsafe { predecessor_ptr.read() }.left)
            }
        };

        let removal_node = unsafe { removal_ptr.read() };
        let removal_node_type = Node::get_node_type(removal_ptr);

        match removal_node_type {
            NodeType::Left => {
                // removal node type is not root, so must have parent,
                // can safely unwrap here
                let parent_ptr = removal_node.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.left = child_ptr_opt;
                unsafe {
                    parent_ptr.write(parent);
                };
                // if optional child pointer points to a node,
                // connect it to parent
                if let Some(child_ptr) = child_ptr_opt {
                    let mut child = unsafe { child_ptr.read() };
                    child.parent = Some(parent_ptr);
                    unsafe { child_ptr.write(child) };
                }
            }
            NodeType::Right => {
                // removal node type is not root, so must have parent,
                // can safely unwrap here
                let parent_ptr = removal_node.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.right = child_ptr_opt;
                unsafe {
                    parent_ptr.write(parent);
                };
                // if optional child pointer points to a node,
                // connect it to parent
                if let Some(child_ptr) = child_ptr_opt {
                    let mut child = unsafe { child_ptr.read() };
                    child.parent = Some(parent_ptr);
                    unsafe { child_ptr.write(child) };
                }
            }
            NodeType::Root => {
                self.root = child_ptr_opt;
                // if optional child pointer points to a node,
                // the child node becomes root, set parent to None,
                // and color it black.
                if let Some(child_ptr) = child_ptr_opt {
                    let mut child = unsafe { child_ptr.read() };
                    child.parent = None;
                    child.color = Color::Black;
                    unsafe { child_ptr.write(child) };
                }
            }
        }

        // If removed node is red, red-black property is not violated,
        // no rebalancing required.
        // Otherwise, red-black property is violated due to different
        // black node heights among leaf nodes, place black token on
        // removed node's replacement node (can be null)
        let black_token_state_opt = match removal_node.color {
            Color::Red => None,
            Color::Black => match child_ptr_opt {
                // if removed node is replaced by an actual node,
                // record node pointer and its node type
                Some(child_ptr) => Some(BlackTokenState::SomeNode {
                    node_ptr: child_ptr,
                    node_type: removal_node_type,
                }),
                // if removed node becomes null, and the removed node was not root (had parent),
                // record parent pointer and removed node's node type
                None => match removal_node.parent {
                    Some(parent) => Some(BlackTokenState::Null {
                        parent_ptr: parent,
                        node_type: removal_node_type,
                    }),
                    // removed node with no child/parent, so it's the last node in tree,
                    // the tree is empty after removal, rebalancing is not needed.
                    None => None,
                },
            },
        };

        // get item from removed node, then drop node to prevent memory leak
        let item = unsafe {
            // once pointer is converted to box, it'll be drop at the end of scope.
            let boxed_removal_node = Box::from_raw(removal_ptr.as_ptr());
            boxed_removal_node.item
        };

        (black_token_state_opt, item)
    }

    /// Rebalance tree after removal
    ///
    /// * `black_token_state`: black token state
    fn removal_rebalance(&mut self, mut black_token_state: BlackTokenState<T>) {
        // NOTE: the tree cannot be empty at this point,
        // otherwise black token would not be generated.
        loop {
            // Halt if black token is on root.
            // If black token is on some node, the tree cannot be empty,
            // so root can be unwrapped safely.
            if let BlackTokenState::SomeNode { node_ptr, .. } = black_token_state
                && node_ptr == self.root.unwrap()
            {
                break;
            }

            // - NOTE: black token is not on root
            let black_token_ptr_opt = match black_token_state {
                BlackTokenState::SomeNode { node_ptr, .. } => Some(node_ptr),
                BlackTokenState::Null { .. } => None,
            };
            let black_token_color = Node::get_node_color(black_token_ptr_opt);
            let black_token_node_type = match black_token_state {
                BlackTokenState::SomeNode { ref node_type, .. } => node_type,
                BlackTokenState::Null { ref node_type, .. } => node_type,
            };

            let parent_ptr = match black_token_state {
                BlackTokenState::SomeNode { node_ptr, .. } => {
                    // black token is not on root, so it's safe to unwrap parent
                    Node::get_parent_ptr(node_ptr).unwrap()
                }
                BlackTokenState::Null { parent_ptr, .. } => parent_ptr,
            };
            match black_token_color {
                // if black token node is red, just repaint it black and black token can be removed
                Color::Red => {
                    // if black token node is red, the node cannot be null, safe to unwrap
                    let black_token_ptr = black_token_ptr_opt.unwrap();
                    let mut black_token_node = unsafe { black_token_ptr.read() };
                    black_token_node.color = Color::Black;
                    unsafe { black_token_ptr.write(black_token_node) };
                    break;
                }
                Color::Black => {
                    // NOTE: sibling node must exist
                    // The black token node was created because removed node was black,
                    // and because red-black property of same black node height among all
                    // leaf nodes, sibling node must exist, and it's safe to unwrap.
                    let sibling_ptr =
                        Node::get_sibling_ptr(parent_ptr, black_token_node_type).unwrap();
                    let mut sibling = unsafe { sibling_ptr.read() };

                    match sibling.color {
                        // If sibling is red, rotate, but keep black token on the same node,
                        // the rebalancing will be resolved in subsequent loop iterations.
                        //
                        // Explanation:
                        // - After rotation, black token node's parent changes from black to red,
                        // new sibling node is old sibling's disconnected child node. Since old
                        // sibling is red, the new sibling must be black.
                        // - In the next iteration,
                        //   - if both nephews are black, sibling is colored red, and black token
                        //     propagates to parent, and since parent is red, it'll be fixed in
                        //     another iteration
                        //  - if any nephew is red, rotation will rebalance the nodes.
                        Color::Red => match black_token_node_type {
                            NodeType::Left => self.subtree_rotate_left(parent_ptr, true),
                            NodeType::Right => self.subtree_rotate_right(parent_ptr, true),
                            NodeType::Root => {
                                unreachable!(
                                    "Removal rebalancing should not occur when black token \
                                        is placed on root node"
                                );
                            }
                        },
                        Color::Black => {
                            let left_nephew_ptr_opt = Node::get_left_ptr(sibling_ptr);
                            let right_nephew_ptr_opt = Node::get_right_ptr(sibling_ptr);
                            let left_nephew_color = Node::get_node_color(left_nephew_ptr_opt);
                            let right_nephew_color = Node::get_node_color(right_nephew_ptr_opt);

                            // If both nephew are black, color sibling red,
                            // and move black token to parent node
                            if left_nephew_color == Color::Black
                                && right_nephew_color == Color::Black
                            {
                                sibling.color = Color::Red;
                                unsafe { sibling_ptr.write(sibling) };
                                let parent_node_type = Node::get_node_type(parent_ptr);
                                black_token_state = BlackTokenState::SomeNode {
                                    node_ptr: parent_ptr,
                                    node_type: parent_node_type,
                                };
                            } else {
                                // NOTE: one or both nephews are red
                                //
                                // depending on colors of nephews, 1 or 2 rotations are needed
                                // to complete rebalance
                                match black_token_node_type {
                                    NodeType::Left => {
                                        if right_nephew_color == Color::Black {
                                            self.subtree_rotate_right(sibling_ptr, true);
                                            self.subtree_rotate_left(parent_ptr, true);
                                            // color new uncle node (old sibling node) to black
                                            let mut sibling = unsafe { sibling_ptr.read() };
                                            sibling.color = Color::Black;
                                            unsafe { sibling_ptr.write(sibling) };
                                        } else {
                                            self.subtree_rotate_left(parent_ptr, true);
                                            // right nephew is red so can't be null, and can be
                                            // unwrapped safely
                                            let right_nephew_ptr = right_nephew_ptr_opt.unwrap();
                                            // color new uncle node (old right nephew node) to black
                                            let mut right_nephew =
                                                unsafe { right_nephew_ptr.read() };
                                            right_nephew.color = Color::Black;
                                            unsafe { right_nephew_ptr.write(right_nephew) };
                                        }
                                    }
                                    NodeType::Right => {
                                        if left_nephew_color == Color::Black {
                                            self.subtree_rotate_left(sibling_ptr, true);
                                            self.subtree_rotate_right(parent_ptr, true);
                                            // color new uncle node (old sibling node) to black
                                            let mut sibling = unsafe { sibling_ptr.read() };
                                            sibling.color = Color::Black;
                                            unsafe { sibling_ptr.write(sibling) };
                                        } else {
                                            self.subtree_rotate_right(parent_ptr, true);
                                            // right nephew is red so can't be null, and can be
                                            // unwrapped safely
                                            let left_nephew_ptr = left_nephew_ptr_opt.unwrap();
                                            // color new uncle node (old left nephew node) to black
                                            let mut left_nephew = unsafe { left_nephew_ptr.read() };
                                            left_nephew.color = Color::Black;
                                            unsafe { left_nephew_ptr.write(left_nephew) };
                                        }
                                    }
                                    NodeType::Root => {
                                        unreachable!(
                                            "Removal rebalancing should not occur when black token \
                                        is placed on root node"
                                        );
                                    }
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    /// Rotate subtree left
    ///
    /// ### Note
    ///
    /// will panic if subtree root does not have a right child
    ///
    /// * `subtree_root_ptr`: pointer to subtree root
    /// * `swap_color`: flat to swap colors in subtree root node and its right child node
    fn subtree_rotate_left(&mut self, subtree_root_ptr: NonNull<Node<T>>, swap_color: bool) {
        let subtree_root_node_type = Node::get_node_type(subtree_root_ptr);

        // this function assumes subtree root node has a right child, unwrapping
        let right_ptr = Node::get_right_ptr(subtree_root_ptr).unwrap();
        let right_left_ptr_opt = Node::get_left_ptr(right_ptr);
        let mut subtree_root = unsafe { subtree_root_ptr.read() };
        let mut right = unsafe { right_ptr.read() };

        // connect old/new subtree roots to their parents
        right.parent = subtree_root.parent;
        subtree_root.parent = Some(right_ptr);

        // connect old/new subtree roots to their child
        subtree_root.right = right_left_ptr_opt;
        right.left = Some(subtree_root_ptr);

        // swap color if needed
        if swap_color {
            mem::swap(&mut right.color, &mut subtree_root.color);
        }

        // If subtree root is not root of the entire tree,
        // connect old subtree root's parent to new subtree root and write parent.
        // Else, reconnect tree root
        match subtree_root_node_type {
            NodeType::Left => {
                let parent_ptr = right.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.left = Some(right_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            NodeType::Right => {
                let parent_ptr = right.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.right = Some(right_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            NodeType::Root => {
                self.root = Some(right_ptr);
            }
        }

        // write old/new subtree root
        unsafe { subtree_root_ptr.write(subtree_root) };
        unsafe { right_ptr.write(right) };

        // if old subtree root's right node is not null, reconnect it back
        if let Some(right_left_ptr) = right_left_ptr_opt {
            let mut right_left = unsafe { right_left_ptr.read() };
            right_left.parent = Some(subtree_root_ptr);
            unsafe { right_left_ptr.write(right_left) };
        }
    }

    /// Rotate subtree right
    ///
    /// ### Note
    ///
    /// will panic if subtree root does not have a left child
    ///
    /// * `subtree_root_ptr`: pointer to subtree root
    /// * `swap_color`: flat to swap colors in subtree root node and its left child node
    fn subtree_rotate_right(&mut self, subtree_root_ptr: NonNull<Node<T>>, swap_color: bool) {
        let subtree_root_node_type = Node::get_node_type(subtree_root_ptr);

        // this function assumes subtree root node has a left child, unwrapping
        let left_ptr = Node::get_left_ptr(subtree_root_ptr).unwrap();
        let left_right_ptr_opt = Node::get_right_ptr(left_ptr);
        let mut subtree_root = unsafe { subtree_root_ptr.read() };
        let mut left = unsafe { left_ptr.read() };

        // connect old/new subtree roots to their parents
        left.parent = subtree_root.parent;
        subtree_root.parent = Some(left_ptr);

        // connect old/new subtree roots to their child
        subtree_root.left = left_right_ptr_opt;
        left.right = Some(subtree_root_ptr);

        // swap color if needed
        if swap_color {
            mem::swap(&mut left.color, &mut subtree_root.color);
        }

        // If subtree root is not root of the entire tree,
        // connect old subtree root's parent to new subtree root and write parent.
        // Else, reconnect tree root
        match subtree_root_node_type {
            NodeType::Left => {
                let parent_ptr = left.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.left = Some(left_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            NodeType::Right => {
                let parent_ptr = left.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.right = Some(left_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            NodeType::Root => {
                self.root = Some(left_ptr);
            }
        }

        // write old/new subtree root
        unsafe { subtree_root_ptr.write(subtree_root) };
        unsafe { left_ptr.write(left) };

        // if old subtree root's left node is not null, reconnect it back
        if let Some(left_right_ptr) = left_right_ptr_opt {
            let mut left_right = unsafe { left_right_ptr.read() };
            left_right.parent = Some(subtree_root_ptr);
            unsafe { left_right_ptr.write(left_right) };
        }
    }

    /// Check if tree contains an item
    ///
    /// * `item`: reference to item
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// assert!(!tree.contains(&5));
    /// tree.insert(5);
    /// assert!(tree.contains(&5));
    /// assert_eq!(tree.remove(&5), Some(5));
    /// assert!(!tree.contains(&5));
    /// assert_eq!(tree.remove(&5), None);
    /// ```
    pub fn contains(&self, item: &T) -> bool {
        let mut curr_ptr = match self.root {
            Some(root) => root,
            None => return false,
        };

        // traverse tree,
        // if leaf node reached without finding item, item does not exist
        loop {
            let node = unsafe { curr_ptr.read() };
            match node.item.cmp(item) {
                Ordering::Greater => {
                    if let Some(left_ptr) = node.left {
                        curr_ptr = left_ptr;
                    } else {
                        return false;
                    }
                }
                Ordering::Less => {
                    if let Some(right_ptr) = node.right {
                        curr_ptr = right_ptr;
                    } else {
                        return false;
                    }
                }
                Ordering::Equal => return true,
            }
        }
    }

    /// Get min item in tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// tree.insert(10);
    /// tree.insert(5);
    /// assert_eq!(tree.min(), Some(&5));
    /// tree.pop_min();
    /// assert_eq!(tree.min(), Some(&10));
    /// tree.pop_min();
    /// assert_eq!(tree.min(), None);
    /// ```
    pub fn min(&self) -> Option<&T> {
        // From root node, traverse left until leaf node
        let mut curr_ptr = self.root?;
        while let Some(left_ptr) = unsafe { curr_ptr.read() }.left {
            curr_ptr = left_ptr;
        }
        Some(&unsafe { curr_ptr.as_ref() }.item)
    }

    /// Get max item in tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// tree.insert(5);
    /// tree.insert(10);
    /// assert_eq!(tree.max(), Some(&10));
    /// tree.pop_max();
    /// assert_eq!(tree.max(), Some(&5));
    /// tree.pop_max();
    /// assert_eq!(tree.max(), None);
    /// ```
    pub fn max(&self) -> Option<&T> {
        // From root node, traverse right until leaf node
        let mut curr_ptr = self.root?;
        while let Some(right_ptr) = unsafe { curr_ptr.read() }.right {
            curr_ptr = right_ptr;
        }
        Some(&unsafe { curr_ptr.as_ref() }.item)
    }

    /// Pop min node from tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// tree.insert(10);
    /// tree.insert(5);
    /// assert_eq!(tree.pop_min(), Some(5));
    /// assert_eq!(tree.pop_min(), Some(10));
    /// assert_eq!(tree.pop_min(), None);
    /// ```
    pub fn pop_min(&mut self) -> Option<T> {
        // if tree is not empty, get pointer to min node
        let root_ptr = self.root?;
        let min_ptr = Node::get_subtree_min_ptr(root_ptr);
        // remove the node
        let (black_token_opt, item) = self.remove_node(min_ptr);
        // decrement tree size
        self.size -= 1;
        // handle black token if present
        if let Some(black_token) = black_token_opt {
            self.removal_rebalance(black_token);
        }
        Some(item)
    }

    /// Pop max node from tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// tree.insert(5);
    /// tree.insert(10);
    /// assert_eq!(tree.pop_max(), Some(10));
    /// assert_eq!(tree.pop_max(), Some(5));
    /// assert_eq!(tree.pop_max(), None);
    /// ```
    pub fn pop_max(&mut self) -> Option<T> {
        // if tree is not empty, get pointer to min node
        let root_ptr = self.root?;
        let max_ptr = Node::get_subtree_max_ptr(root_ptr);
        // remove the node
        let (black_token_opt, item) = self.remove_node(max_ptr);
        // decrement tree size
        self.size -= 1;
        // handle black token if present
        if let Some(black_token) = black_token_opt {
            self.removal_rebalance(black_token);
        }
        Some(item)
    }

    /// Get iterator
    ///
    /// * `order`: traversal order of iterator
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::{RedBlackTree, TraversalOrder};
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.iter(TraversalOrder::Level);
    /// for i in [2, 1, 4, 3, 5] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut iter = tree.iter(TraversalOrder::Pre);
    /// for i in [2, 1, 4, 3, 5] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut iter = tree.iter(TraversalOrder::In);
    /// for i in 1..=5 {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut iter = tree.iter(TraversalOrder::Post);
    /// for i in [1, 3, 5, 4, 2] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self, order: TraversalOrder) -> Iter<T> {
        Iter {
            curr: self.root.map(|root| unsafe { root.as_ref() }),
            nodes: VecDeque::new(),
            post_order_node_groups: VecDeque::new(),
            order,
        }
    }

    /// Get into-iterator which consumes the tree
    ///
    /// * `order`: traversal order of into-iterator
    ///
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::{RedBlackTree, TraversalOrder};
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::new();
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.iter(TraversalOrder::Level);
    /// for i in [2, 1, 4, 3, 5] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.iter(TraversalOrder::Pre);
    /// for i in [2, 1, 4, 3, 5] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.iter(TraversalOrder::In);
    /// for i in 1..=5 {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.iter(TraversalOrder::Post);
    /// for i in [1, 3, 5, 4, 2] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn into_iter(mut self, order: TraversalOrder) -> IntoIter<T> {
        IntoIter {
            curr: self.root.take(),
            ptrs: VecDeque::new(),
            post_order_ptr_groups: VecDeque::new(),
            order,
        }
    }
}

impl<T> Default for RedBlackTree<T>
where
    T: Ord + Debug,
{
    /// Create default empty red-black tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::red_black_tree::RedBlackTree;
    /// let mut tree: RedBlackTree<i32> = RedBlackTree::default();
    /// assert_eq!(tree.size(), 0);
    /// assert!(tree.is_empty());
    /// ```
    fn default() -> Self {
        Self::new()
    }
}

/// Iterator struct
///
/// * `curr`: current node being processed
/// * `nodes`: nodes to be processed
/// * `post_order_node_groups`: node groups to be processed for post order traversal
///   each node group consists of a node, and its right child node if child node is
///   not yet processed.
/// * `order`: traversal order
pub struct Iter<'a, T> {
    curr: Option<&'a Node<T>>,
    nodes: VecDeque<&'a Node<T>>,
    post_order_node_groups: VecDeque<(&'a Node<T>, Option<&'a Node<T>>)>,
    order: TraversalOrder,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Iterator next() implementation, routes to iterator based on traversal order
    fn next(&mut self) -> Option<Self::Item> {
        match self.order {
            TraversalOrder::Level => self.level_order_next(),
            TraversalOrder::Pre => self.pre_order_next(),
            TraversalOrder::In => self.in_order_next(),
            TraversalOrder::Post => self.post_order_next(),
        }
    }
}

impl<'a, T> Iter<'a, T> {
    /// Iterator next() for level-order traversal
    fn level_order_next(&mut self) -> Option<&'a T> {
        self.curr.map(|curr_node| {
            // if children are present, push to processing queue
            if let Some(left_ptr) = curr_node.left {
                self.nodes.push_front(unsafe { left_ptr.as_ref() });
            }
            if let Some(right_ptr) = curr_node.right {
                self.nodes.push_front(unsafe { right_ptr.as_ref() });
            }

            // save current node item
            let item = &curr_node.item;
            // pop a node from processing queue and assign to current node so
            // that it can be processed in next next() call
            self.curr = self.nodes.pop_back();
            item
        })
    }

    /// Iterator next() for pre-order traversal
    fn pre_order_next(&mut self) -> Option<&'a T> {
        self.curr.map(|curr_node| {
            // if children are present, push to processing stack, right child goes in first
            if let Some(right_ptr) = curr_node.right {
                self.nodes.push_front(unsafe { right_ptr.as_ref() });
            }
            if let Some(left_ptr) = curr_node.left {
                self.nodes.push_front(unsafe { left_ptr.as_ref() });
            }

            // save current node item
            let item = &curr_node.item;
            // pop a node from processing stack and assign to current node so
            // that it can be processed in next next() call
            self.curr = self.nodes.pop_front();
            item
        })
    }

    /// Iterator next() for in-order traversal
    fn in_order_next(&mut self) -> Option<&'a T> {
        // traverse left and save all nodes to stack
        while let Some(curr_node) = self.curr {
            self.nodes.push_front(curr_node);
            self.curr = curr_node.left.map(|left_ptr| unsafe { left_ptr.as_ref() })
        }

        // pop a node from stack, assign its right child to current node if present
        // so that it can be processed in next next() call.
        self.nodes.pop_front().map(|front_node| {
            self.curr = front_node
                .right
                .map(|right_ptr| unsafe { right_ptr.as_ref() });
            &front_node.item
        })
    }

    /// Iterator next() for post-order traversal
    fn post_order_next(&mut self) -> Option<&'a T> {
        loop {
            // traverse left, for each node, push the node and its right child as
            // a node group to stack
            while let Some(curr_node) = self.curr {
                let right_node = curr_node
                    .right
                    .map(|right_ptr| unsafe { right_ptr.as_ref() });
                self.post_order_node_groups
                    .push_front((curr_node, right_node));
                self.curr = curr_node.left.map(|left_ptr| unsafe { left_ptr.as_ref() });
            }

            // pop a node group from stack, if node group's right child node is present,
            // re-push the node group without the right child node, and assign right
            // child node to current node so that it can be processed in next loop iteration.
            let node_group = self.post_order_node_groups.pop_front()?;
            match node_group.1 {
                Some(right_node) => {
                    self.post_order_node_groups.push_front((node_group.0, None));
                    self.curr = Some(right_node)
                }
                None => return Some(&node_group.0.item),
            };
        }
    }
}

type IntoPostOrderNodeGroups<T> = (NonNull<Node<T>>, Option<NonNull<Node<T>>>);

/// Into-iterator struct
///
/// * `curr`: current node pointer being processed
/// * `ptrs`: node pointers to be processed
/// * `post_order_ptr_groups`: node pointer groups to be processed for post order traversal
///   each node group consists of a node pointer and its right child node pointer
///   if the child node is not yet processed.
/// * `order`: traversal order
pub struct IntoIter<T> {
    curr: Option<NonNull<Node<T>>>,
    ptrs: VecDeque<NonNull<Node<T>>>,
    post_order_ptr_groups: VecDeque<IntoPostOrderNodeGroups<T>>,
    order: TraversalOrder,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    /// Iterator next() implementation, routes to into-iterator based on traversal order
    fn next(&mut self) -> Option<Self::Item> {
        match self.order {
            TraversalOrder::Level => self.level_order_next(),
            TraversalOrder::Pre => self.pre_order_next(),
            TraversalOrder::In => self.in_order_next(),
            TraversalOrder::Post => self.post_order_next(),
        }
    }
}

impl<T> IntoIter<T> {
    /// Into-iterator next() for level-order traversal
    fn level_order_next(&mut self) -> Option<T> {
        self.curr.map(|curr_ptr| {
            // If children are present, push to processing queue.
            // Convert current pointer to box so that node can be dropped
            let curr_node = unsafe { Box::from_raw(curr_ptr.as_ptr()) };
            if let Some(left_ptr) = curr_node.left {
                self.ptrs.push_front(left_ptr);
            }
            if let Some(right_ptr) = curr_node.right {
                self.ptrs.push_front(right_ptr);
            }

            // save current node item
            let item = curr_node.item;
            // pop a node from processing queue and assign to current node so
            // that it can be processed in next next() call
            self.curr = self.ptrs.pop_back();
            item
        })
    }

    /// Into-iterator next() for pre-order traversal
    fn pre_order_next(&mut self) -> Option<T> {
        self.curr.map(|curr_ptr| {
            // If children are present, push to processing stack, right child goes in first
            // Convert current pointer to box so that node can be dropped
            let curr_node = unsafe { Box::from_raw(curr_ptr.as_ptr()) };
            if let Some(right_ptr) = curr_node.right {
                self.ptrs.push_front(right_ptr);
            }
            if let Some(left_ptr) = curr_node.left {
                self.ptrs.push_front(left_ptr);
            }

            // save current node item
            let item = curr_node.item;
            // pop a node from processing stack and assign to current node so
            // that it can be processed in next next() call
            self.curr = self.ptrs.pop_front();
            item
        })
    }

    /// Into-iterator next() for in-order traversal
    fn in_order_next(&mut self) -> Option<T> {
        // traverse left and save all nodes to stack
        while let Some(curr_ptr) = self.curr {
            self.ptrs.push_front(curr_ptr);
            self.curr = unsafe { curr_ptr.read() }.left;
        }

        // pop a node from stack, assign its right child to current node if present
        // so that it can be processed in next next() call.
        self.ptrs.pop_front().map(|front_ptr| {
            // convert popped pointer to box so that node can be dropped
            let node = unsafe { Box::from_raw(front_ptr.as_ptr()) };
            self.curr = node.right;
            node.item
        })
    }

    /// Into-iterator next() for post-order traversal
    fn post_order_next(&mut self) -> Option<T> {
        loop {
            // traverse left, for each node, push the node and its right child as
            // a node group to stack
            while let Some(curr_ptr) = self.curr {
                let curr_node = unsafe { curr_ptr.read() };
                let right_ptr = curr_node.right;
                self.post_order_ptr_groups.push_front((curr_ptr, right_ptr));
                self.curr = curr_node.left;
            }

            // pop a node group from stack, if node group's right child node is present,
            // re-push the node group without the right child node, and assign right
            // child node to current node so that it can be processed in next loop iteration.
            let ptr_group = self.post_order_ptr_groups.pop_front()?;
            match ptr_group.1 {
                Some(right_ptr) => {
                    self.post_order_ptr_groups.push_front((ptr_group.0, None));
                    self.curr = Some(right_ptr)
                }
                // convert node pointer to box so that node can be dropped
                None => return Some(unsafe { Box::from_raw(ptr_group.0.as_ptr()) }.item),
            };
        }
    }
}

impl<T> Drop for RedBlackTree<T> {
    /// Drops all nodes in tree
    fn drop(&mut self) {
        let mut nodes = match self.root {
            Some(root) => vec![root],
            None => return,
        };

        while let Some(curr_ptr) = nodes.pop() {
            let node = unsafe { Box::from_raw(curr_ptr.as_ptr()) };
            if let Some(left_ptr) = node.left {
                nodes.push(left_ptr);
            }
            if let Some(right_ptr) = node.right {
                nodes.push(right_ptr);
            }
        }
    }
}

impl<T> Drop for IntoIter<T> {
    /// Into-iterator next() implementation drops processed nodes
    /// Since Into-iterator owns the tree, all nodes must be dropped
    /// or there would be memory leaks. Drop all memory by exhausting
    /// the into-iterator
    fn drop(&mut self) {
        for _ in self.by_ref() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{self, Value};
    use std::collections::{HashMap, HashSet};
    use std::fs;
    use std::path;

    fn new_tilted_tree(mirror: bool) -> RedBlackTree<i32> {
        // if mirror is false, right-tilted tree, else left-tilted
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        for i in 1..=20 {
            match mirror {
                false => {
                    let _ = tree.insert(i);
                }
                true => {
                    let _ = tree.insert(21 - i);
                }
            };
        }
        tree
    }

    fn new_compact_tree(mirror: bool) -> RedBlackTree<i32> {
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        for i in 1..=10 {
            match mirror {
                false => {
                    let _ = tree.insert(i);
                    let _ = tree.insert(21 - i);
                }
                true => {
                    let _ = tree.insert(21 - i);
                    let _ = tree.insert(i);
                }
            };
        }
        tree
    }

    fn new_spread_tree(mirror: bool) -> RedBlackTree<i32> {
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        for i in (1..=10).rev() {
            match mirror {
                false => {
                    let _ = tree.insert(i);
                    let _ = tree.insert(21 - i);
                }
                true => {
                    let _ = tree.insert(21 - i);
                    let _ = tree.insert(i);
                }
            };
        }
        tree
    }

    /// Validate red-black tree
    ///
    /// * `tree`: ref to red-black tree
    fn validate_bst(tree: &RedBlackTree<i32>) {
        // first node has no lower/upper bound
        let min_val: Option<i32> = None;
        let max_val: Option<i32> = None;

        // empty tree is always valid
        let root = match tree.root {
            Some(root) => root,
            None => return,
        };

        // Each item in queue represent a node pointer, and its upper/lower bound
        let mut queue = vec![(root, min_val, max_val)];

        // pop a queue item
        while let Some(queue_item) = queue.pop() {
            // unpack queue item
            let curr_ptr = queue_item.0;
            let min_val = queue_item.1;
            let max_val = queue_item.2;
            let curr_node = unsafe { curr_ptr.read() };

            // if min/max is present, validate node item is within bound
            match (min_val, max_val) {
                (None, None) => {}
                (None, Some(max)) => assert!(curr_node.item < max),
                (Some(min), None) => assert!(curr_node.item > min),
                (Some(min), Some(max)) => assert!(curr_node.item > min && curr_node.item < max),
            }

            // push left child node pointer to processing queue; left child's
            // upper bound is current node's item
            if let Some(left_ptr) = curr_node.left {
                queue.push((left_ptr, min_val, Some(curr_node.item)))
            }
            // push right child node pointer to processing queue; right child's
            // lower bound is current node's item
            if let Some(right_ptr) = curr_node.right {
                queue.push((right_ptr, Some(curr_node.item), max_val))
            }
        }
    }

    /// Validate red-black tree's property
    ///
    /// * `tree`: ref to red-black tree
    fn validate_rbt<T: Debug>(tree: &RedBlackTree<T>) {
        // unwrap root node pointer if tree is not empty
        let root_ptr = match tree.root {
            Some(root) => root,
            // empty tree is always valid
            None => return,
        };
        let root = unsafe { root_ptr.read() };

        // assert root node is black
        assert_eq!(root.color, Color::Black);

        let mut queue: Vec<NonNull<Node<T>>> = Vec::new();
        queue.push(root_ptr);

        // stores black node height for each node
        let mut black_node_heights: HashMap<NonNull<Node<T>>, usize> = HashMap::new();
        // stores unique black node heights for leaf nodes
        let mut leaf_black_node_heights: HashSet<usize> = HashSet::new();

        // pop and process queue item
        while let Some(curr_ptr) = queue.pop() {
            let curr_node = unsafe { curr_ptr.read() };

            // save black node height
            match curr_node.parent {
                Some(parent_ptr) => {
                    // check parent's black node height, if current node is black, increment
                    // height, then save current node's black node height
                    let parent_height = black_node_heights.get(&parent_ptr).unwrap();
                    let curr_height = match curr_node.color {
                        Color::Red => *parent_height,
                        Color::Black => *parent_height + 1,
                    };
                    assert!(black_node_heights.insert(curr_ptr, curr_height).is_none());
                }
                None => {
                    // root node is black so black node height is 1
                    assert!(black_node_heights.insert(curr_ptr, 1).is_none());
                }
            }

            // if current node has left child, push it to queue
            if let Some(left_ptr) = curr_node.left {
                // if current node is red, assert left child must be black
                if curr_node.color == Color::Red {
                    assert_eq!(unsafe { left_ptr.read() }.color, Color::Black);
                }
                queue.push(left_ptr);
            }
            // if current node has right child, push it to queue
            if let Some(right_ptr) = curr_node.right {
                // if current node is red, assert right child must be black
                if curr_node.color == Color::Red {
                    assert_eq!(unsafe { right_ptr.read() }.color, Color::Black);
                }
                queue.push(right_ptr);
            }

            // for leaf node, record black node heights in unique set
            if curr_node.left.is_none() && curr_node.right.is_none() {
                leaf_black_node_heights.insert(*black_node_heights.get(&curr_ptr).unwrap());
            }
        }

        // All leaf node's black node height should be identical,
        // so the unique set should have length of 1.
        assert_eq!(leaf_black_node_heights.len(), 1);
    }

    /// Validate red-black tree's traversal order
    ///
    /// * `tree`: ref to red-black tree
    /// * `expected_orders`: expected traversal order
    fn validate_order(tree: &RedBlackTree<i32>, expected_orders: &Value) {
        let order_types = vec![
            (TraversalOrder::Level, "level"),
            (TraversalOrder::In, "in"),
            (TraversalOrder::Pre, "pre"),
            (TraversalOrder::Post, "post"),
        ];
        // for each traversal order, iterate the tree and compare it with expected order
        for order_type in order_types {
            let actual_order: Vec<i32> = tree.iter(order_type.0).copied().collect();
            let expected_order: Vec<i32> = expected_orders[order_type.1]
                .as_array()
                .unwrap()
                .iter()
                .map(|i| i32::try_from(i.as_i64().unwrap()).unwrap())
                .collect();
            assert_eq!(actual_order, expected_order);
        }
    }

    /// Validate red-black tree's into-iterator traversal order
    ///
    /// * `tree_generator`: function that generates desired tree
    /// * `mirror`: mirror flag to be passed into tree generator
    /// * `expected_orders`: expected traversal order
    fn validate_into_order(
        tree_generator: fn(bool) -> RedBlackTree<i32>,
        mirror: bool,
        expected_orders: &Value,
    ) {
        let order_types = vec![
            (TraversalOrder::Level, "level"),
            (TraversalOrder::In, "in"),
            (TraversalOrder::Pre, "pre"),
            (TraversalOrder::Post, "post"),
        ];
        // for each traversal order, generate a tree, iterate the tree,
        // and compare it with the expected order
        for order_type in order_types {
            // generate tree
            let tree = tree_generator(mirror);
            let actual_order: Vec<i32> = tree.into_iter(order_type.0).collect();
            let expected_order: Vec<i32> = expected_orders[order_type.1]
                .as_array()
                .unwrap()
                .iter()
                .map(|i| i32::try_from(i.as_i64().unwrap()).unwrap())
                .collect();
            assert_eq!(actual_order, expected_order);
        }
    }

    fn read_json_data(filepath: &str) -> Value {
        let json_string =
            fs::read_to_string(path::Path::new(filepath)).expect("Unable to read file");
        serde_json::from_str(json_string.as_str()).unwrap()
    }

    #[test]
    fn test_new() {
        // new()
        let tree: RedBlackTree<i32> = RedBlackTree::new();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        validate_bst(&tree);
        validate_rbt(&tree);
        let tree: RedBlackTree<String> = RedBlackTree::new();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        // default()
        let tree: RedBlackTree<i32> = RedBlackTree::default();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        validate_bst(&tree);
        validate_rbt(&tree);
        let tree: RedBlackTree<String> = RedBlackTree::default();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
    }

    #[test]
    fn test_contains() {
        // right-tilted tree
        let tree: RedBlackTree<i32> = new_tilted_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }
        // left-tilted tree
        let tree: RedBlackTree<i32> = new_tilted_tree(true);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }

        // compact tree
        let tree: RedBlackTree<i32> = new_compact_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }
        // compact mirror tree
        let tree: RedBlackTree<i32> = new_compact_tree(true);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }

        // spread tree
        let tree: RedBlackTree<i32> = new_spread_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }
        // spread mirror tree
        let tree: RedBlackTree<i32> = new_spread_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }
    }

    #[test]
    fn test_insert_tilted() {
        let order_data = read_json_data("./unit_test_data/rbt_insert_orders.json");

        // right-tilted tree
        let expected_orders = &order_data["right_tilted"];
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        validate_bst(&tree);
        validate_rbt(&tree);
        for i in 1..=20 {
            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
        // right-tilted tree duplicate
        for i in 1..=20 {
            let err = tree.insert(i);
            assert_eq!(err, Err(DuplicateItemErr));
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[19]);
        }

        // left-tilted tree
        let expected_orders = &order_data["left_tilted"];
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        validate_bst(&tree);
        validate_rbt(&tree);
        for i in (1..=20).rev() {
            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
        // left-tilted tree duplicate
        for i in (1..=20).rev() {
            let err = tree.insert(i);
            assert_eq!(err, Err(DuplicateItemErr));
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[19]);
        }
    }

    #[test]
    fn test_insert_compact() {
        let order_data = read_json_data("./unit_test_data/rbt_insert_orders.json");

        // compact tree
        let expected_orders = &order_data["compact"];
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        validate_bst(&tree);
        validate_rbt(&tree);
        for i in 1..=10 {
            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(2 * i - 1).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(2 * i - 2).unwrap()]);

            let _ = tree.insert(21 - i);
            assert!(tree.contains(&(21 - i)));
            assert_eq!(tree.size(), usize::try_from(2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(2 * i - 1).unwrap()]);
        }
        // compact tree duplicate
        for i in 1..=20 {
            let err = tree.insert(i);
            assert_eq!(err, Err(DuplicateItemErr));
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[19]);
        }

        // compact mirror tree
        let expected_orders = &order_data["compact_mirror"];
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        validate_bst(&tree);
        validate_rbt(&tree);
        for i in 1..=10 {
            let _ = tree.insert(21 - i);
            assert!(tree.contains(&(21 - i)));
            assert_eq!(tree.size(), usize::try_from(2 * i - 1).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(2 * i - 2).unwrap()]);

            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(2 * i - 1).unwrap()]);
        }
        // compact tree duplicate
        for i in 1..=20 {
            let err = tree.insert(i);
            assert_eq!(err, Err(DuplicateItemErr));
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[19]);
        }
    }

    #[test]
    fn test_insert_spread() {
        let order_data = read_json_data("./unit_test_data/rbt_insert_orders.json");

        // spread tree
        let expected_orders = &order_data["spread"];
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        validate_bst(&tree);
        validate_rbt(&tree);
        for i in (1..=10).rev() {
            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - 2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(
                &tree,
                &expected_orders[usize::try_from(20 - 2 * i).unwrap()],
            );

            let _ = tree.insert(21 - i);
            assert!(tree.contains(&(21 - i)));
            assert_eq!(tree.size(), usize::try_from(22 - 2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(
                &tree,
                &expected_orders[usize::try_from(21 - 2 * i).unwrap()],
            );
        }
        // spread tree duplicate
        for i in 1..=20 {
            let err = tree.insert(i);
            assert_eq!(err, Err(DuplicateItemErr));
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[19]);
        }

        // spread mirror tree
        let expected_orders = &order_data["spread_mirror"];
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        validate_bst(&tree);
        validate_rbt(&tree);
        for i in (1..=10).rev() {
            let _ = tree.insert(21 - i);
            assert!(tree.contains(&(21 - i)));
            assert_eq!(tree.size(), usize::try_from(21 - 2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(
                &tree,
                &expected_orders[usize::try_from(20 - 2 * i).unwrap()],
            );

            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(22 - 2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(
                &tree,
                &expected_orders[usize::try_from(21 - 2 * i).unwrap()],
            );
        }
        // spread mirror tree duplicate
        for i in 1..=20 {
            let err = tree.insert(i);
            assert_eq!(err, Err(DuplicateItemErr));
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[19]);
        }
    }

    #[test]
    fn test_remove_single_item_tilted() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_single_orders.json");

        // right-tilted tree
        let expected_orders = &order_data["right_tilted"];
        for i in 1..=20 {
            let mut tree = new_tilted_tree(false);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 19);
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }

        // left-tilted tree
        let expected_orders = &order_data["left_tilted"];
        for i in 1..=20 {
            let mut tree = new_tilted_tree(true);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 19);
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_single_item_compact() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_single_orders.json");

        // compact tree
        let expected_orders = &order_data["compact"];
        for i in 1..=20 {
            let mut tree = new_compact_tree(false);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 19);
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }

        // compact mirror tree
        let expected_orders = &order_data["compact_mirror"];
        for i in 1..=20 {
            let mut tree = new_compact_tree(true);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 19);
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_single_item_spread() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_single_orders.json");

        // spread tree
        let expected_orders = &order_data["spread"];
        for i in 1..=20 {
            let mut tree = new_spread_tree(false);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 19);
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }

        // spread mirror tree
        let expected_orders = &order_data["spread_mirror"];
        for i in 1..=20 {
            let mut tree = new_spread_tree(true);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), 20);
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 19);
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_all_asc_order_tilted() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_asc_orders.json");

        // right-tilted tree
        let expected_orders = &order_data["right_tilted"];
        let mut tree = new_tilted_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }

        // left-tilted tree
        let expected_orders = &order_data["left_tilted"];
        let mut tree = new_tilted_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_all_asc_order_compact() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_asc_orders.json");

        // compact tree
        let expected_orders = &order_data["compact"];
        let mut tree = new_compact_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }

        // compact mirror tree
        let expected_orders = &order_data["compact_mirror"];
        let mut tree = new_compact_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_all_asc_order_spread() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_asc_orders.json");

        // spread tree
        let expected_orders = &order_data["spread"];
        let mut tree = new_spread_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }

        // spread mirror tree
        let expected_orders = &order_data["spread_mirror"];
        let mut tree = new_spread_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_all_desc_order_tilted() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_desc_orders.json");

        // right-tilted tree
        let expected_orders = &order_data["right_tilted"];
        let mut tree = new_tilted_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }

        // left-tilted tree
        let expected_orders = &order_data["left_tilted"];
        let mut tree = new_tilted_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
    }

    #[test]
    fn test_remove_all_desc_order_compact() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_desc_orders.json");

        // compact tree
        let expected_orders = &order_data["compact"];
        let mut tree = new_compact_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }

        // compact mirror tree
        let expected_orders = &order_data["compact_mirror"];
        let mut tree = new_compact_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
    }

    #[test]
    fn test_remove_all_desc_order_spread() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_desc_orders.json");

        // spread tree
        let expected_orders = &order_data["spread"];
        let mut tree = new_spread_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }

        // spread mirror tree
        let expected_orders = &order_data["spread_mirror"];
        let mut tree = new_spread_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
    }

    #[test]
    fn test_pop_min_tilted() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_asc_orders.json");

        // right-tilted tree
        let expected_orders = &order_data["right_tilted"];
        let mut tree = new_tilted_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.pop_min(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.pop_min(), None);

        // left-tilted tree
        let expected_orders = &order_data["left_tilted"];
        let mut tree = new_tilted_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.pop_min(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.pop_min(), None);
    }

    #[test]
    fn test_pop_min_compact() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_asc_orders.json");

        // compact tree
        let expected_orders = &order_data["compact"];
        let mut tree = new_compact_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.pop_min(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.pop_min(), None);

        // compact mirror tree
        let expected_orders = &order_data["compact_mirror"];
        let mut tree = new_compact_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.pop_min(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.pop_min(), None);
    }

    #[test]
    fn test_pop_min_spread() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_asc_orders.json");

        // spread tree
        let expected_orders = &order_data["spread"];
        let mut tree = new_spread_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.pop_min(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.pop_min(), None);

        // spread mirror tree
        let expected_orders = &order_data["spread_mirror"];
        let mut tree = new_spread_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.pop_min(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.pop_min(), None);
    }

    #[test]
    fn test_pop_max_tilted() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_desc_orders.json");

        // right-tilted tree
        let expected_orders = &order_data["right_tilted"];
        let mut tree = new_tilted_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);

        // left-tilted tree
        let expected_orders = &order_data["left_tilted"];
        let mut tree = new_tilted_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);
    }

    #[test]
    fn test_pop_max_compact() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_desc_orders.json");

        // compact tree
        let expected_orders = &order_data["compact"];
        let mut tree = new_compact_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);

        // compact mirror tree
        let expected_orders = &order_data["compact_mirror"];
        let mut tree = new_compact_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);
    }

    #[test]
    fn test_pop_max_spread() {
        let order_data = read_json_data("./unit_test_data/rbt_remove_all_desc_orders.json");

        // spread tree
        let expected_orders = &order_data["spread"];
        let mut tree = new_spread_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);

        // spread mirror tree
        let expected_orders = &order_data["spread_mirror"];
        let mut tree = new_spread_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            assert_eq!(tree.remove(&i), None);
            validate_bst(&tree);
            validate_rbt(&tree);
            validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
        }
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);
    }

    #[test]
    fn test_into_iter_tilted() {
        let order_data = read_json_data("./unit_test_data/rbt_insert_orders.json");

        // right-tilted tree
        let expected_orders = &order_data["right_tilted"];
        validate_into_order(new_tilted_tree, false, &expected_orders[19]);

        // left-tilted tree
        let expected_orders = &order_data["left_tilted"];
        validate_into_order(new_tilted_tree, true, &expected_orders[19]);
    }

    #[test]
    fn test_into_iter_compact() {
        let order_data = read_json_data("./unit_test_data/rbt_insert_orders.json");

        // compact tree
        let expected_orders = &order_data["compact"];
        validate_into_order(new_compact_tree, false, &expected_orders[19]);

        // compact-mirror tree
        let expected_orders = &order_data["compact_mirror"];
        validate_into_order(new_compact_tree, true, &expected_orders[19]);
    }

    #[test]
    fn test_into_iter_spread() {
        let order_data = read_json_data("./unit_test_data/rbt_insert_orders.json");

        // compact tree
        let expected_orders = &order_data["spread"];
        validate_into_order(new_spread_tree, false, &expected_orders[19]);

        // compact-mirror tree
        let expected_orders = &order_data["spread_mirror"];
        validate_into_order(new_spread_tree, true, &expected_orders[19]);
    }

    #[test]
    fn test_into_iter_partial_consume() {
        // partial consumption of the tree with into_iter in all traversal orders
        // to ensure tree moved into iterator is dropped correctly without memory leaks
        for order in [
            TraversalOrder::Level,
            TraversalOrder::Pre,
            TraversalOrder::In,
            TraversalOrder::Post,
        ] {
            let tree = new_tilted_tree(false);
            let mut iter = tree.into_iter(order);
            for _i in 1..=10 {
                iter.next();
            }
        }
    }
}
