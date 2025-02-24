//! Binary search tree implementation

use std::{cmp::Ordering, collections::VecDeque, fmt::Debug, mem};

pub enum Order {
    Level,
    Pre,
    In,
    Post,
}

#[derive(Debug)]
pub struct BinarySearchTree<T>
where
    T: Ord + Debug,
{
    head: Link<T>,
    size: usize,
}

#[derive(Debug)]
struct Link<T>(Option<Box<Node<T>>>);

#[derive(Debug)]
struct Node<T> {
    item: T,
    left: Link<T>,
    right: Link<T>,
}

impl<T> Node<T> {
    /// Create new node populated with item but no child links.
    ///
    /// * `item`: item in node
    fn new_boxed(item: T) -> Box<Node<T>> {
        Box::new(Node {
            item,
            left: Link(None),
            right: Link(None),
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct DuplicateItem;

impl<T: Ord + Debug> Link<T> {
    /// Pop max node from sub-tree which link is pointing to
    fn pop_max(&mut self) -> Option<T> {
        // if link does not point to some node, return
        // else, points current link to self
        let mut curr = match self.0.as_mut() {
            Some(_) => self,
            None => {
                return None;
            }
        };

        // while current link's right child also points to some node, traverse right
        while curr.0.as_ref().unwrap().right.0.is_some() {
            curr = &mut curr.0.as_mut().unwrap().right;
        }

        // take the node current link points to
        let node = curr.0.take().unwrap();
        // set current link to point to taken node's left child
        curr.0 = node.left.0;
        // return item in the taken node
        Some(node.item)
    }

    /// Pop min node from sub-tree which link is pointing to
    fn pop_min(&mut self) -> Option<T> {
        // if link does not point to some node, return
        // else, points current link to self
        let mut curr = match self.0.as_mut() {
            Some(_) => self,
            None => {
                return None;
            }
        };

        // while current link's left child also points to some node, traverse left
        while curr.0.as_ref().unwrap().left.0.is_some() {
            curr = &mut curr.0.as_mut().unwrap().left;
        }

        // take the node current link points to
        let node = curr.0.take().unwrap();
        // set current link to point to taken node's right child
        curr.0 = node.right.0;
        // return item in the taken node
        Some(node.item)
    }
}

impl<T: Ord + Debug> BinarySearchTree<T> {
    /// Creates new binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert_eq!(tree.size(), 0);
    /// assert!(tree.is_empty());
    /// ```
    pub fn new() -> BinarySearchTree<T> {
        BinarySearchTree {
            head: Link(None),
            size: 0,
        }
    }

    /// Get number of nodes in binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert_eq!(tree.size(), 0);
    /// tree.insert(5);
    /// assert_eq!(tree.size(), 1);
    /// tree.remove(&5);
    /// assert_eq!(tree.size(), 0);
    /// ```
    pub fn size(&self) -> usize {
        self.size
    }

    /// Get whether binary search tree is empty
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert!(tree.is_empty());
    /// tree.insert(5);
    /// assert!(!tree.is_empty());
    /// tree.remove(&5);
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Insert item to binary search tree
    ///
    /// * `item`: item to insert
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::{BinarySearchTree, DuplicateItem};
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert!(!tree.contains(&5));
    /// assert_eq!(tree.insert(5), Ok(()));
    /// assert!(tree.contains(&5));
    /// assert_eq!(tree.insert(5), Err(DuplicateItem));
    /// ```
    pub fn insert(&mut self, item: T) -> Result<(), DuplicateItem> {
        // if tree is empty (head points to None),
        // assign head to new node, else, assign
        // head to current node
        let mut curr = match self.head.0.as_mut() {
            Some(head) => head,
            None => {
                self.size += 1;
                self.head = Link(Some(Node::new_boxed(item)));
                return Ok(());
            }
        };

        // traverse to leaf node and insert new node
        loop {
            // compare current node item to new item
            // - if new item is smaller, store left child
            // - if new item is larger, store right child
            // - if equal, return error as duplicate item is not allowed
            let child = match item.cmp(&curr.item) {
                Ordering::Less => &mut curr.left.0,
                Ordering::Greater => &mut curr.right.0,
                Ordering::Equal => return Err(DuplicateItem),
            };

            if let Some(child) = child {
                curr = child;
            } else {
                // if child is none, leaf node reached, insert new node
                self.size += 1;
                *child = Some(Node::new_boxed(item));
                return Ok(());
            }
        }
    }

    /// Remove item from binary search tree
    ///
    /// * `item`: reference to item to remove
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(5);
    /// assert!(tree.contains(&5));
    /// tree.remove(&5);
    /// assert!(!tree.contains(&5));
    /// ```
    pub fn remove(&mut self, item: &T) -> Option<T> {
        // if tree is empty (head points to None), return None
        // else, assign head as current link
        let mut curr = match self.head.0.as_mut() {
            Some(_head) => &mut self.head,
            None => {
                return None;
            }
        };

        // to remove item, find the node with same item.
        loop {
            // if current link points to None, item does not exist in tree, return None
            curr.0.as_ref()?;
            match curr.0.as_ref().unwrap().item.cmp(item) {
                Ordering::Less => curr = &mut curr.0.as_mut().unwrap().right,
                Ordering::Greater => curr = &mut curr.0.as_mut().unwrap().left,
                Ordering::Equal => {
                    self.size -= 1;
                    let curr_node = curr.0.as_mut().unwrap();

                    // match current node's left and right child
                    // - if node has no child node, remove node
                    // - if node has 1 child node, remove node and assign child node to current node
                    // - if node has 2 child node, replace node with poppped min node from the right
                    // child's sub tree
                    return match (curr_node.left.0.as_ref(), curr_node.right.0.as_ref()) {
                        (None, None) => Some(curr.0.take().unwrap().item),
                        (Some(_), None) => {
                            let left = curr_node.left.0.take();
                            let removed_item = mem::replace(&mut curr.0, left).unwrap().item;
                            Some(removed_item)
                        }
                        (None, Some(_)) => {
                            let right = curr_node.right.0.take();
                            let removed_item = mem::replace(&mut curr.0, right).unwrap().item;
                            Some(removed_item)
                        }
                        (Some(_), Some(_)) => {
                            let right_tree_min = curr_node.right.pop_min().unwrap();
                            return Some(mem::replace(&mut curr_node.item, right_tree_min));
                        }
                    };
                }
            }
        }
    }

    /// Check if binary search tree contains item
    ///
    /// * `item`: item to check
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// assert!(!tree.contains(&5));
    /// tree.insert(5);
    /// assert!(tree.contains(&5));
    /// assert_eq!(tree.remove(&5), Some(5));
    /// assert!(!tree.contains(&5));
    /// assert_eq!(tree.remove(&5), None);
    /// ```
    pub fn contains(&self, item: &T) -> bool {
        // if tree is empty (head points to None), return None
        // else, assign head as current link
        let mut curr = match self.head.0.as_ref() {
            Some(head) => Some(head),
            None => {
                return false;
            }
        };

        // traverse tree until item found, or leaf node reached
        while let Some(node) = curr {
            match node.item.cmp(item) {
                Ordering::Greater => curr = node.left.0.as_ref(),
                Ordering::Less => curr = node.right.0.as_ref(),
                Ordering::Equal => return true,
            }
        }

        // no item is found, return false
        false
    }

    /// Get min item in binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(10);
    /// tree.insert(5);
    /// assert_eq!(tree.min(), Some(&5));
    /// tree.pop_min();
    /// assert_eq!(tree.min(), Some(&10));
    /// tree.pop_min();
    /// assert_eq!(tree.min(), None);
    /// ```
    pub fn min(&self) -> Option<&T> {
        // if tree is empty (head points to None), return None
        // else, traverse left repeatedly and return leaf item
        let mut curr = self.head.0.as_ref()?;
        while let Some(left) = curr.left.0.as_ref() {
            curr = left;
        }
        Some(&curr.item)
    }

    /// Get max item in binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(10);
    /// tree.insert(5);
    /// assert_eq!(tree.max(), Some(&10));
    /// tree.pop_max();
    /// assert_eq!(tree.max(), Some(&5));
    /// tree.pop_max();
    /// assert_eq!(tree.max(), None);
    /// ```
    pub fn max(&self) -> Option<&T> {
        // if tree is empty (head points to None), return None
        // else, traverse right repeatedly and return leaf item
        let mut curr = self.head.0.as_ref()?;
        while let Some(right) = curr.right.0.as_ref() {
            curr = right;
        }
        Some(&curr.item)
    }

    /// Pop min item in binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(10);
    /// tree.insert(5);
    /// assert_eq!(tree.pop_min(), Some(5));
    /// assert_eq!(tree.pop_min(), Some(10));
    /// assert_eq!(tree.pop_min(), None);
    /// ```
    pub fn pop_min(&mut self) -> Option<T> {
        // pop min node in head link, decrement size if node is popped
        self.head.pop_min().inspect(|_| {
            self.size -= 1;
        })
    }

    /// Pop max item in binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// tree.insert(10);
    /// tree.insert(5);
    /// assert_eq!(tree.pop_max(), Some(10));
    /// assert_eq!(tree.pop_max(), Some(5));
    /// assert_eq!(tree.pop_max(), None);
    /// ```
    pub fn pop_max(&mut self) -> Option<T> {
        // pop max node in head link, decrement size if node is popped
        self.head.pop_max().inspect(|_| {
            self.size -= 1;
        })
    }

    /// Create iterator for binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// /* Shape
    ///  *    3
    ///  *  2   5
    ///  * 1   4
    ///  */
    /// use dsa::binary_search_tree::{BinarySearchTree, Order};
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    ///
    /// let mut iter = tree.iter(Order::In);
    /// for i in 1..=5 {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut iter = tree.iter(Order::Pre);
    /// for i in [3, 2, 1, 5, 4] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut iter = tree.iter(Order::Post);
    /// for i in [1, 2, 4, 5, 3] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut iter = tree.iter(Order::Level);
    /// for i in [3, 2, 5, 1, 4] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self, order: Order) -> Iter<T> {
        Iter {
            curr: self.head.0.as_deref(),
            nodes: VecDeque::new(),
            order,
        }
    }

    /// Iterate into binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// /* Shape
    ///  *    3
    ///  *  2   5
    ///  * 1   4
    ///  */
    /// use dsa::binary_search_tree::{BinarySearchTree, Order};
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.into_iter(Order::In);
    /// for i in 1..=5 {
    ///     assert_eq!(iter.next(), Some(i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.into_iter(Order::Pre);
    /// for i in [3, 2, 1, 5, 4] {
    ///     assert_eq!(iter.next(), Some(i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.into_iter(Order::Post);
    /// for i in [1, 2, 4, 5, 3] {
    ///     assert_eq!(iter.next(), Some(i));
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
    /// for i in [3, 2, 1, 5, 4] {
    ///     tree.insert(i);
    /// }
    /// let mut iter = tree.into_iter(Order::Level);
    /// for i in [3, 2, 5, 1, 4] {
    ///     assert_eq!(iter.next(), Some(i));
    /// }
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn into_iter(mut self, order: Order) -> IntoIter<T> {
        IntoIter {
            curr: self.head.0.take().map(|node| *node),
            nodes: VecDeque::new(),
            post_nodes: VecDeque::new(),
            order,
        }
    }
}

impl<T: Ord + Debug> Default for BinarySearchTree<T> {
    /// Creates new binary search tree
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_search_tree::BinarySearchTree;
    /// let tree: BinarySearchTree<i32> = BinarySearchTree::default();
    /// assert_eq!(tree.size(), 0);
    /// assert!(tree.is_empty());
    /// ```
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, T> {
    curr: Option<&'a Node<T>>,
    nodes: VecDeque<&'a Node<T>>,
    order: Order,
}

impl<'a, T> Iterator for Iter<'a, T>
where
    T: PartialEq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.order {
            Order::Level => self.level_order_next(),
            Order::Pre => self.pre_order_next(),
            Order::In => self.in_order_next(),
            Order::Post => self.post_order_next(),
        }
    }
}

impl<'a, T> Iter<'a, T>
where
    T: PartialEq,
{
    fn level_order_next(&mut self) -> Option<&'a T> {
        // self.nodes is a queue in this iterator
        // if current node is Some:
        // - push node's left and right child to queue if exists
        // - pop a new node from queue and assign it to current node
        // - return old current node's item
        self.curr.map(|node| {
            let item = &node.item;
            if let Some(left) = node.left.0.as_deref() {
                self.nodes.push_front(left);
            }
            if let Some(right) = node.right.0.as_deref() {
                self.nodes.push_front(right);
            }
            self.curr = self.nodes.pop_back();
            item
        })
    }

    fn pre_order_next(&mut self) -> Option<&'a T> {
        // self.nodes is a stack in this iterator
        // if current node is Some:
        // - push node's left and right child to stack if exists
        // - pop a new node from stack and assign it to current node
        // - return old current node's item
        self.curr.map(|node| {
            let item = &node.item;
            if let Some(right) = node.right.0.as_deref() {
                self.nodes.push_front(right);
            }
            if let Some(left) = node.left.0.as_deref() {
                self.nodes.push_front(left);
            }
            self.curr = self.nodes.pop_front();
            item
        })
    }

    fn in_order_next(&mut self) -> Option<&'a T> {
        // self.nodes is a stack in this iterator
        // if curr is assigned Some:
        // - store node in stack
        // - traverse left
        while let Some(curr) = self.curr {
            self.nodes.push_front(curr);
            self.curr = curr.left.0.as_deref();
        }

        // pop a node from stack, if Some:
        // - set node's right child to curr for left traversal in next call
        // - return node item
        self.nodes.pop_front().map(|node| {
            self.curr = node.right.0.as_deref();
            &node.item
        })
    }

    fn post_order_next(&mut self) -> Option<&'a T> {
        // self.nodes is a stack in this iterator
        // In post-order traversal, each nodes's item must be returned after
        // item's right subtree has been processed.
        // To signal that a node's right subtree is not processed, we use stack
        // push order, by pushing right child before parent node, which results
        // in parent node being popped before right right child.
        loop {
            // if curr is Some:
            // - traverse left
            // - for each node:
            //   - store right child if exist
            //   - store current node
            while let Some(curr) = self.curr {
                if let Some(right) = curr.right.0.as_deref() {
                    self.nodes.push_front(right);
                }
                self.nodes.push_front(curr);
                self.curr = curr.left.0.as_deref();
            }

            // pop a node from stack
            if let Some(front) = self.nodes.pop_front() {
                // if next node from stack is right child of popped node,
                // the right child has not been processed.
                // - pop the right child off stack and assign it to curr
                // - re-push front (the parent node) and continue this loop iteration,
                // and the traversal loop above can process right child node
                if let Some(front_right) = front.right.0.as_ref() {
                    if let Some(second_front) = self.nodes.front() {
                        if front_right.item == second_front.item {
                            self.curr = self.nodes.pop_front();
                            self.nodes.push_front(front);
                            continue;
                        }
                    }
                }
                // return popped node item normally
                return Some(&front.item);
            } else {
                // if stack is empty return None
                return None;
            }
        }
    }
}

pub struct IntoIter<T> {
    curr: Option<Node<T>>,
    nodes: VecDeque<Node<T>>,
    // post-order iterator uses post_nodes
    // within a VecDeque item, the first tuple parameter stores
    // the node, and seocnd parameter stores unprocessed right child
    post_nodes: VecDeque<(Node<T>, Option<Node<T>>)>,
    order: Order,
}

impl<T> Iterator for IntoIter<T>
where
    T: PartialEq,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.order {
            Order::Level => self.level_order_next(),
            Order::Pre => self.pre_order_next(),
            Order::In => self.in_order_next(),
            Order::Post => self.post_order_next(),
        }
    }
}

impl<T> IntoIter<T>
where
    T: PartialEq,
{
    fn level_order_next(&mut self) -> Option<T> {
        // self.nodes is a queue in this iterator
        // if current node is Some:
        // - destructure node
        // - push node's left and right child to queue if exists
        // - pop a new node from queue and assign it to current node
        // - return old current node's item
        self.curr.take().map(|node| {
            let Node { left, right, item } = node;
            if let Some(left) = left.0 {
                self.nodes.push_front(*left);
            }
            if let Some(right) = right.0 {
                self.nodes.push_front(*right);
            }
            self.curr = self.nodes.pop_back();
            item
        })
    }

    fn pre_order_next(&mut self) -> Option<T> {
        // self.nodes is a stack in this iterator
        // if current node is Some:
        // - destructure node
        // - push node's left and right child to stack if exists
        // - pop a new node from stack and assign it to current node
        // - return old current node's item
        self.curr.take().map(|node| {
            let Node { left, right, item } = node;
            if let Some(right) = right.0 {
                self.nodes.push_front(*right);
            }
            if let Some(left) = left.0 {
                self.nodes.push_front(*left);
            }
            self.curr = self.nodes.pop_front();
            item
        })
    }

    fn in_order_next(&mut self) -> Option<T> {
        // self.nodes is a stack in this iterator
        // if curr is assigned Some:
        // - unlink left child
        // - store node in stack
        // - traverse left
        while let Some(mut curr) = self.curr.take() {
            let left = curr.left.0.take();
            self.nodes.push_front(curr);
            self.curr = left.map(|node| *node);
        }

        // pop a node from stack, if Some:
        // - set node's right child to curr for left traversal in next call
        // - return node item
        self.nodes.pop_front().map(|node| {
            self.curr = node.right.0.map(|node| *node);
            node.item
        })
    }

    fn post_order_next(&mut self) -> Option<T> {
        // self.nodes is a stack in this iterator
        // within a VecDeque item, the first tuple parameter stores
        // the node, and seocnd parameter stores unprocessed right child
        loop {
            // if curr is assigned Some:
            // - traverse and unlink left child,
            // - if right child exists, push curr and right child into post_nodes
            // - else, just push curr into post_nodes
            while let Some(mut curr) = self.curr.take() {
                self.curr = curr.left.0.take().map(|node| *node);
                let stack_item = if let Some(right) = curr.right.0.take() {
                    (curr, Some(*right))
                } else {
                    (curr, None)
                };
                self.post_nodes.push_front(stack_item);
            }

            // pop a stack item from stack
            if let Some(mut front) = self.post_nodes.pop_front() {
                // if item includes unprocessed right child
                // - take the right child and set it to curr
                // - re-push node to stack without right child
                // - continue this iteration so that right child can be
                // processed by traversal loop above
                if let Some(right) = front.1.take() {
                    self.curr = Some(right);
                    self.post_nodes.push_front(front);
                    continue;
                }

                // return popped node item normally
                return Some(front.0.item);
            } else {
                // if stack is empty return None
                return None;
            }
        }
    }
}

impl<T> Drop for BinarySearchTree<T>
where
    T: Ord + Debug,
{
    fn drop(&mut self) {
        // walk the tree in in-order iteration
        let mut nodes: Vec<Box<Node<T>>> = Vec::new();
        if let Some(node) = self.head.0.take() {
            nodes.push(node);
        } else {
            return;
        }
        while let Some(node) = nodes.pop() {
            if let Some(left) = node.left.0 {
                nodes.push(left);
            }
            if let Some(right) = node.right.0 {
                nodes.push(right);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_flat_tree_items() -> Vec<i32> {
        /* Shape
         *            8
         *         /     \
         *       4        12
         *    /    \    /    \
         *   2     6    10    14
         *  / \   / \  / \   / \
         * 1  3  5  7  9 11 13 15
         */
        vec![8, 4, 2, 1, 3, 6, 5, 7, 12, 10, 9, 11, 14, 13, 15]
    }

    fn get_jagged_tree_items() -> Vec<i32> {
        /* Shape
         *              8
         *           /     \
         *         4        12
         *      /     \   /     \
         *     2      7  9        15
         *    / \    /    \      / \
         *   1  3   6     10    14 16
         *  /      /       \    /
         * 0      5        11 13
         */
        vec![8, 4, 2, 1, 0, 3, 7, 6, 5, 12, 9, 10, 11, 15, 14, 13, 16]
    }

    fn new_flat_tree() -> BinarySearchTree<i32> {
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        let items = get_flat_tree_items();
        for item in items {
            tree.insert(item).unwrap();
        }
        tree
    }

    fn new_jagged_tree() -> BinarySearchTree<i32> {
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        let items = get_jagged_tree_items();
        for item in items {
            tree.insert(item).unwrap();
        }
        tree
    }

    fn new_left_only_tree() -> BinarySearchTree<i32> {
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        for i in (1..=20).rev() {
            tree.insert(i).unwrap();
        }
        tree
    }

    fn new_right_only_tree() -> BinarySearchTree<i32> {
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        for i in 1..=25 {
            tree.insert(i).unwrap();
        }
        tree
    }

    #[test]
    fn test_new() {
        // new()
        let tree: BinarySearchTree<i32> = BinarySearchTree::new();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        let tree: BinarySearchTree<String> = BinarySearchTree::new();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        // default()
        let tree: BinarySearchTree<i32> = BinarySearchTree::default();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
        let tree: BinarySearchTree<String> = BinarySearchTree::default();
        assert_eq!(tree.size(), 0);
        assert!(tree.is_empty());
    }

    #[test]
    fn test_contains() {
        // flat tree contains
        let tree = new_flat_tree();
        for i in -5..=30 {
            if (1..=15).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            };
        }
        // jagged tree contains
        let tree = new_jagged_tree();
        for i in -5..=30 {
            if (0..=16).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            };
        }
        // left-only tree contains
        let tree = new_left_only_tree();
        for i in -5..=30 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            };
        }
        // right tree contains
        let tree = new_right_only_tree();
        for i in -5..=30 {
            if (1..=25).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            };
        }
    }

    #[test]
    fn test_insert() {
        // flat tree insert
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        for (index, item) in get_flat_tree_items().iter().enumerate() {
            tree.insert(*item).unwrap();
            assert!(tree.contains(item));
            assert_eq!(tree.size(), index + 1);
            assert!(!tree.is_empty());
        }
        // flat tree insert duplicate
        for item in get_flat_tree_items() {
            let err = tree.insert(item);
            assert_eq!(err, Err(DuplicateItem));
            assert!(tree.contains(&item));
            assert_eq!(tree.size(), 15);
            assert!(!tree.is_empty());
        }

        // jagged tree insert
        let mut tree: BinarySearchTree<i32> = BinarySearchTree::new();
        for (index, item) in get_flat_tree_items().iter().enumerate() {
            tree.insert(*item).unwrap();
            assert!(tree.contains(item));
            assert_eq!(tree.size(), index + 1);
            assert!(!tree.is_empty());
        }
        // jagged tree insert duplicate
        for item in get_flat_tree_items() {
            let err = tree.insert(item);
            assert_eq!(err, Err(DuplicateItem));
            assert!(tree.contains(&item));
            assert_eq!(tree.size(), 15);
            assert!(!tree.is_empty());
        }
    }

    #[test]
    fn test_remove() {
        // flat tree remove in order
        let mut tree = new_flat_tree();
        for i in -5..=0 {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 15);
            assert!(!tree.is_empty());
        }
        for i in 1..=15 {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), (15 - i).try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());
        for i in 16..=20 {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 0);
            assert!(tree.is_empty());
        }
        // flat tree remove in reverse order
        let mut tree = new_flat_tree();
        for i in (16..=20).rev() {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 15);
            assert!(!tree.is_empty());
        }
        for i in (1..=15).rev() {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), (i - 1).try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());
        for i in (-5..=0).rev() {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 0);
            assert!(tree.is_empty());
        }
        // flat tree remove in insert order
        let mut tree = new_flat_tree();
        for (index, item) in get_flat_tree_items().iter().enumerate() {
            assert!(!tree.is_empty());
            assert!(tree.contains(item));
            assert_eq!(tree.remove(item), Some(*item));
            assert_eq!(tree.size(), 14 - index);
            assert!(!tree.contains(item));
        }
        assert!(tree.is_empty());

        // jagged tree remove in order
        let mut tree = new_jagged_tree();
        for i in -5..=-1 {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 17);
            assert!(!tree.is_empty());
        }
        for i in 0..=16 {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), (16 - i).try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());
        for i in 17..=20 {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 0);
            assert!(tree.is_empty());
        }
        // jagged tree remove in reverse order
        let mut tree = new_jagged_tree();
        for i in (17..=20).rev() {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 17);
            assert!(!tree.is_empty());
        }
        for i in (0..=16).rev() {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), i.try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());
        for i in (-5..=-1).rev() {
            assert!(!tree.contains(&i));
            assert_eq!(tree.remove(&i), None);
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), 0);
            assert!(tree.is_empty());
        }
        // jagged tree remove in insert order
        let mut tree = new_jagged_tree();
        for (index, item) in get_jagged_tree_items().iter().enumerate() {
            assert!(!tree.is_empty());
            assert!(tree.contains(item));
            assert_eq!(tree.remove(item), Some(*item));
            assert_eq!(tree.size(), 16 - index);
            assert!(!tree.contains(item));
        }
        assert!(tree.is_empty());

        // left-only tree remove in order
        let mut tree = new_left_only_tree();
        for i in 1..=20 {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), (20 - i).try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());
        // left-only tree remove in reverse order
        let mut tree = new_left_only_tree();
        for i in (1..=20).rev() {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), (i - 1).try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());

        // right-only tree remove in order
        let mut tree = new_right_only_tree();
        for i in 1..=25 {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), (25 - i).try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());
        // right-only tree remove in reverse order
        let mut tree = new_right_only_tree();
        for i in (1..=25).rev() {
            assert!(!tree.is_empty());
            assert!(tree.contains(&i));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.remove(&i), Some(i));
            assert_eq!(tree.size(), (i - 1).try_into().unwrap());
            assert!(!tree.contains(&i));
        }
        assert!(tree.is_empty());
    }

    #[test]
    fn test_pop_min() {
        // flat tree
        let mut tree = new_flat_tree();
        for i in 1..=15 {
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.max(), Some(&15));
            assert_eq!(tree.pop_min(), Some(i));
            assert_eq!(tree.size(), (15 - i).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_min(), None);

        // jagged tree
        let mut tree = new_jagged_tree();
        for i in 0..=16 {
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.max(), Some(&16));
            assert_eq!(tree.pop_min(), Some(i));
            assert_eq!(tree.size(), (16 - i).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_min(), None);

        // left-only tree
        let mut tree = new_left_only_tree();
        for i in 1..=20 {
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.max(), Some(&20));
            assert_eq!(tree.pop_min(), Some(i));
            assert_eq!(tree.size(), (20 - i).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_min(), None);

        // right-only tree
        let mut tree = new_right_only_tree();
        for i in 1..=25 {
            assert_eq!(tree.min(), Some(&i));
            assert_eq!(tree.max(), Some(&25));
            assert_eq!(tree.pop_min(), Some(i));
            assert_eq!(tree.size(), (25 - i).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_min(), None);
    }

    #[test]
    fn test_pop_max() {
        // flat tree
        let mut tree = new_flat_tree();
        for i in (1..=15).rev() {
            assert_eq!(tree.min(), Some(&1));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert_eq!(tree.size(), (i - 1).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);

        // jagged tree
        let mut tree = new_jagged_tree();
        for i in (0..=16).rev() {
            assert_eq!(tree.min(), Some(&0));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert_eq!(tree.size(), (i).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);

        // left-only tree
        let mut tree = new_left_only_tree();
        for i in (1..=20).rev() {
            assert_eq!(tree.min(), Some(&1));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert_eq!(tree.size(), (i - 1).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);

        // right-only tree
        let mut tree = new_right_only_tree();
        for i in (1..=25).rev() {
            assert_eq!(tree.min(), Some(&1));
            assert_eq!(tree.max(), Some(&i));
            assert_eq!(tree.pop_max(), Some(i));
            assert_eq!(tree.size(), (i - 1).try_into().unwrap())
        }
        assert_eq!(tree.min(), None);
        assert_eq!(tree.max(), None);
        assert_eq!(tree.pop_max(), None);
    }

    #[test]
    fn test_iter() {
        // flat tree
        let tree = new_flat_tree();
        let mut iter = tree.iter(Order::In);
        for i in 1..=15 {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        let mut iter = tree.iter(Order::Pre);
        for i in [8, 4, 2, 1, 3, 6, 5, 7, 12, 10, 9, 11, 14, 13, 15] {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        let mut iter = tree.iter(Order::Post);
        for i in [1, 3, 2, 5, 7, 6, 4, 9, 11, 10, 13, 15, 14, 12, 8] {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        let mut iter = tree.iter(Order::Level);
        for i in [8, 4, 12, 2, 6, 10, 14, 1, 3, 5, 7, 9, 11, 13, 15] {
            assert_eq!(iter.next(), Some(&i));
        }

        /* Shape
         *              8
         *           /     \
         *         4        12
         *      /     \   /     \
         *     2      7  9        15
         *    / \    /    \      / \
         *   1  3   6     10    14 16
         *  /      /       \    /
         * 0      5        11 13
         */
        // jagged tree
        let tree = new_jagged_tree();
        let mut iter = tree.iter(Order::In);
        for i in 0..=16 {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        let mut iter = tree.iter(Order::Pre);
        for i in [8, 4, 2, 1, 0, 3, 7, 6, 5, 12, 9, 10, 11, 15, 14, 13, 16] {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Post);
        for i in [0, 1, 3, 2, 5, 6, 7, 4, 11, 10, 9, 13, 14, 16, 15, 12, 8] {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Level);
        for i in [8, 4, 12, 2, 7, 9, 15, 1, 3, 6, 10, 14, 16, 0, 5, 11, 13] {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        // left-only tree
        let tree = new_left_only_tree();
        let mut iter = tree.iter(Order::In);
        for i in 1..=20 {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Pre);
        for i in (1..=20).rev() {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Post);
        for i in 1..=20 {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Level);
        for i in (1..=20).rev() {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);

        // right-only tree
        let tree = new_right_only_tree();
        let mut iter = tree.iter(Order::In);
        for i in 1..=25 {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Pre);
        for i in 1..=25 {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Post);
        for i in (1..=25).rev() {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);
        let mut iter = tree.iter(Order::Level);
        for i in 1..=25 {
            assert_eq!(iter.next(), Some(&i))
        }
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_into_iter() {
        // flat tree
        let tree = new_flat_tree();
        let mut iter = tree.into_iter(Order::In);
        for i in 1..=15 {
            assert_eq!(iter.next(), Some(i));
        }
        assert_eq!(iter.next(), None);

        let tree = new_flat_tree();
        let mut iter = tree.into_iter(Order::Pre);
        for i in [8, 4, 2, 1, 3, 6, 5, 7, 12, 10, 9, 11, 14, 13, 15] {
            assert_eq!(iter.next(), Some(i));
        }
        assert_eq!(iter.next(), None);

        let tree = new_flat_tree();
        let mut iter = tree.into_iter(Order::Post);
        for i in [1, 3, 2, 5, 7, 6, 4, 9, 11, 10, 13, 15, 14, 12, 8] {
            assert_eq!(iter.next(), Some(i));
        }
        assert_eq!(iter.next(), None);

        let tree = new_flat_tree();
        let mut iter = tree.into_iter(Order::Level);
        for i in [8, 4, 12, 2, 6, 10, 14, 1, 3, 5, 7, 9, 11, 13, 15] {
            assert_eq!(iter.next(), Some(i));
        }

        /* Shape
         *              8
         *           /     \
         *         4        12
         *      /     \   /     \
         *     2      7  9        15
         *    / \    /    \      / \
         *   1  3   6     10    14 16
         *  /      /       \    /
         * 0      5        11 13
         */
        // jagged tree
        let tree = new_jagged_tree();
        let mut iter = tree.into_iter(Order::In);
        for i in 0..=16 {
            assert_eq!(iter.next(), Some(i));
        }
        assert_eq!(iter.next(), None);
        let tree = new_jagged_tree();
        let mut iter = tree.into_iter(Order::Pre);
        for i in [8, 4, 2, 1, 0, 3, 7, 6, 5, 12, 9, 10, 11, 15, 14, 13, 16] {
            assert_eq!(iter.next(), Some(i));
        }
        assert_eq!(iter.next(), None);
        let tree = new_jagged_tree();
        let mut iter = tree.into_iter(Order::Post);
        for i in [0, 1, 3, 2, 5, 6, 7, 4, 11, 10, 9, 13, 14, 16, 15, 12, 8] {
            assert_eq!(iter.next(), Some(i));
        }
        assert_eq!(iter.next(), None);
        let tree = new_jagged_tree();
        let mut iter = tree.into_iter(Order::Level);
        for i in [8, 4, 12, 2, 7, 9, 15, 1, 3, 6, 10, 14, 16, 0, 5, 11, 13] {
            assert_eq!(iter.next(), Some(i));
        }
        assert_eq!(iter.next(), None);

        // left-only tree
        let tree = new_left_only_tree();
        let mut iter = tree.into_iter(Order::In);
        for i in 1..=20 {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);
        let tree = new_left_only_tree();
        let mut iter = tree.into_iter(Order::Pre);
        for i in (1..=20).rev() {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);
        let tree = new_left_only_tree();
        let mut iter = tree.into_iter(Order::Post);
        for i in 1..=20 {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);
        let tree = new_left_only_tree();
        let mut iter = tree.into_iter(Order::Level);
        for i in (1..=20).rev() {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);

        // right-only tree
        let tree = new_right_only_tree();
        let mut iter = tree.into_iter(Order::In);
        for i in 1..=25 {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);
        let tree = new_right_only_tree();
        let mut iter = tree.into_iter(Order::Pre);
        for i in 1..=25 {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);
        let tree = new_right_only_tree();
        let mut iter = tree.into_iter(Order::Post);
        for i in (1..=25).rev() {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);
        let tree = new_right_only_tree();
        let mut iter = tree.into_iter(Order::Level);
        for i in 1..=25 {
            assert_eq!(iter.next(), Some(i))
        }
        assert_eq!(iter.next(), None);
    }
}
