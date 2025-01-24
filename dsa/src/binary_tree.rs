//! Binary tree implementation

use std::{cmp::Ordering, collections::VecDeque, fmt::Debug, mem};

enum Order {
    Level,
    Pre,
    In,
    Post,
}

#[derive(Debug)]
pub struct BinaryTree<T> {
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
    fn new_boxed(item: T) -> Box<Node<T>> {
        Box::new(Node {
            item,
            left: Link(None),
            right: Link(None),
        })
    }
}

impl<T: Ord + Debug> Link<T> {
    pub fn pop_max(&mut self) -> Option<T> {
        let mut curr = match self.0.as_mut() {
            Some(_) => self,
            None => {
                return None;
            }
        };

        while curr.0.as_ref().unwrap().right.0.is_some() {
            curr = &mut curr.0.as_mut().unwrap().right;
        }

        let node = curr.0.take().unwrap();
        curr.0 = node.left.0;
        Some(node.item)
    }

    pub fn pop_min(&mut self) -> Option<T> {
        let mut curr = match self.0.as_mut() {
            Some(_) => self,
            None => {
                return None;
            }
        };

        while curr.0.as_ref().unwrap().left.0.is_some() {
            curr = &mut curr.0.as_mut().unwrap().left;
        }

        let node = curr.0.take().unwrap();
        curr.0 = node.right.0;
        Some(node.item)
    }
}

impl<T: Ord + Debug> BinaryTree<T> {
    pub fn new() -> BinaryTree<T> {
        BinaryTree {
            head: Link(None),
            size: 0,
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn insert(&mut self, item: T) {
        let new_node = Node::new_boxed(item);

        let mut curr = match self.head.0.as_mut() {
            Some(head) => head,
            None => {
                self.head = Link(Some(new_node));
                return;
            }
        };

        loop {
            // allows duplicate item, if equal, go to left node
            let child = if new_node.item <= curr.item {
                &mut curr.left.0
            } else {
                &mut curr.right.0
            };

            match child {
                Some(child) => {
                    curr = child;
                }
                None => {
                    *child = Some(new_node);
                    break;
                }
            }
        }
    }

    pub fn remove(&mut self, item: &T) -> Option<T> {
        let mut curr = match self.head.0.as_mut() {
            Some(_head) => &mut self.head,
            None => {
                return None;
            }
        };

        loop {
            match curr.0.as_ref().unwrap().item.cmp(item) {
                Ordering::Less => curr = &mut curr.0.as_mut().unwrap().right,
                Ordering::Greater => curr = &mut curr.0.as_mut().unwrap().left,
                Ordering::Equal => {
                    let node = curr.0.as_mut().unwrap();
                    return match (node.left.0.as_mut(), node.right.0.as_mut()) {
                        (None, None) => Some(curr.0.take().unwrap().item),
                        (Some(_), None) => Some(mem::replace(
                            &mut node.item,
                            node.left.0.take().unwrap().item,
                        )),
                        (None, Some(_)) => Some(mem::replace(
                            &mut node.item,
                            node.right.0.take().unwrap().item,
                        )),
                        (Some(_), Some(_)) => {
                            return Some(mem::replace(
                                &mut node.item,
                                node.right.pop_min().unwrap(),
                            ));
                        }
                    };
                }
            }
        }
    }

    pub fn contains(&self, item: &T) -> bool {
        let mut curr = match self.head.0.as_ref() {
            Some(head) => Some(head),
            None => {
                return false;
            }
        };

        while let Some(node) = curr {
            match node.item.cmp(item) {
                Ordering::Greater => curr = node.left.0.as_ref(),
                Ordering::Less => curr = node.right.0.as_ref(),
                Ordering::Equal => return true,
            }
        }

        false
    }

    pub fn min(&self) -> Option<&T> {
        let mut curr = self.head.0.as_ref()?;
        while let Some(left) = curr.left.0.as_ref() {
            curr = left;
        }
        Some(&curr.item)
    }
    pub fn max(&self) -> Option<&T> {
        let mut curr = self.head.0.as_ref()?;
        while let Some(right) = curr.right.0.as_ref() {
            curr = right;
        }
        Some(&curr.item)
    }
    pub fn pop_min(&mut self) -> Option<T> {
        self.head.pop_min()
    }
    pub fn pop_max(&mut self) -> Option<T> {
        self.head.pop_max()
    }

    pub fn iter(&self, order_type: Order) -> Iter<T> {
        Iter {
            curr: self.head.0.as_deref(),
            nodes: VecDeque::new(),
            order: order_type,
        }
    }

    pub fn iter_mut(&mut self, order_type: Order) -> IterMut<T> {
        IterMut {
            curr: self.head.0.as_deref_mut(),
            nodes: VecDeque::new(),
            order: order_type,
        }
    }
}

impl<T: Ord + Debug> Default for BinaryTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, T> {
    curr: Option<&'a Node<T>>,
    nodes: VecDeque<&'a Node<T>>,
    order: Order,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.order {
            Order::Level => self.level_order_next(),
            Order::Pre => self.pre_order_next(),
            Order::In => self.in_order_next(),
            Order::Post => todo!(),
        }
    }
}

impl<'a, T> Iter<'a, T> {
    fn level_order_next(&mut self) -> Option<&'a T> {
        self.curr.take().map(|node| {
            if let Some(right) = node.right.0.as_deref() {
                self.nodes.push_front(right);
            }
            if let Some(left) = node.left.0.as_deref() {
                self.nodes.push_front(left);
            }
            self.curr = self.nodes.pop_back();
            &node.item
        })
    }

    fn pre_order_next(&mut self) -> Option<&'a T> {
        self.curr.take().map(|node| {
            if let Some(right) = node.right.0.as_deref() {
                self.nodes.push_front(right);
            }
            if let Some(left) = node.left.0.as_deref() {
                self.nodes.push_front(left);
            }
            self.curr = self.nodes.pop_front();
            &node.item
        })
    }

    fn in_order_next(&mut self) -> Option<&'a T> {
        while let Some(curr) = self.curr {
            self.nodes.push_front(curr);
            self.curr = curr.left.0.as_deref();
        }

        self.nodes.pop_front().map(|node| {
            self.curr = node.right.0.as_deref();
            &node.item
        })
    }
}

pub struct IterMut<'a, T> {
    curr: Option<&'a mut Node<T>>,
    nodes: VecDeque<&'a mut Node<T>>,
    order: Order,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.order {
            Order::Level => self.level_order_next(),
            Order::Pre => self.pre_order_next(),
            Order::In => self.in_order_next(),
            Order::Post => todo!(),
        }
    }
}

impl<'a, T> IterMut<'a, T> {
    fn level_order_next(&mut self) -> Option<&'a mut T> {
        self.curr.take().map(|node| {
            if let Some(right) = node.right.0.as_deref_mut() {
                self.nodes.push_front(right);
            }
            if let Some(left) = node.left.0.as_deref_mut() {
                self.nodes.push_front(left);
            }
            self.curr = self.nodes.pop_back();
            &mut node.item
        })
    }

    fn pre_order_next(&mut self) -> Option<&'a mut T> {
        self.curr.take().map(|node| {
            if let Some(right) = node.right.0.as_deref_mut() {
                self.nodes.push_front(right);
            }
            if let Some(left) = node.left.0.as_deref_mut() {
                self.nodes.push_front(left);
            }
            self.curr = self.nodes.pop_front();
            &mut node.item
        })
    }

    fn in_order_next(&mut self) -> Option<&'a mut T> {
        while let Some(curr) = self.curr.take() {
            self.curr = curr.left.0.as_deref_mut();
            self.nodes.push_front(curr);
        }
        self.nodes.pop_front().map(|node| {
            self.curr = node.right.0.as_deref_mut();
            &mut node.item
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whatever() {
        let mut tree = BinaryTree::new();
        tree.insert(8);
        tree.insert(4);
        tree.insert(2);
        tree.insert(1);
        tree.insert(3);
        tree.insert(6);
        tree.insert(5);
        tree.insert(7);
        tree.insert(12);
        tree.insert(10);
        tree.insert(9);
        tree.insert(11);
        tree.insert(14);
        tree.insert(13);
        tree.insert(15);

        let mut iter = tree.iter_mut(Order::In);
        for j in 1..=16 {
            if let Some(head) = iter.next() {
                *head += 2
            }
        }
        let mut iter = tree.iter(Order::In);
        for j in 1..=16 {
            println!("{:?}", iter.next());
        }
    }
}
