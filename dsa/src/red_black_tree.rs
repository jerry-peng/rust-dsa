use std::alloc;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::ptr::NonNull;

#[derive(Debug)]
pub enum Order {
    Level,
    Pre,
    In,
    Post,
}

#[derive(Debug)]
enum Color {
    RED,
    BLACK,
}

pub struct DuplicateItem;

#[derive(Debug)]
pub struct RedBlackTree<T> {
    head: Link<T>,
    size: usize,
}

#[derive(Debug)]
pub struct Link<T> {
    node: Option<NonNull<Node<T>>>,
    color: Color,
}

#[derive(Debug)]
pub struct Node<T> {
    item: T,
    parent: Link<T>,
    left: Link<T>,
    right: Link<T>,
}

impl<T: Ord + Debug> Node<T> {
    fn new(item: T) -> Node<T> {
        Node {
            item,
            parent: Link {
                node: None,
                color: Color::BLACK,
            },
            left: Link {
                node: None,
                color: Color::BLACK,
            },
            right: Link {
                node: None,
                color: Color::BLACK,
            },
        }
    }

    fn alloc(node: Node<T>) -> NonNull<Node<T>> {
        // create memory layout for a single node
        let layout = alloc::Layout::new::<Node<T>>();
        // allocate memory
        let raw_ptr = unsafe { alloc::alloc(layout) };
        // if memory allocation fails, signal error
        if raw_ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }
        // create non-null pointer, write node, and return pointer
        let non_null_ptr = unsafe { NonNull::new_unchecked(raw_ptr as *mut Node<T>) };
        unsafe { non_null_ptr.write(node) };
        non_null_ptr
    }
}

impl<T: Ord + Debug> RedBlackTree<T> {
    pub fn new() -> RedBlackTree<T> {
        RedBlackTree {
            head: Link {
                node: None,
                color: Color::BLACK,
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

    pub fn insert(&mut self, item: T) -> Result<(), DuplicateItem> {
        // if tree is empty (head points to None), assign new node to head
        // else, assign head node to curr which tracks current node during traversal
        let mut curr = match self.head.node.as_mut() {
            Some(head) => head,
            None => {
                self.size += 1;
                self.head = Link {
                    node: Some(Node::alloc(Node::new(item))),
                    color: Color::BLACK,
                };
                return Ok(());
            }
        };

        while let Some(node) =
    }

    pub fn remove(&mut self, item: &T) -> Option<T> {
        todo!();
    }

    pub fn contains(&self, item: &T) -> bool {
        // if tree is empty, return None
        // else, assign head node in "curr" which tracks current node during traversal
        let mut curr = match self.head.node.as_ref() {
            None => return false,
            Some(_) => self.head.node,
        };

        // traverse left if current node item is smaller,
        // or traverse right if item is bigger,
        // if an equal item is found, return true
        while let Some(node) = curr {
            let node = unsafe { node.as_ref() };
            match node.item.cmp(item) {
                Ordering::Greater => curr = node.left.node,
                Ordering::Less => curr = node.right.node,
                Ordering::Equal => return true,
            }
        }

        // no node with equal item found, return false
        false
    }

    pub fn min(&self) -> Option<&T> {
        todo!();
    }

    pub fn max(&self) -> Option<&T> {
        todo!();
    }

    pub fn pop_min(&mut self) -> Option<T> {
        todo!();
    }

    pub fn pop_max(&mut self) -> Option<T> {
        todo!();
    }
}

impl<T: Ord + Debug> Default for RedBlackTree<T> {
    fn default() -> Self {
        Self::new()
    }
}
