use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::mem;
use std::ptr::NonNull;
use std::{alloc, vec};

#[derive(Debug, PartialEq)]
pub struct DuplicateItemErr;

#[derive(Debug)]
pub enum TraversalOrder {
    Level,
    Pre,
    In,
    Post,
}

#[derive(Debug, PartialEq)]
enum Color {
    Red,
    Black,
}

#[derive(Debug, PartialEq)]
enum LinkType {
    Left,
    Right,
    Root,
}

#[derive(Debug)]
pub struct RedBlackTree<T> {
    root: NonNull<Link<T>>,
    size: usize,
}

/// Link struct, a node wrapper.
/// In context of red-black tree, an empty node with no item is a leaf node,
/// otherwise it's a branch node. In my implementation, node is wrapped in link
/// and leaf link contains no node, while branch link contains a node.
///
/// * `color`: color of link; new branch link are red, leaf link are black
/// * `parent`: parent link; empty if link is root
/// * `node`: node; empty for leaf link
#[derive(Debug, PartialEq)]
pub struct Link<T> {
    color: Color,
    parent: Option<NonNull<Link<T>>>,
    node: Option<Node<T>>,
}

/// Node struct;
/// * `item`: item
/// * `left`: link to left child
/// * `right`: link to right child
#[derive(Debug, PartialEq)]
struct Node<T> {
    item: T,
    left: NonNull<Link<T>>,
    right: NonNull<Link<T>>,
}

impl<T> Link<T>
where
    T: Debug + PartialEq,
{
    fn new_leaf(parent_ptr: Option<NonNull<Link<T>>>) -> NonNull<Link<T>> {
        // create memory layout for a single link
        let layout = alloc::Layout::new::<Link<T>>();
        // allocate memory
        let raw_ptr = unsafe { alloc::alloc(layout) };
        // if memory allocation fails, signal error
        if raw_ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }
        // create non-null pointer, write link, and return pointer
        let non_null_ptr = unsafe { NonNull::new_unchecked(raw_ptr as *mut Link<T>) };

        let link = Link {
            color: Color::Black,
            parent: parent_ptr,
            node: None,
        };
        unsafe { non_null_ptr.write(link) };
        non_null_ptr
    }

    fn gen_branch(link_ptr: NonNull<Link<T>>, item: T, color: Color) {
        let mut link = unsafe { link_ptr.read() };
        if Link::is_branch(link_ptr) {
            unreachable!(
                "Node already exists in link; existing node: {:?}",
                link.node
            );
        }
        link.color = color;
        link.node = Some(Node {
            item,
            left: Link::new_leaf(Some(link_ptr)),
            right: Link::new_leaf(Some(link_ptr)),
        });
        unsafe { link_ptr.write(link) };
    }

    fn is_root(link_ptr: NonNull<Link<T>>) -> bool {
        unsafe { link_ptr.read() }.parent.is_none()
    }

    fn is_branch(link_ptr: NonNull<Link<T>>) -> bool {
        unsafe { link_ptr.read() }.node.is_some()
    }

    fn get_link_type(link_ptr: NonNull<Link<T>>) -> LinkType {
        let link = unsafe { link_ptr.read() };
        match link.parent {
            Some(parent_ptr) => {
                let parent_node = unsafe { parent_ptr.read() }.node.unwrap();
                if link_ptr == parent_node.left {
                    LinkType::Left
                } else if link_ptr == parent_node.right {
                    LinkType::Right
                } else {
                    unreachable!(
                        "Mislink between parent and child; parent node: [{:?}]; child node: [{:?}]",
                        parent_node, link.node
                    );
                }
            }
            None => LinkType::Root,
        }
    }

    fn get_left_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        unsafe { link_ptr.read() }
            .node
            .as_ref()
            .map(|node| node.left)
    }

    fn get_right_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        unsafe { link_ptr.read() }
            .node
            .as_ref()
            .map(|node| node.right)
    }

    fn get_parent_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        unsafe { link_ptr.read() }.parent
    }

    fn get_sibling_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        let link_type = Link::get_link_type(link_ptr);
        unsafe { link_ptr.read() }
            .parent
            .and_then(|parent_ptr| match link_type {
                LinkType::Left => Some(Link::get_right_ptr(parent_ptr).unwrap()),
                LinkType::Right => Some(Link::get_left_ptr(parent_ptr).unwrap()),
                LinkType::Root => None,
            })
    }

    fn get_subtree_min_link(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        let mut curr = link_ptr;
        while let Some(node) = unsafe { curr.read() }.node {
            curr = node.left;
        }
        unsafe { curr.read() }.parent
    }

    fn get_subtree_max_link(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        let mut curr = link_ptr;
        while let Some(node) = unsafe { curr.read() }.node {
            curr = node.right;
        }
        unsafe { curr.read() }.parent
    }
}

impl<T> RedBlackTree<T>
where
    T: Ord + Debug,
{
    pub fn new() -> RedBlackTree<T> {
        RedBlackTree {
            root: Link::new_leaf(None),
            size: 0,
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    pub fn insert(&mut self, item: T) -> Result<(), DuplicateItemErr> {
        let mut curr_ptr = self.root;

        while let Some(node) = unsafe { curr_ptr.read().node } {
            match node.item.cmp(&item) {
                Ordering::Greater => curr_ptr = node.left,
                Ordering::Less => curr_ptr = node.right,
                Ordering::Equal => return Err(DuplicateItemErr),
            }
        }

        let new_link_color = if self.is_empty() {
            Color::Black
        } else {
            Color::Red
        };
        Link::gen_branch(curr_ptr, item, new_link_color);
        self.size += 1;

        self.rebalance_insertion(curr_ptr);
        Ok(())
    }

    fn rebalance_insertion(&mut self, mut curr_ptr: NonNull<Link<T>>) {
        while !Link::is_root(curr_ptr) {
            let parent_ptr = Link::get_parent_ptr(curr_ptr).unwrap();
            let mut parent = unsafe { parent_ptr.read() };
            if parent.color == Color::Black {
                break;
            }
            let uncle_ptr = Link::get_sibling_ptr(parent_ptr).unwrap();
            let mut uncle = unsafe { uncle_ptr.read() };

            let grandparent_ptr = Link::get_parent_ptr(parent_ptr).unwrap();

            match uncle.color {
                Color::Red => {
                    parent.color = Color::Black;
                    unsafe { parent_ptr.write(parent) };
                    uncle.color = Color::Black;
                    unsafe { uncle_ptr.write(uncle) };

                    if !Link::is_root(grandparent_ptr) {
                        let mut grandparent = unsafe { grandparent_ptr.read() };
                        grandparent.color = Color::Red;
                        unsafe { grandparent_ptr.write(grandparent) };
                        curr_ptr = grandparent_ptr;
                    } else {
                        break;
                    }
                }
                Color::Black => {
                    match (
                        Link::get_link_type(curr_ptr),
                        Link::get_link_type(parent_ptr),
                    ) {
                        (LinkType::Left, LinkType::Left) => {
                            self.subtree_rotate_right(grandparent_ptr, true)
                        }
                        (LinkType::Right, LinkType::Right) => {
                            self.subtree_rotate_left(grandparent_ptr, true)
                        }
                        (LinkType::Left, LinkType::Right) => {
                            self.subtree_rotate_right(parent_ptr, false);
                            self.subtree_rotate_left(grandparent_ptr, true);
                        }
                        (LinkType::Right, LinkType::Left) => {
                            self.subtree_rotate_left(parent_ptr, false);
                            self.subtree_rotate_right(grandparent_ptr, true);
                        }
                        // TODO update message
                        _ => unreachable!("curr and parent cannot possibly be root"),
                    };
                    break;
                }
            }
        }
    }

    pub fn remove(&mut self, item: &T) -> Option<T> {
        let mut curr_ptr = self.root;

        loop {
            if let Some(node) = unsafe { curr_ptr.read() }.node {
                match node.item.cmp(item) {
                    Ordering::Greater => curr_ptr = node.left,
                    Ordering::Less => curr_ptr = node.right,
                    Ordering::Equal => break,
                }
            } else {
                return None;
            }
        }

        let (black_token_ptr, item) = self.remove_link(curr_ptr);
        self.size -= 1;
        if let Some(ptr) = black_token_ptr {
            self.rebalance_removal(ptr);
        }
        Some(item)
    }

    fn remove_link(&mut self, mut link_ptr: NonNull<Link<T>>) -> (Option<NonNull<Link<T>>>, T) {
        let right_ptr = Link::get_right_ptr(link_ptr).unwrap();
        let left_ptr = Link::get_left_ptr(link_ptr).unwrap();
        let right = unsafe { right_ptr.read() };
        let left = unsafe { left_ptr.read() };

        let (ptr_to_delete, child_type_to_connect) = match (left.node, right.node) {
            (None, None) | (None, Some(_)) => (link_ptr, LinkType::Right),
            (Some(_), None) => (link_ptr, LinkType::Left),
            (Some(_), Some(_)) => {
                let mut left_max_ptr = Link::get_subtree_max_link(left_ptr).unwrap();
                let left_max_node = unsafe { left_max_ptr.as_mut() }.node.as_mut().unwrap();
                let left_max_item = &mut left_max_node.item;
                let link_ptr_item = &mut unsafe { link_ptr.as_mut() }.node.as_mut().unwrap().item;
                mem::swap(left_max_item, link_ptr_item);
                (left_max_ptr, LinkType::Left)
            }
        };

        let mut link_to_delete = unsafe { ptr_to_delete.read() };
        let child_ptr_to_connect = match child_type_to_connect {
            LinkType::Left => link_to_delete.node.as_mut().unwrap().left,
            LinkType::Right => link_to_delete.node.as_mut().unwrap().right,
            LinkType::Root => unreachable!("IMPOSSIBLE"),
        };

        let mut child_link_to_connect = unsafe { child_ptr_to_connect.read() };
        match Link::get_link_type(ptr_to_delete) {
            LinkType::Left => {
                let parent_ptr = link_to_delete.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.node.as_mut().unwrap().left = child_ptr_to_connect;
                child_link_to_connect.parent = Some(parent_ptr);
                unsafe {
                    parent_ptr.write(parent);
                    child_ptr_to_connect.write(child_link_to_connect);
                };
            }
            LinkType::Right => {
                let parent_ptr = link_to_delete.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.node.as_mut().unwrap().right = child_ptr_to_connect;
                child_link_to_connect.parent = Some(parent_ptr);
                unsafe {
                    parent_ptr.write(parent);
                    child_ptr_to_connect.write(child_link_to_connect);
                };
            }
            LinkType::Root => {
                self.root = child_ptr_to_connect;
                child_link_to_connect.parent = None;
                child_link_to_connect.color = Color::Black;
                unsafe { child_ptr_to_connect.write(child_link_to_connect) };
            }
        }

        // drop links
        unsafe {
            let Node {
                item,
                left: left_ptr,
                right: right_ptr,
            } = link_to_delete.node.unwrap();
            let _ = Box::from_raw(ptr_to_delete.as_ptr());
            match child_type_to_connect {
                LinkType::Left => {
                    let _ = Box::from_raw(right_ptr.as_ptr());
                }
                LinkType::Right => {
                    let _ = Box::from_raw(left_ptr.as_ptr());
                }
                LinkType::Root => unreachable!("IMPOSSIBLE"),
            };

            let black_token_ptr = match link_to_delete.color {
                Color::Red => None,
                Color::Black => match child_type_to_connect {
                    LinkType::Left => Some(left_ptr),
                    LinkType::Right => Some(right_ptr),
                    LinkType::Root => unreachable!("IMPOSSIBLE"),
                },
            };

            (black_token_ptr, item)
        }
    }

    fn rebalance_removal(&mut self, mut black_token_ptr: NonNull<Link<T>>) {
        while black_token_ptr != self.root {
            let mut black_token_link = unsafe { black_token_ptr.read() };
            match black_token_link.color {
                Color::Red => {
                    black_token_link.color = Color::Black;
                    unsafe { black_token_ptr.write(black_token_link) };
                    break;
                }
                Color::Black => {
                    let sibling_ptr = Link::get_sibling_ptr(black_token_ptr).unwrap();
                    let mut sibling = unsafe { sibling_ptr.read() };
                    match sibling.color {
                        Color::Red => {
                            let parent_ptr = Link::get_parent_ptr(black_token_ptr).unwrap();
                            match Link::get_link_type(black_token_ptr) {
                                LinkType::Left => self.subtree_rotate_left(parent_ptr, true),
                                LinkType::Right => self.subtree_rotate_right(parent_ptr, true),
                                // TODO fix panic message
                                LinkType::Root => unreachable!("NOT POSSIBLE"),
                            }
                        }
                        Color::Black => {
                            // We can safely unwrap, because if black token node is black,
                            // sibling has to be black to maintain red black tree property where
                            // leaf node's black node count is equal
                            let left_nephew_ptr = Link::get_left_ptr(sibling_ptr).unwrap();
                            let right_nephew_ptr = Link::get_right_ptr(sibling_ptr).unwrap();
                            let mut left_nephew = unsafe { left_nephew_ptr.read() };
                            let mut right_nephew = unsafe { right_nephew_ptr.read() };
                            if left_nephew.color == Color::Black
                                && right_nephew.color == Color::Black
                            {
                                sibling.color = Color::Red;
                                unsafe { sibling_ptr.write(sibling) };
                                black_token_ptr = Link::get_parent_ptr(black_token_ptr).unwrap();
                            } else {
                                // one of the nephews has to be red
                                match Link::get_link_type(black_token_ptr) {
                                    LinkType::Left => {
                                        if right_nephew.color == Color::Black {
                                            self.subtree_rotate_right(sibling_ptr, true);
                                            self.subtree_rotate_left(
                                                black_token_link.parent.unwrap(),
                                                true,
                                            );
                                            let mut sibling = unsafe { sibling_ptr.read() };
                                            sibling.color = Color::Black;
                                            unsafe { sibling_ptr.write(sibling) };
                                        } else {
                                            self.subtree_rotate_left(
                                                black_token_link.parent.unwrap(),
                                                true,
                                            );
                                            right_nephew.color = Color::Black;
                                            unsafe { right_nephew_ptr.write(right_nephew) };
                                        }
                                    }
                                    LinkType::Right => {
                                        if left_nephew.color == Color::Black {
                                            self.subtree_rotate_left(sibling_ptr, true);
                                            self.subtree_rotate_right(
                                                black_token_link.parent.unwrap(),
                                                true,
                                            );
                                            let mut sibling = unsafe { sibling_ptr.read() };
                                            sibling.color = Color::Black;
                                            unsafe { sibling_ptr.write(sibling) };
                                        } else {
                                            self.subtree_rotate_right(
                                                black_token_link.parent.unwrap(),
                                                true,
                                            );
                                            left_nephew.color = Color::Black;
                                            unsafe { left_nephew_ptr.write(left_nephew) };
                                        }
                                    }
                                    // TODO fix message
                                    LinkType::Root => unreachable!("UNREACHABLE!!!"),
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    fn subtree_rotate_left(&mut self, root_ptr: NonNull<Link<T>>, swap_color: bool) {
        let root_link_type = Link::get_link_type(root_ptr);
        // self, right child should be a branch node by default, and right left child should at
        // least be a link
        // Link parent
        let right_ptr = Link::get_right_ptr(root_ptr).unwrap();
        let right_left_ptr = Link::get_left_ptr(right_ptr).unwrap();
        let mut root = unsafe { root_ptr.read() };
        let mut right = unsafe { right_ptr.read() };
        let mut right_left = unsafe { right_left_ptr.read() };

        right.parent = root.parent;
        root.parent = Some(right_ptr);
        right_left.parent = Some(root_ptr);

        root.node.as_mut().unwrap().right = right_left_ptr;
        right.node.as_mut().unwrap().left = root_ptr;

        if swap_color {
            mem::swap(&mut right.color, &mut root.color);
        }

        match root_link_type {
            LinkType::Left => {
                let parent_ptr = right.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.node.as_mut().unwrap().left = right_ptr;
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Right => {
                let parent_ptr = right.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.node.as_mut().unwrap().right = right_ptr;
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Root => {
                self.root = right_ptr;
                right.color = Color::Black;
            }
        }

        unsafe { root_ptr.write(root) };
        unsafe { right_ptr.write(right) };
        unsafe { right_left_ptr.write(right_left) };
    }

    fn subtree_rotate_right(&mut self, root_ptr: NonNull<Link<T>>, swap_color: bool) {
        let root_link_type = Link::get_link_type(root_ptr);
        // self, left child should be a branch node by default, and left right child should at
        // least be a link
        // Link parent
        let left_ptr = Link::get_left_ptr(root_ptr).unwrap();
        let left_right_ptr = Link::get_right_ptr(left_ptr).unwrap();
        let mut root = unsafe { root_ptr.read() };
        let mut left = unsafe { left_ptr.read() };
        let mut left_right = unsafe { left_right_ptr.read() };

        left.parent = root.parent;
        root.parent = Some(left_ptr);
        left_right.parent = Some(root_ptr);

        root.node.as_mut().unwrap().left = left_right_ptr;
        left.node.as_mut().unwrap().right = root_ptr;

        if swap_color {
            mem::swap(&mut left.color, &mut root.color);
        }

        match root_link_type {
            LinkType::Left => {
                let parent_ptr = left.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.node.as_mut().unwrap().left = left_ptr;
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Right => {
                let parent_ptr = left.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.node.as_mut().unwrap().right = left_ptr;
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Root => {
                self.root = left_ptr;
                left.color = Color::Black;
            }
        }

        unsafe { root_ptr.write(root) };
        unsafe { left_ptr.write(left) };
        unsafe { left_right_ptr.write(left_right) };
    }

    pub fn contains(&self, item: &T) -> bool {
        // set root as current link
        // traverse left if current node item is smaller,
        // or traverse right if item is bigger,
        // if an equal item is found, return true
        let mut curr_ptr = self.root;
        while let Some(ref node) = unsafe { curr_ptr.read() }.node {
            match node.item.cmp(item) {
                Ordering::Greater => curr_ptr = node.left,
                Ordering::Less => curr_ptr = node.right,
                Ordering::Equal => return true,
            }
        }

        // no node with equal item found, return false
        false
    }

    pub fn min(&self) -> Option<&T> {
        let mut curr_ptr = self.root;
        while let Some(node) = unsafe { curr_ptr.read() }.node {
            curr_ptr = node.left;
        }
        unsafe { curr_ptr.read() }
            .parent
            .map(|parent| &unsafe { parent.as_ref() }.node.as_ref().unwrap().item)
    }

    pub fn max(&self) -> Option<&T> {
        let mut curr_ptr = self.root;
        while let Some(node) = unsafe { curr_ptr.read() }.node {
            curr_ptr = node.right;
        }
        unsafe { curr_ptr.read() }
            .parent
            .map(|parent| &unsafe { parent.as_ref() }.node.as_ref().unwrap().item)
    }

    pub fn height(&self) -> usize {
        todo!()
    }

    pub fn pop_min(&mut self) -> Option<T> {
        todo!();
    }

    pub fn pop_max(&mut self) -> Option<T> {
        todo!();
    }

    pub fn iter(&self, order: TraversalOrder) -> Iter<T> {
        Iter {
            curr: Some(unsafe { self.root.as_ref() }),
            links: VecDeque::new(),
            post_links: VecDeque::new(),
            order,
        }
    }

    pub fn into_iter(self, order: TraversalOrder) -> IntoIter<T> {
        IntoIter {
            curr: None,
            links: VecDeque::new(),
            post_links: VecDeque::new(),
            order,
        }
    }
}

impl<T> Default for RedBlackTree<T>
where
    T: Ord + Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, T> {
    curr: Option<&'a Link<T>>,
    links: VecDeque<&'a Link<T>>,
    post_links: VecDeque<(&'a Link<T>, Option<&'a Link<T>>)>,
    order: TraversalOrder,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

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
    fn level_order_next(&mut self) -> Option<&'a T> {
        self.curr.take().and_then(|link| {
            link.node.as_ref().map(|node| {
                let left_link = unsafe { node.left.as_ref() };
                if left_link.node.is_some() {
                    self.links.push_front(left_link)
                }
                let right_link = unsafe { node.right.as_ref() };
                if right_link.node.is_some() {
                    self.links.push_front(right_link)
                }

                let item = &node.item;
                self.curr = self.links.pop_back();
                item
            })
        })
    }

    fn pre_order_next(&mut self) -> Option<&'a T> {
        self.curr.take().and_then(|link| {
            link.node.as_ref().map(|node| {
                let right_link = unsafe { node.right.as_ref() };
                if right_link.node.is_some() {
                    self.links.push_front(right_link)
                }
                let left_link = unsafe { node.left.as_ref() };
                if left_link.node.is_some() {
                    self.links.push_front(left_link)
                }

                self.curr = self.links.pop_front();
                &node.item
            })
        })
    }

    fn in_order_next(&mut self) -> Option<&'a T> {
        while let Some(link) = self.curr {
            self.curr = link.node.as_ref().map(|node| {
                self.links.push_front(link);
                unsafe { node.left.as_ref() }
            })
        }

        self.links.pop_front().and_then(|link| {
            link.node.as_ref().map(|node| {
                let right_link = unsafe { node.right.as_ref() };
                if right_link.node.is_some() {
                    self.curr = Some(right_link);
                }
                &node.item
            })
        })
    }

    fn post_order_next(&mut self) -> Option<&'a T> {
        loop {
            while let Some(link) = self.curr {
                self.curr = link.node.as_ref().map(|node| {
                    let right_link = unsafe { node.right.as_ref() };
                    match right_link.node.as_ref() {
                        Some(_node) => self.post_links.push_front((link, Some(right_link))),
                        None => self.post_links.push_front((link, None)),
                    }
                    unsafe { node.left.as_ref() }
                })
            }

            match self.post_links.pop_front() {
                Some(links) => match links.1 {
                    Some(right_link) => {
                        self.post_links.push_front((links.0, None));
                        self.curr = Some(right_link)
                    }
                    None => return Some(&links.0.node.as_ref().unwrap().item),
                },
                None => return None,
            }
        }
    }
}

type IntoIterPostOrderLink<T> = (NonNull<Link<T>>, Option<NonNull<Link<T>>>);
pub struct IntoIter<T> {
    // own the tree so it can be dropped later
    curr: Option<NonNull<Link<T>>>,
    links: VecDeque<NonNull<Link<T>>>,
    // post-order iterator uses post_nodes
    // within a VecDeque item, the first tuple parameter stores
    // the node, and seocnd parameter stores unprocessed right child
    post_links: VecDeque<IntoIterPostOrderLink<T>>,
    order: TraversalOrder,
}

impl<T> Iterator for IntoIter<T>
where
    T: PartialEq + Debug,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.order {
            TraversalOrder::Level => self.level_order_next(),
            TraversalOrder::Pre => self.pre_order_next(),
            TraversalOrder::In => self.in_order_next(),
            TraversalOrder::Post => self.post_order_next(),
        }
    }
}

impl<T> IntoIter<T>
where
    T: PartialEq + Debug,
{
    fn level_order_next(&mut self) -> Option<T> {
        // TODO: it works, but it's not freeing memories correctly
        self.curr.take().and_then(|link| {
            unsafe { link.read() }.node.map(|node| {
                let left_link = unsafe { node.left.read() };
                if left_link.node.is_some() {
                    self.links.push_front(node.left);
                }
                let right_link = unsafe { node.right.read() };
                if right_link.node.is_some() {
                    self.links.push_front(node.right);
                }

                let item = node.item;
                self.curr = self.links.pop_back();
                item
            })
        })
    }

    fn pre_order_next(&mut self) -> Option<T> {
        self.curr.take().and_then(|link| {
            unsafe { link.read() }.node.map(|node| {
                let right_link = unsafe { node.right.read() };
                if right_link.node.is_some() {
                    self.links.push_front(node.right)
                }
                let left_link = unsafe { node.left.read() };
                if left_link.node.is_some() {
                    self.links.push_front(node.left)
                }

                let item = node.item;
                self.curr = self.links.pop_front();
                item
            })
        })
    }

    fn in_order_next(&mut self) -> Option<T> {
        while let Some(link) = self.curr {
            self.curr = unsafe { link.read() }.node.as_ref().map(|node| {
                self.links.push_front(link);
                node.left
            })
        }

        self.links.pop_front().and_then(|link| {
            unsafe { link.read() }.node.map(|node| {
                let right_link = unsafe { node.right.read() };
                if right_link.node.is_some() {
                    self.curr = Some(node.right);
                }
                node.item
            })
        })
    }

    fn post_order_next(&mut self) -> Option<T> {
        loop {
            while let Some(link) = self.curr {
                self.curr = unsafe { link.read() }.node.map(|node| {
                    let right_link = unsafe { node.right.as_ref() };
                    match right_link.node.as_ref() {
                        Some(_node) => self.post_links.push_front((link, Some(node.right))),
                        None => self.post_links.push_front((link, None)),
                    }
                    node.left
                })
            }

            match self.post_links.pop_front() {
                Some(links) => match links.1 {
                    Some(right_link) => {
                        self.post_links.push_front((links.0, None));
                        self.curr = Some(right_link)
                    }
                    None => return Some(unsafe { links.0.read() }.node.unwrap().item),
                },
                None => return None,
            }
        }
    }
}

impl<T> Drop for RedBlackTree<T> {
    fn drop(&mut self) {
        let mut nodes = vec![self.root];

        while let Some(link) = nodes.pop() {
            let mut link = unsafe { Box::from_raw(link.as_ptr()) };
            let node = link.node.take();
            node.inspect(|node| {
                nodes.push(node.left);
                nodes.push(node.right);
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{self, Value};
    use std::cmp::{max, min};
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

    fn validate_bst(tree: &RedBlackTree<i32>) {
        // node, min, max
        let min_val: Option<i32> = None;
        let max_val: Option<i32> = None;
        let root = unsafe { tree.root.read() };
        if root.node.is_none() {
            return;
        }
        let mut queue = vec![(tree.root, min_val, max_val)];

        while let Some(queue_item) = queue.pop() {
            let link_ptr = queue_item.0;
            let min_val = queue_item.1;
            let max_val = queue_item.2;

            let link = unsafe { link_ptr.read() };
            let node = link.node.as_ref().unwrap();

            match (min_val, max_val) {
                (None, None) => {}
                (None, Some(max)) => assert!(node.item < max),
                (Some(min), None) => assert!(node.item > min),
                (Some(min), Some(max)) => assert!(node.item > min && node.item < max),
            }

            if unsafe { node.left.read() }.node.as_ref().is_some() {
                queue.push((
                    node.left,
                    min_val,
                    Some(max_val.map_or(node.item, |val| min(val, node.item))),
                ));
            }
            if unsafe { node.right.read() }.node.as_ref().is_some() {
                queue.push((
                    node.right,
                    Some(min_val.map_or(node.item, |val| max(val, node.item))),
                    max_val,
                ));
            }
        }
    }

    fn validate_rbt<T: Debug>(tree: &RedBlackTree<T>) {
        let root = unsafe { tree.root.read() };
        assert_eq!(root.color, Color::Black);

        let mut queue: Vec<NonNull<Link<T>>> = Vec::new();
        queue.push(tree.root);

        let mut black_link_heights: HashMap<NonNull<Link<T>>, usize> = HashMap::new();
        let mut leaf_heights: HashSet<usize> = HashSet::new();

        while let Some(link_ptr) = queue.pop() {
            let link = unsafe { link_ptr.read() };
            match link.parent {
                Some(parent_ptr) => {
                    let parent_height = black_link_heights.get(&parent_ptr).unwrap();
                    let height = match link.color {
                        Color::Red => *parent_height,
                        Color::Black => *parent_height + 1,
                    };
                    assert!(black_link_heights.insert(link_ptr, height).is_none());
                }
                None => {
                    assert!(black_link_heights.insert(link_ptr, 1).is_none());
                }
            }
            match link.node {
                Some(ref node) => {
                    if link.color == Color::Red {
                        assert_eq!(unsafe { node.left.read() }.color, Color::Black);
                        assert_eq!(unsafe { node.right.read() }.color, Color::Black);
                    }
                    queue.push(node.left);
                    queue.push(node.right);
                }
                None => {
                    assert_eq!(link.color, Color::Black);
                    leaf_heights.insert(*black_link_heights.get(&link_ptr).unwrap());
                }
            }
            if link.node.is_none() {
                assert_eq!(link.color, Color::Black);
            }
        }
        assert_eq!(leaf_heights.len(), 1);
    }

    fn validate_order(tree: &RedBlackTree<i32>, expected_orders: &Value) {
        let order_types = vec![
            (TraversalOrder::Level, "level"),
            (TraversalOrder::In, "in"),
            (TraversalOrder::Pre, "pre"),
            (TraversalOrder::Post, "post"),
        ];
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

    fn read_json_data(filepath: &str) -> Value {
        let insert_order_json_string =
            fs::read_to_string(path::Path::new(filepath)).expect("Unable to read file");
        serde_json::from_str(insert_order_json_string.as_str()).unwrap()
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
        // right-tilted tree contains
        let tree: RedBlackTree<i32> = new_tilted_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }
        // left-tilted tree contains
        let tree: RedBlackTree<i32> = new_tilted_tree(true);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }

        // compact tree contains
        let tree: RedBlackTree<i32> = new_compact_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }
        // compact mirror tree contains
        let tree: RedBlackTree<i32> = new_compact_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }

        // spread tree contains
        let tree: RedBlackTree<i32> = new_spread_tree(false);
        for i in -5..=25 {
            if (1..=20).contains(&i) {
                assert!(tree.contains(&i));
            } else {
                assert!(!tree.contains(&i));
            }
        }
        // spread mirror tree contains
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
            // validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            // validate_order(&tree, &expected_orders[19]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(20 - i).unwrap()]);
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
            // validate_order(&tree, &expected_orders[19]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(2 * i - 2).unwrap()]);

            let _ = tree.insert(21 - i);
            assert!(tree.contains(&(21 - i)));
            assert_eq!(tree.size(), usize::try_from(2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            // validate_order(&tree, &expected_orders[usize::try_from(2 * i - 1).unwrap()]);
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
            // validate_order(&tree, &expected_orders[19]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(2 * i - 2).unwrap()]);

            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            // validate_order(&tree, &expected_orders[usize::try_from(2 * i - 1).unwrap()]);
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
            // validate_order(&tree, &expected_orders[19]);
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
            // validate_order(
            //     &tree,
            //     &expected_orders[usize::try_from(20 - 2 * i).unwrap()],
            // );

            let _ = tree.insert(21 - i);
            assert!(tree.contains(&(21 - i)));
            assert_eq!(tree.size(), usize::try_from(22 - 2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            // validate_order(
            //     &tree,
            //     &expected_orders[usize::try_from(21 - 2 * i).unwrap()],
            // );
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
            // validate_order(&tree, &expected_orders[19]);
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
            // validate_order(
            //     &tree,
            //     &expected_orders[usize::try_from(20 - 2 * i).unwrap()],
            // );

            let _ = tree.insert(i);
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(22 - 2 * i).unwrap());
            assert!(!tree.is_empty());
            validate_bst(&tree);
            validate_rbt(&tree);
            // validate_order(
            //     &tree,
            //     &expected_orders[usize::try_from(21 - 2 * i).unwrap()],
            // );
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
            // validate_order(&tree, &expected_orders[19]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_single_item_sprea() {
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
            // validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            // validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }

    #[test]
    fn test_remove_all_asc_order_tilted() {
        // right-tilted tree
        let mut tree = new_tilted_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }

        // left-tilted tree
        let mut tree = new_tilted_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
    }

    #[test]
    fn test_remove_all_asc_order_compact() {
        // compact tree
        let mut tree = new_compact_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }

        // compact mirror tree
        let mut tree = new_compact_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
    }

    #[test]
    fn test_remove_all_asc_order_spread() {
        // spread tree
        let mut tree = new_spread_tree(false);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }

        // spread mirror tree
        let mut tree = new_spread_tree(true);
        for i in 1..=20 {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(21 - i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(20 - i).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
    }

    #[test]
    fn test_remove_all_desc_order_tilted() {
        // right-tilted tree
        let mut tree = new_tilted_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }

        // right-tilted tree
        let mut tree = new_tilted_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
    }

    #[test]
    fn test_remove_all_desc_order_compact() {
        // compact tree
        let mut tree = new_compact_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
        // compact mirror tree
        let mut tree = new_compact_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
    }

    #[test]
    fn test_remove_all_desc_order_spread() {
        // spread tree
        let mut tree = new_spread_tree(false);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
        // spread mirror tree
        let mut tree = new_spread_tree(true);
        for i in (1..=20).rev() {
            assert!(tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i).unwrap());
            assert_eq!(tree.remove(&i), Some(i));
            assert!(!tree.contains(&i));
            assert_eq!(tree.size(), usize::try_from(i - 1).unwrap());
            validate_bst(&tree);
            validate_rbt(&tree);
        }
    }
}
