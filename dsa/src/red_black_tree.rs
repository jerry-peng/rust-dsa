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
    root: Option<NonNull<Link<T>>>,
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
    item: T,
    left: Option<NonNull<Link<T>>>,
    right: Option<NonNull<Link<T>>>,
}

enum BlackToken<T> {
    SomeLink {
        link_ptr: NonNull<Link<T>>,
        link_type: LinkType,
    },
    Null {
        parent_ptr: NonNull<Link<T>>,
        link_type: LinkType,
    },
}

impl<T> Link<T>
where
    T: Debug + PartialEq,
{
    fn new_link(parent_ptr: Option<NonNull<Link<T>>>, item: T) -> NonNull<Link<T>> {
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

        // if parent pointer is none, new link is root which is black, otherwise, link is red
        let color = if let Some(_) = parent_ptr {
            Color::Red
        } else {
            Color::Black
        };

        let link = Link {
            color,
            parent: parent_ptr,
            item,
            left: None,
            right: None,
        };
        unsafe { non_null_ptr.write(link) };
        non_null_ptr
    }

    fn is_root(link_ptr: NonNull<Link<T>>) -> bool {
        unsafe { link_ptr.read() }.parent.is_none()
    }

    fn get_link_type(link_ptr: NonNull<Link<T>>) -> LinkType {
        let link = unsafe { link_ptr.read() };
        match link.parent {
            Some(parent_ptr) => {
                let parent = unsafe { parent_ptr.read() };
                if let Some(left) = parent.left
                    && link_ptr == left
                {
                    LinkType::Left
                } else if let Some(right) = parent.right
                    && link_ptr == right
                {
                    LinkType::Right
                } else {
                    unreachable!(
                        "Mislink between parent and child; parent: [{:?}]; child: [{:?}]",
                        parent, link
                    );
                }
            }
            None => LinkType::Root,
        }
    }

    fn get_left_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        unsafe { link_ptr.read() }.left
    }

    fn get_right_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        unsafe { link_ptr.read() }.right
    }

    fn get_parent_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        unsafe { link_ptr.read() }.parent
    }

    fn get_sibling_ptr(link_ptr: NonNull<Link<T>>) -> Option<NonNull<Link<T>>> {
        let link_type = Link::get_link_type(link_ptr);
        let link = unsafe { link_ptr.read() };
        match link_type {
            LinkType::Left => Link::get_right_ptr(link.parent.unwrap()),
            LinkType::Right => Link::get_left_ptr(link.parent.unwrap()),
            LinkType::Root => None,
        }
    }

    fn get_subtree_min_link(link_ptr: NonNull<Link<T>>) -> NonNull<Link<T>> {
        let mut curr_ptr = link_ptr;
        while let Some(left_ptr) = unsafe { curr_ptr.read() }.left {
            curr_ptr = left_ptr;
        }
        curr_ptr
    }

    fn get_subtree_max_link(link_ptr: NonNull<Link<T>>) -> NonNull<Link<T>> {
        let mut curr_ptr = link_ptr;
        while let Some(right_ptr) = unsafe { curr_ptr.read() }.right {
            curr_ptr = right_ptr;
        }
        curr_ptr
    }

    fn get_opt_link_ptr_color(link_ptr: Option<NonNull<Link<T>>>) -> Color {
        match link_ptr {
            Some(ptr) => unsafe { ptr.read() }.color,
            None => Color::Black,
        }
    }
}

impl<T> RedBlackTree<T>
where
    T: Ord + Debug,
{
    pub fn new() -> RedBlackTree<T> {
        RedBlackTree {
            root: None,
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
        let mut curr_ptr = match self.root {
            Some(root_ptr) => root_ptr,
            None => {
                self.root = Some(Link::new_link(None, item));
                self.size += 1;
                return Ok(());
            }
        };

        loop {
            let mut curr_link = unsafe { curr_ptr.read() };
            match curr_link.item.cmp(&item) {
                Ordering::Greater => {
                    if let Some(left_ptr) = curr_link.left {
                        curr_ptr = left_ptr;
                    } else {
                        let new_link_ptr = Link::new_link(Some(curr_ptr), item);
                        curr_link.left = Some(new_link_ptr);
                        unsafe { curr_ptr.write(curr_link) };
                        curr_ptr = new_link_ptr;
                        break;
                    }
                }
                Ordering::Less => {
                    if let Some(right_ptr) = curr_link.right {
                        curr_ptr = right_ptr;
                    } else {
                        let new_link_ptr = Link::new_link(Some(curr_ptr), item);
                        curr_link.right = Some(new_link_ptr);
                        unsafe { curr_ptr.write(curr_link) };
                        curr_ptr = new_link_ptr;
                        break;
                    }
                }
                Ordering::Equal => return Err(DuplicateItemErr),
            }
        }

        self.rebalance_insertion(curr_ptr);
        self.size += 1;
        Ok(())
    }

    fn rebalance_insertion(&mut self, mut curr_ptr: NonNull<Link<T>>) {
        while !Link::is_root(curr_ptr) {
            let parent_ptr = Link::get_parent_ptr(curr_ptr).unwrap();
            let mut parent = unsafe { parent_ptr.read() };
            if parent.color == Color::Black {
                break;
            }

            // uncle may be null
            let uncle_ptr_opt = Link::get_sibling_ptr(parent_ptr);
            let uncle_color = Link::get_opt_link_ptr_color(uncle_ptr_opt);
            // parent is black, grandparent must exist
            let grandparent_ptr = Link::get_parent_ptr(parent_ptr).unwrap();

            match uncle_color {
                Color::Red => {
                    parent.color = Color::Black;
                    unsafe { parent_ptr.write(parent) };

                    // uncle must exist if uncle is colored red
                    let uncle_ptr = uncle_ptr_opt.unwrap();
                    let mut uncle = unsafe { uncle_ptr.read() };
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
        let mut curr_ptr = self.root?;

        loop {
            let curr_link = unsafe { curr_ptr.read() };
            match curr_link.item.cmp(item) {
                Ordering::Greater => {
                    if let Some(left_ptr) = curr_link.left {
                        curr_ptr = left_ptr;
                    } else {
                        return None;
                    }
                }
                Ordering::Less => {
                    if let Some(right_ptr) = curr_link.right {
                        curr_ptr = right_ptr;
                    } else {
                        return None;
                    }
                }
                Ordering::Equal => break,
            }
        }

        let (black_token_opt, item) = self.remove_link(curr_ptr);
        self.size -= 1;
        if let Some(black_token) = black_token_opt {
            self.rebalance_removal(black_token);
        }
        Some(item)
    }

    fn remove_link(&mut self, mut link_ptr: NonNull<Link<T>>) -> (Option<BlackToken<T>>, T) {
        let right_ptr_opt = Link::get_right_ptr(link_ptr);
        let left_ptr_opt = Link::get_left_ptr(link_ptr);

        let (removal_ptr, child_ptr_opt) = match (left_ptr_opt, right_ptr_opt) {
            (None, None) => (link_ptr, None),
            (None, Some(right_ptr)) => (link_ptr, Some(right_ptr)),
            (Some(left_ptr), None) => (link_ptr, Some(left_ptr)),
            (Some(left_ptr), Some(_)) => {
                let mut left_max_ptr = Link::get_subtree_max_link(left_ptr);
                let left_max_item = &mut unsafe { left_max_ptr.as_mut() }.item;
                let link_ptr_item = &mut unsafe { link_ptr.as_mut() }.item;
                mem::swap(left_max_item, link_ptr_item);
                (left_max_ptr, unsafe { left_max_ptr.read() }.left)
            }
        };

        let removal_link = unsafe { removal_ptr.read() };

        let removal_link_type = Link::get_link_type(removal_ptr);
        match removal_link_type {
            LinkType::Left => {
                let parent_ptr = removal_link.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.left = child_ptr_opt;
                unsafe {
                    parent_ptr.write(parent);
                };
                if let Some(child_ptr) = child_ptr_opt {
                    let mut child = unsafe { child_ptr.read() };
                    child.parent = Some(parent_ptr);
                    unsafe { child_ptr.write(child) };
                }
            }
            LinkType::Right => {
                let parent_ptr = removal_link.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.right = child_ptr_opt;
                unsafe {
                    parent_ptr.write(parent);
                };
                if let Some(child_ptr) = child_ptr_opt {
                    let mut child = unsafe { child_ptr.read() };
                    child.parent = Some(parent_ptr);
                    unsafe { child_ptr.write(child) };
                }
            }
            LinkType::Root => {
                self.root = child_ptr_opt;
                if let Some(child_ptr) = child_ptr_opt {
                    let mut child = unsafe { child_ptr.read() };
                    child.parent = None;
                    child.color = Color::Black;
                    unsafe { child_ptr.write(child) };
                }
            }
        }

        let black_token_opt = match removal_link.color {
            Color::Red => None,
            Color::Black => match child_ptr_opt {
                Some(child_ptr) => Some(BlackToken::SomeLink {
                    link_ptr: child_ptr,
                    link_type: removal_link_type,
                }),
                None => match removal_link.parent {
                    Some(parent) => Some(BlackToken::Null {
                        parent_ptr: parent,
                        link_type: removal_link_type,
                    }),
                    // removed link has no child or parent, the tree is empty
                    None => None,
                },
            },
        };

        // drop links
        let item = unsafe {
            let boxed_removal_link = Box::from_raw(removal_ptr.as_ptr());
            boxed_removal_link.item
        };

        (black_token_opt, item)
    }

    fn rebalance_removal(&mut self, mut black_token_state: BlackToken<T>) {
        loop {
            // root cannot be null, else black token should be None and never enter this function
            // if black token is some and points to root, break out of the loop
            if let BlackToken::SomeLink { link_ptr, .. } = black_token_state
                && link_ptr == self.root.unwrap()
            {
                break;
            }

            // black token cannot be on root
            let black_token_ptr_opt = match black_token_state {
                BlackToken::SomeLink { link_ptr, .. } => Some(link_ptr),
                BlackToken::Null { .. } => None,
            };
            let black_token_color = Link::get_opt_link_ptr_color(black_token_ptr_opt);
            let (parent_ptr, black_token_link_type) = match black_token_state {
                BlackToken::SomeLink {
                    link_ptr,
                    ref link_type,
                } => (Link::get_parent_ptr(link_ptr).unwrap(), link_type),
                BlackToken::Null {
                    parent_ptr,
                    ref link_type,
                } => (parent_ptr, link_type),
            };
            match black_token_color {
                Color::Red => {
                    // if black token is red, the link must exists, unwrap all the way
                    let black_token_ptr = black_token_ptr_opt.unwrap();
                    let mut black_token_link = unsafe { black_token_ptr.read() };
                    black_token_link.color = Color::Black;
                    unsafe { black_token_ptr.write(black_token_link) };
                    break;
                }
                Color::Black => {
                    // sibling must exist, because the black token node exist due to removed node
                    // being black, due to RB tree rule, all leaf nodes must have same black node
                    // height, so sibling must exist.
                    let sibling_ptr = match black_token_state {
                        BlackToken::SomeLink { link_ptr, .. } => {
                            Link::get_sibling_ptr(link_ptr).unwrap()
                        }
                        BlackToken::Null { parent_ptr, .. } => match black_token_link_type {
                            LinkType::Left => Link::get_right_ptr(parent_ptr).unwrap(),
                            LinkType::Right => Link::get_left_ptr(parent_ptr).unwrap(),
                            LinkType::Root => unreachable!("NANI???"),
                        },
                    };
                    let mut sibling = unsafe { sibling_ptr.read() };
                    match sibling.color {
                        Color::Red => {
                            match black_token_link_type {
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
                            let left_nephew_ptr_opt = Link::get_left_ptr(sibling_ptr);
                            let right_nephew_ptr_opt = Link::get_right_ptr(sibling_ptr);
                            let left_nephew_color =
                                Link::get_opt_link_ptr_color(left_nephew_ptr_opt);
                            let right_nephew_color =
                                Link::get_opt_link_ptr_color(right_nephew_ptr_opt);
                            if left_nephew_color == Color::Black
                                && right_nephew_color == Color::Black
                            {
                                sibling.color = Color::Red;
                                unsafe { sibling_ptr.write(sibling) };
                                let parent_link_type = Link::get_link_type(parent_ptr);
                                black_token_state = BlackToken::SomeLink {
                                    link_ptr: parent_ptr,
                                    link_type: parent_link_type,
                                };
                            } else {
                                // one of the nephews has to be red
                                match black_token_link_type {
                                    LinkType::Left => {
                                        if right_nephew_color == Color::Black {
                                            self.subtree_rotate_right(sibling_ptr, true);
                                            self.subtree_rotate_left(parent_ptr, true);
                                            let mut sibling = unsafe { sibling_ptr.read() };
                                            sibling.color = Color::Black;
                                            unsafe { sibling_ptr.write(sibling) };
                                        } else {
                                            self.subtree_rotate_left(parent_ptr, true);
                                            // right nephew is red so it must not be null
                                            let right_nephew_ptr = right_nephew_ptr_opt.unwrap();
                                            let mut right_nephew =
                                                unsafe { right_nephew_ptr.read() };
                                            right_nephew.color = Color::Black;
                                            unsafe { right_nephew_ptr.write(right_nephew) };
                                        }
                                    }
                                    LinkType::Right => {
                                        if left_nephew_color == Color::Black {
                                            self.subtree_rotate_left(sibling_ptr, true);
                                            self.subtree_rotate_right(parent_ptr, true);
                                            let mut sibling = unsafe { sibling_ptr.read() };
                                            sibling.color = Color::Black;
                                            unsafe { sibling_ptr.write(sibling) };
                                        } else {
                                            self.subtree_rotate_right(parent_ptr, true);
                                            // left nephew is red so it must not be null
                                            let left_nephew_ptr = left_nephew_ptr_opt.unwrap();
                                            let mut left_nephew = unsafe { left_nephew_ptr.read() };
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

    fn subtree_rotate_left(&mut self, subtree_root_ptr: NonNull<Link<T>>, swap_color: bool) {
        let subtree_root_link_type = Link::get_link_type(subtree_root_ptr);
        // self, right child should be a branch node by default, and right left child should at
        // least be a link
        // Link parent
        let right_ptr = Link::get_right_ptr(subtree_root_ptr).unwrap();
        let right_left_ptr_opt = Link::get_left_ptr(right_ptr);
        let mut subtree_root = unsafe { subtree_root_ptr.read() };
        let mut right = unsafe { right_ptr.read() };

        right.parent = subtree_root.parent;
        subtree_root.parent = Some(right_ptr);

        subtree_root.right = right_left_ptr_opt;
        right.left = Some(subtree_root_ptr);

        if swap_color {
            mem::swap(&mut right.color, &mut subtree_root.color);
        }

        match subtree_root_link_type {
            LinkType::Left => {
                let parent_ptr = right.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.left = Some(right_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Right => {
                let parent_ptr = right.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.right = Some(right_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Root => {
                self.root = Some(right_ptr);
                right.color = Color::Black;
            }
        }

        unsafe { subtree_root_ptr.write(subtree_root) };
        unsafe { right_ptr.write(right) };

        if let Some(right_left_ptr) = right_left_ptr_opt {
            let mut right_left = unsafe { right_left_ptr.read() };
            right_left.parent = Some(subtree_root_ptr);
            unsafe { right_left_ptr.write(right_left) };
        }
    }

    fn subtree_rotate_right(&mut self, subtree_root_ptr: NonNull<Link<T>>, swap_color: bool) {
        let subtree_root_link_type = Link::get_link_type(subtree_root_ptr);
        // self, left child should be a branch node by default, and left right child should at
        // least be a link
        // Link parent
        let left_ptr = Link::get_left_ptr(subtree_root_ptr).unwrap();
        let left_right_ptr_opt = Link::get_right_ptr(left_ptr);
        let mut subtree_root = unsafe { subtree_root_ptr.read() };
        let mut left = unsafe { left_ptr.read() };

        left.parent = subtree_root.parent;
        subtree_root.parent = Some(left_ptr);

        subtree_root.left = left_right_ptr_opt;
        left.right = Some(subtree_root_ptr);

        if swap_color {
            mem::swap(&mut left.color, &mut subtree_root.color);
        }

        match subtree_root_link_type {
            LinkType::Left => {
                let parent_ptr = left.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.left = Some(left_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Right => {
                let parent_ptr = left.parent.unwrap();
                let mut parent = unsafe { parent_ptr.read() };
                parent.right = Some(left_ptr);
                unsafe { parent_ptr.write(parent) };
            }
            LinkType::Root => {
                self.root = Some(left_ptr);
                left.color = Color::Black;
            }
        }

        unsafe { subtree_root_ptr.write(subtree_root) };
        unsafe { left_ptr.write(left) };

        if let Some(left_right_ptr) = left_right_ptr_opt {
            let mut left_right = unsafe { left_right_ptr.read() };
            left_right.parent = Some(subtree_root_ptr);
            unsafe { left_right_ptr.write(left_right) };
        }
    }

    pub fn contains(&self, item: &T) -> bool {
        // set root as current link
        // traverse left if current node item is smaller,
        // or traverse right if item is bigger,
        // if an equal item is found, return true
        let mut curr_ptr = match self.root {
            Some(root) => root,
            None => return false,
        };

        loop {
            let link = unsafe { curr_ptr.read() };
            match link.item.cmp(item) {
                Ordering::Greater => {
                    if let Some(left_ptr) = link.left {
                        curr_ptr = left_ptr;
                    } else {
                        return false;
                    }
                }
                Ordering::Less => {
                    if let Some(right_ptr) = link.right {
                        curr_ptr = right_ptr;
                    } else {
                        return false;
                    }
                }
                Ordering::Equal => return true,
            }
        }
    }

    pub fn min(&self) -> Option<&T> {
        let mut curr_ptr = self.root?;

        while let Some(left_ptr) = unsafe { curr_ptr.read() }.left {
            curr_ptr = left_ptr;
        }

        Some(&unsafe { curr_ptr.as_ref() }.item)
    }

    pub fn max(&self) -> Option<&T> {
        let mut curr_ptr = self.root?;

        while let Some(right_ptr) = unsafe { curr_ptr.read() }.right {
            curr_ptr = right_ptr;
        }
        Some(&unsafe { curr_ptr.as_ref() }.item)
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
            curr_link: self.root.map(|root| unsafe { root.as_ref() }),
            links: VecDeque::new(),
            post_group_links: VecDeque::new(),
            order,
        }
    }

    pub fn into_iter(self, order: TraversalOrder) -> IntoIter<T> {
        IntoIter {
            curr: None,
            ptrs: VecDeque::new(),
            post_ptrs: VecDeque::new(),
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
    curr_link: Option<&'a Link<T>>,
    links: VecDeque<&'a Link<T>>,
    post_group_links: VecDeque<(&'a Link<T>, Option<&'a Link<T>>)>,
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
        self.curr_link.map(|curr_link| {
            if let Some(left_ptr) = curr_link.left {
                self.links.push_front(unsafe { left_ptr.as_ref() });
            }
            if let Some(right_ptr) = curr_link.right {
                self.links.push_front(unsafe { right_ptr.as_ref() });
            }

            let item = &curr_link.item;
            self.curr_link = self.links.pop_back();
            item
        })
    }

    fn pre_order_next(&mut self) -> Option<&'a T> {
        self.curr_link.map(|curr_link| {
            if let Some(right_ptr) = curr_link.right {
                self.links.push_front(unsafe { right_ptr.as_ref() });
            }
            if let Some(left_ptr) = curr_link.left {
                self.links.push_front(unsafe { left_ptr.as_ref() });
            }

            let item = &curr_link.item;
            self.curr_link = self.links.pop_front();
            item
        })
    }

    fn in_order_next(&mut self) -> Option<&'a T> {
        while let Some(curr_link) = self.curr_link {
            self.links.push_front(curr_link);
            self.curr_link = curr_link.left.map(|left_ptr| unsafe { left_ptr.as_ref() })
        }

        self.links.pop_front().map(|link| {
            self.curr_link = link.right.map(|right_ptr| unsafe { right_ptr.as_ref() });
            &link.item
        })
    }

    fn post_order_next(&mut self) -> Option<&'a T> {
        loop {
            while let Some(curr_link) = self.curr_link {
                let right_link = curr_link
                    .right
                    .map(|right_ptr| unsafe { right_ptr.as_ref() });
                self.post_group_links.push_front((curr_link, right_link));
                self.curr_link = curr_link.left.map(|left_ptr| unsafe { left_ptr.as_ref() });
            }

            let post_link = self.post_group_links.pop_front()?;
            match post_link.1 {
                Some(right_link) => {
                    self.post_group_links.push_front((post_link.0, None));
                    self.curr_link = Some(right_link)
                }
                None => return Some(&post_link.0.item),
            };
        }
    }
}

type IntoIterPostOrderLink<T> = (NonNull<Link<T>>, Option<NonNull<Link<T>>>);
pub struct IntoIter<T> {
    // own the tree so it can be dropped later
    curr: Option<NonNull<Link<T>>>,
    ptrs: VecDeque<NonNull<Link<T>>>,
    // post-order iterator uses post_nodes
    // within a VecDeque item, the first tuple parameter stores
    // the node, and seocnd parameter stores unprocessed right child
    post_ptrs: VecDeque<IntoIterPostOrderLink<T>>,
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
        self.curr.map(|curr_ptr| {
            let curr_link = unsafe { curr_ptr.read() };
            if let Some(left_ptr) = curr_link.left {
                self.ptrs.push_front(left_ptr);
            }
            if let Some(right_ptr) = curr_link.right {
                self.ptrs.push_front(right_ptr);
            }

            let item = curr_link.item;
            self.curr = self.ptrs.pop_back();
            item
        })
    }

    fn pre_order_next(&mut self) -> Option<T> {
        self.curr.map(|curr_ptr| {
            let curr_link = unsafe { curr_ptr.read() };
            if let Some(right_ptr) = curr_link.right {
                self.ptrs.push_front(right_ptr);
            }
            if let Some(left_ptr) = curr_link.left {
                self.ptrs.push_front(left_ptr);
            }

            let item = curr_link.item;
            self.curr = self.ptrs.pop_front();
            item
        })
    }

    fn in_order_next(&mut self) -> Option<T> {
        while let Some(curr_ptr) = self.curr {
            self.ptrs.push_front(curr_ptr);
            self.curr = unsafe { curr_ptr.read() }.left;
        }

        self.ptrs.pop_front().map(|ptr| {
            let link = unsafe { ptr.read() };
            self.curr = link.right;
            link.item
        })
    }

    fn post_order_next(&mut self) -> Option<T> {
        loop {
            while let Some(curr_ptr) = self.curr {
                let curr_link = unsafe { curr_ptr.read() };
                let right_ptr = curr_link.right;
                self.post_ptrs.push_front((curr_ptr, right_ptr));
                self.curr = curr_link.left;
            }

            let post_link = self.post_ptrs.pop_front()?;
            match post_link.1 {
                Some(right_ptr) => {
                    self.post_ptrs.push_front((post_link.0, None));
                    self.curr = Some(right_ptr)
                }
                None => return Some(unsafe { post_link.0.read() }.item),
            };
        }
    }
}

impl<T> Drop for RedBlackTree<T> {
    fn drop(&mut self) {
        let mut nodes = match self.root {
            Some(root) => vec![root],
            None => return,
        };

        while let Some(ptr) = nodes.pop() {
            let link = unsafe { Box::from_raw(ptr.as_ptr()) };
            if let Some(left_ptr) = link.left {
                nodes.push(left_ptr);
            }
            if let Some(right_ptr) = link.right {
                nodes.push(right_ptr);
            }
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
        let root = match tree.root {
            Some(root) => root,
            None => return,
        };
        let mut queue = vec![(root, min_val, max_val)];

        while let Some(queue_item) = queue.pop() {
            let link_ptr = queue_item.0;
            let min_val = queue_item.1;
            let max_val = queue_item.2;

            let link = unsafe { link_ptr.read() };

            match (min_val, max_val) {
                (None, None) => {}
                (None, Some(max)) => assert!(link.item < max),
                (Some(min), None) => assert!(link.item > min),
                (Some(min), Some(max)) => assert!(link.item > min && link.item < max),
            }

            if let Some(left_ptr) = link.left {
                queue.push((
                    left_ptr,
                    min_val,
                    Some(max_val.map_or(link.item, |val| min(val, link.item))),
                ))
            }
            if let Some(right_ptr) = link.right {
                queue.push((
                    right_ptr,
                    Some(min_val.map_or(link.item, |val| max(val, link.item))),
                    max_val,
                ))
            }
        }
    }

    fn validate_rbt<T: Debug>(tree: &RedBlackTree<T>) {
        let root_ptr = match tree.root {
            Some(root) => root,
            None => return,
        };

        let root = unsafe { root_ptr.read() };
        assert_eq!(root.color, Color::Black);

        let mut queue: Vec<NonNull<Link<T>>> = Vec::new();
        queue.push(root_ptr);

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
            if let Some(left_ptr) = link.left {
                if link.color == Color::Red {
                    assert_eq!(unsafe { left_ptr.read() }.color, Color::Black);
                }
                queue.push(left_ptr);
            }
            if let Some(right_ptr) = link.right {
                if link.color == Color::Red {
                    assert_eq!(unsafe { right_ptr.read() }.color, Color::Black);
                }
                queue.push(right_ptr);
            }
            if link.left.is_none() && link.right.is_none() {
                leaf_heights.insert(*black_link_heights.get(&link_ptr).unwrap());
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
        let tree: RedBlackTree<i32> = new_compact_tree(true);
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
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
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
            validate_order(&tree, &expected_orders[usize::try_from(i - 1).unwrap()]);
        }
    }
}
