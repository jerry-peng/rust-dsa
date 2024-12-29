//! Doubly linked list implemented with unsafe rust
//!
use std::alloc::{self, alloc, Layout};
use std::boxed::Box;
use std::ptr::NonNull;

type Link<T> = Option<NonNull<Node<T>>>;

#[derive(Debug, PartialEq)]
pub struct DoublyLinkedList<T> {
    head: Link<T>,
    tail: Link<T>,
    len: usize,
}

struct Node<T> {
    item: T,
    next: Link<T>,
    prev: Link<T>,
}

impl<T> Node<T> {
    fn new(item: T) -> Node<T> {
        Node {
            item,
            next: None,
            prev: None,
        }
    }

    fn alloc(node: Node<T>) -> NonNull<Node<T>> {
        // create memory layout for a single node
        let layout = Layout::new::<Node<T>>();
        // allocate memory
        let raw_ptr = unsafe { alloc(layout) };
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

impl<T> DoublyLinkedList<T> {
    /// Create new empty doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let list = DoublyLinkedList::<u8>::new();
    /// assert_eq!(list.peek_front(), None);
    /// ```
    pub fn new() -> DoublyLinkedList<T> {
        DoublyLinkedList {
            head: None,
            tail: None,
            len: 0,
        }
    }

    /// Get length of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert_eq!(list.len(), 0);
    /// list.push_front(1);
    /// assert_eq!(list.len(), 1);
    /// list.push_front(2);
    /// assert_eq!(list.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Get whether doubly linked list is empty
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert_eq!(list.is_empty(), true);
    /// list.push_front(1);
    /// assert_eq!(list.is_empty(), false);
    /// list.push_front(2);
    /// assert_eq!(list.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Push an item to front of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert_eq!(list.peek_front(), None);
    /// list.push_front(2);
    /// assert_eq!(list.peek_front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, item: T) {
        let mut new_node = Node::new(item);
        match self.head.as_mut() {
            Some(head_ptr) => {
                new_node.next = Some(*head_ptr);
                let node_ptr = Node::alloc(new_node);
                unsafe { head_ptr.as_mut().prev = Some(node_ptr) };
                self.head = Some(node_ptr);
            }
            None => {
                let node_ptr = Node::alloc(new_node);
                self.head = Some(node_ptr);
                self.tail = Some(node_ptr);
            }
        }
        self.len += 1
    }

    /// Push an item to back of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert_eq!(list.peek_back(), None);
    /// list.push_back(2);
    /// assert_eq!(list.peek_back(), Some(&2));
    /// ```
    pub fn push_back(&mut self, item: T) {
        let mut new_node = Node::new(item);
        match self.tail.as_mut() {
            Some(tail_ptr) => {
                new_node.prev = Some(*tail_ptr);
                let node_ptr = Node::alloc(new_node);
                unsafe { tail_ptr.as_mut().next = Some(node_ptr) };
                self.tail = Some(node_ptr);
            }
            None => {
                let node_ptr = Node::alloc(new_node);
                self.head = Some(node_ptr);
                self.tail = Some(node_ptr);
            }
        }
        self.len += 1
    }

    /// Peek item at front of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert_eq!(list.peek_front(), None);
    /// list.push_front(2);
    /// assert_eq!(list.peek_front(), Some(&2));
    /// ```
    pub fn peek_front(&self) -> Option<&T> {
        self.head.map(|head_ptr| unsafe { &head_ptr.as_ref().item })
    }

    /// Peek item at back of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert_eq!(list.peek_back(), None);
    /// list.push_back(2);
    /// assert_eq!(list.peek_back(), Some(&2));
    /// ```
    pub fn peek_back(&self) -> Option<&T> {
        self.tail.map(|tail_ptr| unsafe { &tail_ptr.as_ref().item })
    }

    /// Pop item at front of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// list.push_front(2);
    /// assert_eq!(list.peek_front(), Some(&2));
    /// assert_eq!(list.pop_front(), Some(2));
    /// assert_eq!(list.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.map(|old_head_ptr| {
            let mut boxed_old_head: Box<Node<T>> = unsafe { Box::from_raw(old_head_ptr.as_ptr()) };
            self.head = boxed_old_head.next.take().map(|mut new_head_ptr| {
                unsafe {
                    new_head_ptr.as_mut().prev.take();
                }
                new_head_ptr
            });
            if self.head.is_none() {
                self.tail.take();
            }
            self.len -= 1;
            boxed_old_head.item
        })
    }

    /// Pop item at back of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// list.push_back(2);
    /// assert_eq!(list.peek_back(), Some(&2));
    /// assert_eq!(list.pop_back(), Some(2));
    /// assert_eq!(list.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.map(|old_tail_ptr| {
            let mut boxed_old_tail: Box<Node<T>> = unsafe { Box::from_raw(old_tail_ptr.as_ptr()) };
            self.tail = boxed_old_tail.prev.take().map(|mut new_tail_ptr| {
                unsafe {
                    new_tail_ptr.as_mut().next.take();
                }
                new_tail_ptr
            });
            if self.tail.is_none() {
                self.head.take();
            }
            self.len -= 1;
            boxed_old_tail.item
        })
    }

    /// Iterate doubly linked list immutably
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// for i in 1..=5 {
    ///     list.push_back(i);
    /// }
    /// let mut iter = list.iter();
    /// for i in 1..=2 {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// for i in (3..=5).rev() {
    ///     assert_eq!(iter.next_back(), Some(&i));
    /// }
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            next_front: self.head.map(|node_ptr| unsafe { node_ptr.as_ref() }),
            next_back: self.tail.map(|node_ptr| unsafe { node_ptr.as_ref() }),
            start: 0,
            end: isize::try_from(self.len).ok().unwrap() - 1,
        }
    }

    /// Iterate doubly linked list mutably
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// for i in 1..=5 {
    ///     list.push_back(i);
    /// }
    /// let mut iter_mut = list.iter_mut();
    /// for i in 1..=2 {
    ///     let item = iter_mut.next().unwrap();
    ///     *item += 2
    /// }
    /// for i in (3..=5).rev() {
    ///     let item = iter_mut.next_back().unwrap();
    ///     *item += 4;
    /// }
    /// let mut iter = list.iter();
    /// for i in [3, 4, 7, 8, 9] {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            next: self.head.map(|mut node_ptr| unsafe { node_ptr.as_mut() }),
            next_back: self.tail.map(|mut node_ptr| unsafe { node_ptr.as_mut() }),
            start: 0,
            end: isize::try_from(self.len).ok().unwrap() - 1,
        }
    }
}

impl<T> Default for DoublyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, T> {
    next_front: Option<&'a Node<T>>,
    next_back: Option<&'a Node<T>>,
    start: isize,
    end: isize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.end < self.start {
            return None;
        }
        self.next_front.take().map(|old_next_front| {
            self.next_front = old_next_front
                .next
                .map(|new_next_front_ptr| unsafe { new_next_front_ptr.as_ref() });
            let item = &old_next_front.item;
            self.start += 1;
            item
        })
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.end < self.start {
            return None;
        }
        self.next_back.take().map(|old_next_back| {
            self.next_back = old_next_back
                .prev
                .map(|new_next_back_ptr| unsafe { new_next_back_ptr.as_ref() });
            let item = &old_next_back.item;
            self.end -= 1;
            item
        })
    }
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
    next_back: Option<&'a mut Node<T>>,
    start: isize,
    end: isize,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.end < self.start {
            return None;
        }
        self.next.take().map(|old_next| {
            let item = &mut old_next.item;
            self.next = old_next
                .next
                .as_mut()
                .map(|new_next_ptr| unsafe { new_next_ptr.as_mut() });
            self.start += 1;
            item
        })
    }
}

impl<T> DoubleEndedIterator for IterMut<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.end < self.start {
            return None;
        }
        self.next_back.take().map(|old_next_back| {
            let item = &mut old_next_back.item;
            self.next_back = old_next_back
                .prev
                .as_mut()
                .map(|new_next_back_ptr| unsafe { new_next_back_ptr.as_mut() });
            self.end -= 1;
            item
        })
    }
}

impl<T> IntoIterator for DoublyLinkedList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Iterate into doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_unsafe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// for i in 1..=5 {
    ///     list.push_back(i);
    /// }
    /// let mut iter = list.into_iter();
    /// for i in 1..=2 {
    ///     assert_eq!(iter.next(), Some(i));
    /// }
    /// for i in (3..=5).rev() {
    ///     assert_eq!(iter.next_back(), Some(i));
    /// }
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter { list: self }
    }
}

pub struct IntoIter<T> {
    list: DoublyLinkedList<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<T> Drop for DoublyLinkedList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        // new()
        assert_eq!(
            DoublyLinkedList::<usize>::new(),
            DoublyLinkedList {
                head: None,
                tail: None,
                len: 0
            }
        );
        // default()
        assert_eq!(
            DoublyLinkedList::<usize>::default(),
            DoublyLinkedList {
                head: None,
                tail: None,
                len: 0
            }
        );
    }

    #[test]
    fn test_push_front_peek() {
        let mut list = DoublyLinkedList::<String>::new();
        assert_eq!(list.peek_front(), None);
        assert_eq!(list.len(), 0);
        assert!(list.is_empty());
        list.push_front("Hello".to_string());
        assert_eq!(list.peek_front(), Some(&"Hello".to_string()));
        assert_eq!(list.len(), 1);
        assert!(!list.is_empty());
        list.push_front("World".to_string());
        assert_eq!(list.peek_front(), Some(&"World".to_string()));
        assert_eq!(list.len(), 2);
        assert!(!list.is_empty());
    }

    #[test]
    fn test_push_back_peek() {
        let mut list = DoublyLinkedList::<String>::new();
        assert_eq!(list.peek_back(), None);
        assert_eq!(list.len(), 0);
        assert!(list.is_empty());
        list.push_back("Hello".to_string());
        assert_eq!(list.peek_back(), Some(&"Hello".to_string()));
        assert_eq!(list.len(), 1);
        assert!(!list.is_empty());
        list.push_back("World".to_string());
        assert_eq!(list.peek_back(), Some(&"World".to_string()));
        assert_eq!(list.len(), 2);
        assert!(!list.is_empty());
    }

    #[test]
    fn test_pop_front_peek() {
        let mut list = DoublyLinkedList::<usize>::new();
        assert_eq!(list.pop_front(), None);

        // push items to front
        for i in 1..=5 {
            list.push_front(i);
        }

        // peek and pop items from front
        for i in (1..=5).rev() {
            assert_eq!(list.peek_front(), Some(&i));
            assert_eq!(list.pop_front(), Some(i));
            assert_eq!(list.len(), i - 1);
        }
        assert_eq!(list.peek_front(), None);
        assert_eq!(list.pop_front(), None);
    }

    #[test]
    fn test_pop_back_peek() {
        let mut list = DoublyLinkedList::<usize>::new();
        assert_eq!(list.pop_back(), None);

        // push items to back
        for i in 1..=5 {
            list.push_back(i);
        }

        // peek and pop items from back
        for i in (1..=5).rev() {
            assert_eq!(list.peek_back(), Some(&i));
            assert_eq!(list.pop_back(), Some(i));
            assert_eq!(list.len(), i - 1);
        }
        assert_eq!(list.peek_front(), None);
        assert_eq!(list.pop_back(), None);
    }

    #[test]
    fn test_all_push_pop() {
        // test push items to front, pop all from back
        let mut list = DoublyLinkedList::<usize>::new();
        for i in 1..=5 {
            list.push_front(i);
        }
        for i in 1..=5 {
            assert_eq!(list.pop_back(), Some(i));
        }
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.pop_back(), None);
        assert_eq!(list.peek_front(), None);
        assert_eq!(list.peek_back(), None);

        // test push items to back, pop all from front
        let mut list = DoublyLinkedList::<usize>::new();
        for i in 1..=5 {
            list.push_back(i);
        }
        for i in 1..=5 {
            assert_eq!(list.pop_front(), Some(i));
        }
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.pop_back(), None);
        assert_eq!(list.peek_front(), None);
        assert_eq!(list.peek_back(), None);

        // test push items to front, pop from both front and back
        let mut list = DoublyLinkedList::<usize>::new();
        for i in 1..=10 {
            list.push_back(i);
        }
        for i in 1..=7 {
            assert_eq!(list.pop_front(), Some(i));
        }
        for i in (8..=10).rev() {
            assert_eq!(list.pop_back(), Some(i));
        }
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.pop_back(), None);
        assert_eq!(list.peek_front(), None);
        assert_eq!(list.peek_back(), None);
    }

    #[test]
    fn test_immutable_iter() {
        // test empty
        let mut list = DoublyLinkedList::<usize>::new();
        let mut iter = list.iter();
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        // non-empty
        for i in 1..=5 {
            list.push_front(i);
        }

        // test next()
        let mut iter = list.iter();
        for i in (1..=5).rev() {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        // test next_back()
        let mut iter = list.iter();
        for i in 1..=5 {
            assert_eq!(iter.next_back(), Some(&i));
        }
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        // test combination of next()/next_back()
        let mut iter = list.iter();
        assert_eq!(iter.next_back(), Some(&1));
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next_back(), Some(&2));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn test_mutable_iter() {
        // test empty
        let mut list = DoublyLinkedList::<usize>::new();
        let mut iter_mut = list.iter_mut();
        assert_eq!(iter_mut.next(), None);
        assert_eq!(iter_mut.next_back(), None);

        // non-empty
        for i in 1..=5 {
            list.push_front(i);
        }

        // test next()
        let mut iter_mut = list.iter_mut();
        for mut i in (1..=5).rev() {
            assert_eq!(iter_mut.next(), Some(&mut i));
        }
        assert_eq!(iter_mut.next(), None);
        assert_eq!(iter_mut.next_back(), None);

        // test next_back()
        let mut iter_mut = list.iter_mut();
        for mut i in 1..=5 {
            assert_eq!(iter_mut.next_back(), Some(&mut i));
        }
        assert_eq!(iter_mut.next(), None);
        assert_eq!(iter_mut.next_back(), None);

        // test combination of next()/next_back()
        let mut iter_mut = list.iter_mut();
        assert_eq!(iter_mut.next_back(), Some(&mut 1));
        assert_eq!(iter_mut.next(), Some(&mut 5));
        assert_eq!(iter_mut.next(), Some(&mut 4));
        assert_eq!(iter_mut.next_back(), Some(&mut 2));
        assert_eq!(iter_mut.next_back(), Some(&mut 3));
        assert_eq!(iter_mut.next(), None);
        assert_eq!(iter_mut.next_back(), None);

        // test next() mutation
        let mut iter = list.iter_mut();
        for _ in 1..=5 {
            *iter.next().unwrap() += 1;
        }
        let mut iter = list.iter();
        for i in 1..=5 {
            assert_eq!(iter.next_back(), Some(&(i + 1)));
        }

        // test next_back() mutation
        let mut iter_mut = list.iter_mut();
        for _ in 1..=5 {
            *iter_mut.next_back().unwrap() += 1;
        }
        let mut iter = list.iter();
        for i in 1..=5 {
            assert_eq!(iter.next_back(), Some(&(i + 2)));
        }
    }

    #[test]
    fn test_into_iter() {
        // test empty
        let list = DoublyLinkedList::<usize>::new();
        let mut into_iter = list.into_iter();
        assert!(into_iter.next().is_none());
        assert!(into_iter.next_back().is_none());

        // test non-empty next()
        let mut list = DoublyLinkedList::<usize>::new();
        for i in 1..=5 {
            list.push_front(i);
        }
        let mut into_iter = list.into_iter();
        for i in (1..=5).rev() {
            assert_eq!(into_iter.next(), Some(i));
        }
        assert!(into_iter.next().is_none());
        assert!(into_iter.next_back().is_none());

        // test non-empty next_back()
        let mut list = DoublyLinkedList::<usize>::new();
        for i in 1..=5 {
            list.push_back(i);
        }
        let mut into_iter = list.into_iter();
        for i in (1..=5).rev() {
            assert_eq!(into_iter.next_back(), Some(i));
        }
        assert!(into_iter.next().is_none());
        assert!(into_iter.next_back().is_none());

        // test combination of next()/next_back()
        let mut list = DoublyLinkedList::<usize>::new();
        for i in 1..=5 {
            list.push_front(i);
        }
        let mut into_iter = list.into_iter();
        assert_eq!(into_iter.next_back(), Some(1));
        assert_eq!(into_iter.next(), Some(5));
        assert_eq!(into_iter.next(), Some(4));
        assert_eq!(into_iter.next_back(), Some(2));
        assert_eq!(into_iter.next_back(), Some(3));
        assert!(into_iter.next().is_none());
        assert!(into_iter.next_back().is_none());
    }
}
