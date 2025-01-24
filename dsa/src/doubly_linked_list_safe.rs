//! Doubly linked list implemented with safe rust

use std::cell::{Ref, RefCell, RefMut};
use std::rc::{Rc, Weak};

type StrongLink<T> = Option<Rc<RefCell<Node<T>>>>;
type WeakLink<T> = Option<Weak<RefCell<Node<T>>>>;

#[derive(Debug, PartialEq)]
pub struct DoublyLinkedList<T> {
    head: StrongLink<T>,
    tail: StrongLink<T>,
}

#[derive(Debug)]
struct Node<T> {
    item: T,
    next: StrongLink<T>,
    // use weak reference counter to prevent reference cycles
    prev: WeakLink<T>,
}

impl<T> Node<T> {
    fn new(item: T) -> Rc<RefCell<Node<T>>> {
        Rc::new(RefCell::new(Node {
            item,
            next: None,
            prev: None,
        }))
    }
}

impl<T> PartialEq for Node<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        // `prev` is weak reference counter and does not implement PartialEq.
        // Since each node can at most be one other node's `next`, we can
        // disregard `prev` equality.
        self.item == other.item && self.next == other.next
    }
}

impl<T> DoublyLinkedList<T> {
    /// Create new empty doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let list = DoublyLinkedList::<u8>::new();
    /// assert!(list.peek_front().is_none());
    /// ```
    pub fn new() -> DoublyLinkedList<T> {
        DoublyLinkedList {
            head: None,
            tail: None,
        }
    }

    /// Push an item to front of doubly linked list
    ///
    /// * `item`: item to push
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert!(list.peek_front().is_none());
    /// list.push_front(2);
    /// assert_eq!(*list.peek_front().unwrap(), 2);
    /// ```
    pub fn push_front(&mut self, item: T) {
        let new_head = Node::new(item);
        match self.head.take() {
            // if head is Some, link new node as head's prev, and reassign head to new node.
            Some(old_head) => {
                old_head.borrow_mut().prev = Some(Rc::downgrade(&new_head));
                new_head.borrow_mut().next = Some(old_head);
                self.head = Some(new_head.clone());
            }
            // if head is None, linked list is empty, so assign both head and tail to new node.
            None => {
                self.head = Some(new_head.clone());
                self.tail = Some(new_head.clone());
            }
        }
    }

    /// Push an item to back of doubly linked list
    ///
    /// * `item`: item to push
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert!(list.peek_back().is_none());
    /// list.push_back(2);
    /// assert_eq!(*list.peek_back().unwrap(), 2);
    /// ```
    pub fn push_back(&mut self, item: T) {
        let new_head = Node::new(item);
        match self.tail.take() {
            // if tail is Some, link new node as tail's next, and reassign tail to new node.
            Some(old_tail) => {
                old_tail.borrow_mut().next = Some(new_head.clone());
                new_head.borrow_mut().prev = Some(Rc::downgrade(&old_tail));
                self.tail = Some(new_head.clone());
            }
            // if tail is None, linked list is empty, so assign both head and tail to new node.
            None => {
                self.head = Some(new_head.clone());
                self.tail = Some(new_head.clone());
            }
        }
    }

    /// Peek item at front of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert!(list.peek_front().is_none());
    /// list.push_front(2);
    /// assert_eq!(*list.peek_front().unwrap(), 2);
    /// ```
    pub fn peek_front(&self) -> Option<Ref<T>> {
        self.head
            .as_ref()
            .map(|node| Ref::map(node.borrow(), |x| &x.item))
    }

    /// Peek item at back of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// assert!(list.peek_back().is_none());
    /// list.push_back(2);
    /// assert_eq!(*list.peek_back().unwrap(), 2);
    /// ```
    pub fn peek_back(&self) -> Option<Ref<T>> {
        self.tail
            .as_ref()
            .map(|node| Ref::map(node.borrow(), |x| &x.item))
    }

    /// Pop item at front of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// list.push_front(2);
    /// assert_eq!(*list.peek_front().unwrap(), 2);
    /// assert_eq!(list.pop_front().unwrap(), 2);
    /// assert!(list.peek_front().is_none());
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        // since head will be reassigned later, we can unlink head using `take()`
        self.head.take().map(|old_head| {
            match old_head.borrow_mut().next.take() {
                // if head's next node is Some, unlink head node, and reassign head to next node
                Some(new_head) => {
                    new_head.borrow_mut().prev.take();
                    self.head = Some(new_head);
                }
                // if head's next node is None, the linked list is empty, unlink tail as well
                None => {
                    self.tail.take();
                }
            }
            // the popped node should only be referenced by the unlinked old head, so we can unwrap
            // inner node
            Rc::try_unwrap(old_head).ok().unwrap().into_inner().item
        })
    }

    /// Pop item at back of doubly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// list.push_back(2);
    /// assert_eq!(*list.peek_back().unwrap(), 2);
    /// assert_eq!(list.pop_back().unwrap(), 2);
    /// assert!(list.peek_back().is_none());
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        // since tail will be reassigned later, we can unlink tail using `take()`
        self.tail.take().map(|old_tail| {
            match old_tail.borrow_mut().prev.take() {
                // if tail's prev node is Some, unlink tail node, and reassign tail to prev node
                Some(new_tail) => {
                    new_tail.upgrade().unwrap().borrow_mut().next.take();
                    self.tail = new_tail.upgrade();
                }
                // if tail's prev node is None, the linked list is empty, unlink tail as well
                None => {
                    self.head.take();
                }
            }
            Rc::try_unwrap(old_tail).ok().unwrap().into_inner().item
        })
    }

    /// Iterate doubly linked list immutably or mutably
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// list.push_back(1);
    /// list.push_back(2);
    /// list.push_back(3);
    /// let mut iter = list.iter();
    /// assert_eq!(*iter.next().unwrap().borrow(), 1);
    /// // mutable borrows are placed in a block because internally implementation
    /// // of iterator uses borrow to check if iterator is exhausted, and mutable
    /// // borrows must be dropped to prevent runtime borrow checker error
    /// {
    ///     // Need separate statements for unwrap() and borrow_mut()
    ///     // so that unwrapped value lives long enough.
    ///     let mut item_ref = iter.next().unwrap();
    ///     let mut item = item_ref.borrow_mut();
    ///     *item += 2;
    ///     assert_eq!(*item, 4);
    /// }
    /// assert_eq!(*iter.next_back().unwrap().borrow(), 3);
    /// assert!(iter.next().is_none());
    /// assert!(iter.next_back().is_none());
    /// ```
    pub fn iter(&self) -> Iter<T>
    where
        T: PartialEq,
    {
        Iter {
            next_front: self.head.clone(),
            next_back: self.tail.clone(),
        }
    }
}

impl<T> Default for DoublyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
/// Wrapper for iterator's return type.
///
/// * `node`: Reference counter of RefCell-boxed node
pub struct IterRef<T> {
    node: Rc<RefCell<Node<T>>>,
}

impl<T> IterRef<T> {
    /// helper function to borrow immutable reference to node's item
    pub fn borrow(&self) -> Ref<'_, T> {
        Ref::map(self.node.borrow(), |node| &node.item)
    }
    /// helper function to borrow mutable reference to node's item
    pub fn borrow_mut(&mut self) -> RefMut<'_, T> {
        RefMut::map(self.node.borrow_mut(), |node| &mut node.item)
    }
}

pub struct Iter<T>
where
    T: PartialEq,
{
    next_front: StrongLink<T>,
    next_back: StrongLink<T>,
}

impl<T> Iterator for Iter<T>
where
    T: PartialEq,
{
    // On the topic of iterator data and return type:
    //
    // Ideally we want to return reference to inner item within node, but one limitation is that
    // iterator's output type cannot reference the iterator itself since input/output lifetime
    // differs in Iterator::next(). This means we can either return owned value or reference
    // bounded to lifetime of another value.
    //
    // Returning owned generic T is not ideal as we would need to clone it, so that leaves us with
    // returning reference. To get reference to value boxed by RefCell, we can only get Ref which
    // has lifetime bounded to RefCell itself.
    //
    // Iterator cannot store Rc<RefCell<Node<T>>>, because having it is an owned value with no
    // lifetime connection to output lifetime, so we could likely need to use Ref<'a, Node<T>>.
    //
    // However, there is limitation to storing Ref in iterator; borrows from Ref does not keep
    // lifetime of the RefCell, but from Ref itself, so chaining Ref borrows will result in
    // ownership errors.
    //
    // The only solution is to return a clone of Rc<RefCell<Node<T>>>. To make it easier for
    // downstream to borrow, we can wrap return in a IterRef type that implements helper borrow
    // functions.
    //
    // This implementation has major flaw, which is RefCell allows interior mutability, so returned
    // value allows mutation, and borrow checking is enforced at runtime instead of at compile time.
    // There's also issue with usage ergonomics when borrowing iterator output mutably; as the
    // `next()` call cannot be in the same statement as `borrow_mut()` or the compiler will
    // complain about value borrowed cannot live long enough... They must be in separate
    // statements.
    //
    // The unsafe version of doubly linked list implementation uses raw pointers and unsafe Rust to
    // achieve correct behavior of iterators.
    //
    // Sources:
    // - https://stackoverflow.com/questions/66279395/how-to-implement-iterator-for-a-rcrefcellt-chain
    // - https://stackoverflow.com/questions/74902054/iterator-for-a-linked-list-in-rust
    // - https://rust-unofficial.github.io/too-many-lists/fourth-iteration.html
    type Item = IterRef<T>;

    fn next(&mut self) -> Option<Self::Item> {
        match (self.next_front.clone(), self.next_back.clone()) {
            // if iterator's `next_front` or `next_back` is None, iterator is exhausted, return None
            (None, None) | (Some(_), None) | (None, Some(_)) => return None,
            // Otherwise, if `next-front` is `next_back`'s next node, iterator is exhausted, return
            // None.
            // The logic could be simplified if the linked list length is tracked, but I want to
            // learn Rc/RefCell so we are doing it the hard way. Length tracking is implemented in
            // unsafe version of doubly linked list.
            (Some(next_front_ref), Some(next_back_ref)) => {
                if next_back_ref.borrow().next == Some(next_front_ref) {
                    return None;
                }
            }
        };

        // if `next_front` is not None, `next_front` assign next node reference counter to
        // `next_front`, and return ItemRef containing reference counter to the old `next_front`
        self.next_front.take().map(|old_next_front| {
            self.next_front = old_next_front.borrow().next.clone();
            IterRef {
                node: old_next_front,
            }
        })
    }
}

impl<T> DoubleEndedIterator for Iter<T>
where
    T: PartialEq,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        match (self.next_front.clone(), self.next_back.clone()) {
            // if iterator's `next_front` or `next_back` is None, iterator is exhausted, return None
            (None, None) | (Some(_), None) | (None, Some(_)) => return None,
            // Otherwise, if `next-front` is `next_back`'s next node, iterator is exhausted, return
            // None.
            // For explanation on why we don't track length of linked instead to simplify logic
            // below, read comment of `Iterator::next()`.
            (Some(next_front_ref), Some(next_back_ref)) => {
                if next_back_ref.borrow().next == Some(next_front_ref) {
                    return None;
                }
            }
        };

        // if `next_back` is not None, `next_back` assign previous node reference counter to
        // `next_back`, and return ItemRef containing reference counter to the old `next_back`
        self.next_back.take().map(|old_next_back| {
            self.next_back = old_next_back
                .borrow()
                .prev
                .as_ref()
                .map(|new_node| new_node.upgrade().unwrap());
            IterRef {
                node: old_next_back,
            }
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
    /// use dsa::doubly_linked_list_safe::DoublyLinkedList;
    /// let mut list = DoublyLinkedList::<u8>::new();
    /// list.push_back(1);
    /// list.push_back(2);
    /// list.push_back(3);
    /// let mut iter = list.into_iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next_back(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next_back(), None);
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
                tail: None
            }
        );
        // default()
        assert_eq!(
            DoublyLinkedList::<usize>::default(),
            DoublyLinkedList {
                head: None,
                tail: None
            }
        );
    }

    #[test]
    fn test_push_front_peek() {
        let mut list = DoublyLinkedList::<String>::new();
        assert!(list.peek_front().is_none());
        list.push_front("Hello".to_string());
        assert_eq!(*list.peek_front().unwrap(), "Hello".to_string());
        list.push_front("World".to_string());
        assert_eq!(*list.peek_front().unwrap(), "World".to_string());
    }

    #[test]
    fn test_push_back_peek() {
        let mut list = DoublyLinkedList::<String>::new();
        assert!(list.peek_back().is_none());
        list.push_back("Hello".to_string());
        assert_eq!(*list.peek_back().unwrap(), "Hello".to_string());
        list.push_back("World".to_string());
        assert_eq!(*list.peek_back().unwrap(), "World".to_string());
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
            assert_eq!(*list.peek_front().unwrap(), i);
            assert_eq!(list.pop_front(), Some(i));
        }
        assert!(list.peek_front().is_none());
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
            assert_eq!(*list.peek_back().unwrap(), i);
            assert_eq!(list.pop_back(), Some(i));
        }
        assert!(list.peek_back().is_none());
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
        assert!(list.peek_front().is_none());
        assert!(list.peek_back().is_none());

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
        assert!(list.peek_front().is_none());
        assert!(list.peek_back().is_none());

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
        assert!(list.peek_front().is_none());
        assert!(list.peek_back().is_none());
    }

    #[test]
    fn test_immutable_iter() {
        // test empty
        let mut list = DoublyLinkedList::<usize>::new();
        let mut iter = list.iter();
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // non-empty
        for i in 1..=5 {
            list.push_front(i);
        }

        // test next()
        let mut iter = list.iter();
        for i in (1..=5).rev() {
            assert_eq!(*iter.next().unwrap().borrow(), i);
        }
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // test next_back()
        let mut iter = list.iter();
        for i in 1..=5 {
            assert_eq!(*iter.next_back().unwrap().borrow(), i);
        }
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // test combination of next()/next_back()
        let mut iter = list.iter();
        assert_eq!(*iter.next_back().unwrap().borrow(), 1);
        assert_eq!(*iter.next().unwrap().borrow(), 5);
        assert_eq!(*iter.next().unwrap().borrow(), 4);
        assert_eq!(*iter.next_back().unwrap().borrow(), 2);
        assert_eq!(*iter.next_back().unwrap().borrow(), 3);
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn test_mutable_iter() {
        // test empty
        let mut list = DoublyLinkedList::<usize>::new();
        let mut iter = list.iter();
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // non-empty
        for i in 1..=5 {
            list.push_front(i);
        }

        // test next()
        let mut iter = list.iter();
        for i in (1..=5).rev() {
            assert_eq!(*iter.next().unwrap().borrow_mut(), i);
        }
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // test next_back()
        let mut iter = list.iter();
        for i in 1..=5 {
            assert_eq!(*iter.next_back().unwrap().borrow_mut(), i);
        }
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // test combination of next()/next_back()
        let mut iter = list.iter();
        assert_eq!(*iter.next_back().unwrap().borrow_mut(), 1);
        assert_eq!(*iter.next().unwrap().borrow_mut(), 5);
        assert_eq!(*iter.next().unwrap().borrow_mut(), 4);
        assert_eq!(*iter.next_back().unwrap().borrow_mut(), 2);
        assert_eq!(*iter.next_back().unwrap().borrow_mut(), 3);
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // test next() mutation
        let mut iter = list.iter();
        for _ in 1..=5 {
            *iter.next().unwrap().borrow_mut() += 1;
        }
        let mut iter = list.iter();
        for i in 1..=5 {
            assert_eq!(*iter.next_back().unwrap().borrow(), i + 1);
        }

        // test next_back() mutation
        let mut iter = list.iter();
        for _ in 1..=5 {
            *iter.next_back().unwrap().borrow_mut() += 1;
        }
        let mut iter = list.iter();
        for i in 1..=5 {
            assert_eq!(*iter.next_back().unwrap().borrow(), i + 2);
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
