//! Singly linked list implemented with safe rust

type Link<T> = Option<Box<Node<T>>>;

#[derive(Debug, PartialEq)]
pub struct SinglyLinkedList<T> {
    head: Link<T>,
}

#[derive(Debug, PartialEq)]
struct Node<T> {
    item: T,
    next: Link<T>,
}

impl<T> SinglyLinkedList<T> {
    /// Create new empty singly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::singly_linked_list_safe::SinglyLinkedList;
    /// let list = SinglyLinkedList::<u8>::new();
    /// assert_eq!(list.peek(), None);
    /// ```
    pub fn new() -> SinglyLinkedList<T> {
        SinglyLinkedList { head: None }
    }

    /// Peek an item in singly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::singly_linked_list_safe::SinglyLinkedList;
    /// let mut list = SinglyLinkedList::<u8>::new();
    /// assert_eq!(list.peek(), None);
    /// list.push(2);
    /// assert_eq!(list.peek(), Some(&2));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|x| &x.item)
    }

    /// Push an item to singly linked list
    ///
    /// * `item`: item to push
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::singly_linked_list_safe::SinglyLinkedList;
    /// let mut list = SinglyLinkedList::<u8>::new();
    /// assert_eq!(list.peek(), None);
    /// list.push(2);
    /// assert_eq!(list.peek(), Some(&2));
    /// ```
    pub fn push(&mut self, item: T) {
        self.head = Some(Box::new(Node {
            item,
            next: self.head.take(),
        }));
    }

    /// Pop an item to singly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::singly_linked_list_safe::SinglyLinkedList;
    /// let mut list = SinglyLinkedList::<u8>::new();
    /// list.push(2);
    /// assert_eq!(list.peek(), Some(&2));
    /// assert_eq!(list.pop(), Some(2));
    /// assert_eq!(list.peek(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        match self.head.take() {
            None => None,
            Some(boxed_node) => {
                self.head = boxed_node.next;
                Some(boxed_node.item)
            }
        }
    }

    /// Iterate singly linked list immutably
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::singly_linked_list_safe::SinglyLinkedList;
    /// let mut list = SinglyLinkedList::<u8>::new();
    /// list.push(2);
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_deref(),
        }
    }

    /// Iterate singly linked list immutably
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::singly_linked_list_safe::SinglyLinkedList;
    /// let mut list = SinglyLinkedList::<u8>::new();
    /// list.push(2);
    /// let mut iter_mut = list.iter_mut();
    /// let item = iter_mut.next().unwrap();
    /// *item += 2;
    /// assert_eq!(list.peek(), Some(&4));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            next: self.head.as_deref_mut(),
        }
    }
}

impl<T> Default for SinglyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_deref();
            &node.item
        })
    }
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_deref_mut();
            &mut node.item
        })
    }
}

impl<T> IntoIterator for SinglyLinkedList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Iterate into singly linked list
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::singly_linked_list_safe::SinglyLinkedList;
    /// let mut list = SinglyLinkedList::<u8>::new();
    /// list.push(2);
    /// let mut iter_mut = list.into_iter();
    /// assert_eq!(iter_mut.next(), Some(2));
    /// assert_eq!(iter_mut.next(), None);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter { list: self }
    }
}

pub struct IntoIter<T> {
    list: SinglyLinkedList<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop()
    }
}

impl<T> Drop for SinglyLinkedList<T> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        // new()
        assert_eq!(
            SinglyLinkedList::<u32>::new(),
            SinglyLinkedList { head: None }
        );
        // default()
        assert_eq!(
            SinglyLinkedList::<u32>::default(),
            SinglyLinkedList { head: None }
        );
    }

    #[test]
    fn test_push_peek() {
        let mut list = SinglyLinkedList::<String>::new();
        assert_eq!(list.peek(), None);
        list.push("Hello".to_string());
        assert_eq!(list.peek(), Some(&"Hello".to_string()));
        list.push("World".to_string());
        assert_eq!(list.peek(), Some(&"World".to_string()));
    }

    #[test]
    fn test_pop_peek() {
        let mut list = SinglyLinkedList::<usize>::new();
        assert_eq!(list.pop(), None);

        // push items
        for i in 1..=5 {
            list.push(i);
        }

        // peek and pop items
        for i in (1..=5).rev() {
            assert_eq!(list.peek(), Some(&i));
            assert_eq!(list.pop(), Some(i));
        }
        assert_eq!(list.peek(), None);
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn test_iter() {
        // iter empty
        let mut list = SinglyLinkedList::<usize>::new();
        let mut iter = list.iter();
        assert_eq!(iter.next(), None);

        // iter_mut empty
        let mut iter_mut = list.iter_mut();
        assert_eq!(iter_mut.next(), None);

        // iter non-empty
        for i in 1..=5 {
            list.push(i);
        }
        let mut iter = list.iter();
        for i in (1..=5).rev() {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        // iter_mut non-empty
        let mut iter_mut = list.iter_mut();
        for _i in 1..=5 {
            let item = iter_mut.next().unwrap();
            *item += 3;
        }

        // verify iter_mut change
        let mut iter = list.iter();
        for i in (4..=8).rev() {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        // into_iter non-empty
        let mut into_iter = list.into_iter();
        for i in (4..=8).rev() {
            assert_eq!(into_iter.next(), Some(i));
        }
        assert_eq!(into_iter.next(), None);

        // into_iter empty
        let list = SinglyLinkedList::<usize>::new();
        let mut into_iter = list.into_iter();
        assert_eq!(into_iter.next(), None);
    }
}
