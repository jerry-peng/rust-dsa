use std::{alloc, boxed, marker, ptr};

#[derive(Debug, PartialEq)]
pub struct SinglyLinkedList<T> {
    head: *mut Node<T>,
}

#[derive(Debug, PartialEq)]
struct Node<T> {
    item: T,
    next: *mut Node<T>,
}

impl<T> SinglyLinkedList<T> {
    pub fn new() -> SinglyLinkedList<T> {
        SinglyLinkedList {
            head: ptr::null_mut(),
        }
    }

    fn alloc_node() -> ptr::NonNull<Node<T>> {
        // create memory layout for a single node
        let layout = alloc::Layout::new::<Node<T>>();
        // allocate memory
        let raw_ptr = unsafe { alloc::alloc(layout) };
        // if memory allocation fails, signal error
        if raw_ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }
        // create non-null pointer
        unsafe { ptr::NonNull::new_unchecked(raw_ptr as *mut Node<T>) }
    }

    pub fn peek(&self) -> Option<&T> {
        let head = unsafe { self.head.as_ref() };
        head.map(|node| &node.item)
    }

    pub fn push(&mut self, item: T) {
        // allocate memory for new node
        let new_node: ptr::NonNull<Node<T>> = SinglyLinkedList::alloc_node();
        // write data to new node
        unsafe {
            new_node.write(Node {
                item,
                next: self.head,
            });
        }
        // assign head to new node
        self.head = new_node.as_ptr();
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.head.is_null() {
            None
        } else {
            let boxed_head = unsafe { boxed::Box::from_raw(self.head) };
            self.head = boxed_head.next;
            Some(boxed_head.item)
        }
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head,
            phantom: marker::PhantomData,
        }
    }

    pub fn iter_mut(&self) -> IterMut<T> {
        IterMut {
            next: self.head,
            phantom: marker::PhantomData,
        }
    }
}

impl<T> Default for SinglyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, T> {
    next: *const Node<T>,
    phantom: marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let next = unsafe { self.next.as_ref() };
        next.map(|node| {
            self.next = node.next;
            &node.item
        })
    }
}

pub struct IterMut<'a, T> {
    next: *mut Node<T>,
    phantom: marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let next = unsafe { self.next.as_mut() };
        next.map(|node| {
            self.next = node.next;
            &mut node.item
        })
    }
}

impl<T> IntoIterator for SinglyLinkedList<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

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
        assert_eq!(
            SinglyLinkedList::<u32>::new(),
            SinglyLinkedList {
                head: ptr::null_mut()
            }
        )
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
