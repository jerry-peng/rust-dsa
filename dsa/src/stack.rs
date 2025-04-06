//! Stack implemented on top of singly linked list

use crate::singly_linked_list_safe::SinglyLinkedList;

pub struct Stack<T> {
    list: SinglyLinkedList<T>,
    len: usize,
}

impl<T> Stack<T> {
    /// Create new empty stack
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::stack::Stack;
    /// let stack = Stack::<usize>::new();
    /// assert_eq!(stack.peek(), None);
    /// ```
    pub fn new() -> Stack<T> {
        Stack {
            list: SinglyLinkedList::<T>::new(),
            len: 0,
        }
    }

    /// Get length of stack
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::stack::Stack;
    /// let mut stack = Stack::new();
    /// assert_eq!(stack.len(), 0);
    /// stack.push(1);
    /// assert_eq!(stack.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Get whether stack is empty
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::stack::Stack;
    /// let mut stack = Stack::new();
    /// assert!(stack.is_empty());
    /// stack.push(1);
    /// assert!(!stack.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Push item to stack
    ///
    /// * `item`: item to push
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::stack::Stack;
    /// let mut stack = Stack::new();
    /// assert_eq!(stack.peek(), None);
    /// stack.push(1);
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn push(&mut self, item: T) {
        self.list.push(item);
        self.len += 1;
    }

    /// Pop item from stack
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::stack::Stack;
    /// let mut stack = Stack::new();
    /// stack.push(1);
    /// stack.push(2);
    /// assert_eq!(stack.peek(), Some(&2));
    /// assert_eq!(stack.pop(), Some(2));
    /// assert_eq!(stack.peek(), Some(&1));
    /// assert_eq!(stack.pop(), Some(1));
    /// assert_eq!(stack.peek(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.len -= 1;
        self.list.pop()
    }

    /// Peek item on stack
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::stack::Stack;
    /// let mut stack = Stack::new();
    /// assert_eq!(stack.peek(), None);
    /// stack.push(1);
    /// assert_eq!(stack.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.list.peek()
    }
}

impl<T> Default for Stack<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_ops() {
        // test empty stack
        let stack = Stack::<usize>::default();
        assert_eq!(stack.peek(), None);
        assert_eq!(stack.len(), 0);
        assert!(stack.is_empty());
        let mut stack = Stack::<usize>::new();
        assert_eq!(stack.peek(), None);
        assert_eq!(stack.len(), 0);
        assert!(stack.is_empty());

        // test push
        for i in 1..=5 {
            stack.push(i);
            assert_eq!(stack.peek(), Some(&i));
            assert_eq!(stack.len(), i);
            assert!(!stack.is_empty());
        }

        // test pop
        for i in (2..=5).rev() {
            assert_eq!(stack.pop(), Some(i));
            assert_eq!(stack.peek(), Some(&(i - 1)));
            assert_eq!(stack.len(), i - 1);
            assert!(!stack.is_empty());
        }

        // test empty stack again
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.peek(), None);
        assert_eq!(stack.len(), 0);
        assert!(stack.is_empty());
    }
}
