use crate::doubly_linked_list_unsafe::DoublyLinkedList;

pub struct Queue<T> {
    list: DoublyLinkedList<T>,
}

impl<T> Queue<T> {
    /// Create new empty queue
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::queue::Queue;
    /// let queue = Queue::<usize>::new();
    /// assert_eq!(queue.peek(), None);
    /// ```
    pub fn new() -> Queue<T> {
        Queue {
            list: DoublyLinkedList::<T>::new(),
        }
    }

    /// Get length of queue
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::queue::Queue;
    /// let mut queue = Queue::new();
    /// assert_eq!(queue.len(), 0);
    /// queue.push(1);
    /// assert_eq!(queue.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.list.len()
    }

    /// Get whether queue is empty
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::queue::Queue;
    /// let mut queue = Queue::new();
    /// assert!(queue.is_empty());
    /// queue.push(1);
    /// assert!(!queue.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Push item to queue
    ///
    /// * `item`: item to push
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::queue::Queue;
    /// let mut queue = Queue::new();
    /// assert_eq!(queue.peek(), None);
    /// queue.push(1);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn push(&mut self, item: T) {
        self.list.push_front(item);
    }

    /// Pop item from queue
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::queue::Queue;
    /// let mut queue = Queue::new();
    /// queue.push(1);
    /// queue.push(2);
    /// assert_eq!(queue.peek(), Some(&1));
    /// assert_eq!(queue.pop(), Some(1));
    /// assert_eq!(queue.peek(), Some(&2));
    /// assert_eq!(queue.pop(), Some(2));
    /// assert_eq!(queue.peek(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.list.pop_back()
    }

    /// Peek item on queue
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::queue::Queue;
    /// let mut queue = Queue::new();
    /// assert_eq!(queue.peek(), None);
    /// queue.push(1);
    /// assert_eq!(queue.peek(), Some(&1));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.list.peek_back()
    }
}

impl<T> Default for Queue<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_ops() {
        // test empty queue
        let queue = Queue::<usize>::default();
        assert_eq!(queue.peek(), None);
        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
        let mut queue = Queue::<usize>::new();
        assert_eq!(queue.peek(), None);
        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());

        // test push
        for i in 1..=5 {
            queue.push(i);
            assert_eq!(queue.peek(), Some(&1));
            assert_eq!(queue.len(), i);
            assert!(!queue.is_empty());
        }

        // test pop
        for i in 1..=4 {
            assert_eq!(queue.peek(), Some(&(i)));
            assert_eq!(queue.pop(), Some(i));
            assert_eq!(queue.len(), 5 - i);
            assert!(!queue.is_empty());
        }

        // test empty queue again
        assert_eq!(queue.peek(), Some(&5));
        assert_eq!(queue.pop(), Some(5));
        assert_eq!(queue.peek(), None);
        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
    }
}
