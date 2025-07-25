//! Binary heap implementation

use std::cmp::Ordering;
use std::fmt::Debug;

#[derive(Debug, PartialEq)]
pub enum HeapType {
    Min,
    Max,
}

#[derive(Debug, PartialEq)]
/// Binary heap structure
///
/// * `items`: items
/// * `heap_type`: heap type (min/max)
pub struct BinaryHeap<T> {
    items: Vec<T>,
    heap_type: HeapType,
}

impl<T: Debug + Ord> BinaryHeap<T> {
    /// Creates new binary heap
    ///
    /// * `heap_type`: heap type (min/max)
    fn new(heap_type: HeapType) -> BinaryHeap<T> {
        BinaryHeap {
            items: Vec::new(),
            heap_type,
        }
    }

    /// Creates new binary min heap
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_min_heap();
    /// assert_eq!(heap.size(), 0);
    /// assert!(heap.is_empty());
    ///
    /// ```
    pub fn new_min_heap() -> BinaryHeap<T> {
        BinaryHeap::new(HeapType::Min)
    }

    /// Creates new binary max heap
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// assert_eq!(heap.size(), 0);
    /// assert!(heap.is_empty());
    ///
    /// ```
    pub fn new_max_heap() -> BinaryHeap<T> {
        BinaryHeap::new(HeapType::Max)
    }

    /// Get number of items stored in heap
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// assert_eq!(heap.size(), 0);
    /// heap.push(5);
    /// assert_eq!(heap.size(), 1);
    /// heap.push(4);
    /// assert_eq!(heap.size(), 2);
    /// heap.pop();
    /// assert_eq!(heap.size(), 1);
    ///
    /// ```
    pub fn size(&self) -> usize {
        self.items.len()
    }

    /// Get whether heap is empty
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// assert!(heap.is_empty());
    /// heap.push(5);
    /// assert!(!heap.is_empty());
    /// heap.pop();
    /// assert!(heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.items.len() == 0
    }

    /// Push item to heap
    ///
    /// * `item`: item to push
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// heap.push(5);
    /// assert_eq!(heap.peek(), Some(&5));
    /// heap.push(6);
    /// assert_eq!(heap.peek(), Some(&6));
    /// ```
    pub fn push(&mut self, item: T) {
        // push item to end of heap, record item index
        self.items.push(item);
        let mut curr_index = self.size() - 1;

        // if parent exists, compare and propagate pushed item up if needed
        while let Some(parent_index) = BinaryHeap::<T>::get_parent_index(curr_index) {
            // propagate item up in following conditions:
            // - for min heap, if pushed item is smaller than parent
            // - for max heap, if pushed item is larger than parent
            // otherwise, heap is valid, break out of the loop
            let curr_item = &self.items[curr_index];
            let parent = &self.items[parent_index];
            match (&self.heap_type, curr_item.cmp(parent)) {
                (HeapType::Min, Ordering::Less) | (HeapType::Max, Ordering::Greater) => {
                    self.items.swap(curr_index, parent_index);
                    curr_index = parent_index;
                }
                _ => break,
            }
        }
    }

    /// Pop item from heap
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// heap.push(5);
    /// heap.push(6);
    /// assert_eq!(heap.pop(), Some(6));
    /// assert_eq!(heap.pop(), Some(5));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        match self.size() {
            0 => None,
            1 => self.items.pop(),
            size => {
                self.items.swap(0, size - 1);
                let item = self.items.pop().unwrap();
                self.pop_reorder();
                Some(item)
            }
        }
    }

    /// Reorder heap after item pop
    fn pop_reorder(&mut self) {
        let mut curr_index = 0;

        loop {
            // based on current index, get child indices
            let (first_child_index, second_child_index) =
                BinaryHeap::<T>::get_child_indices(curr_index);

            // compare last item index to first child index;
            // - if less, no child exist
            // - if equal, only 1 child exists
            // - if more, both children exist
            // no chance of underflow, size should always be above 1 in this loop
            match (self.size() - 1).cmp(&first_child_index) {
                // child do not exist; heap reorder is complete
                Ordering::Less => break,
                // only 1 child exist; swap current index item and child item under
                // following conditions:
                // - for min heap, if current index item is greater than child item
                // - for max heap, if current index item is less than child item
                // otherwise heap reorder is complete
                Ordering::Equal => {
                    let curr_item = &self.items[curr_index];
                    let first_child = &self.items[first_child_index];

                    match (&self.heap_type, curr_item.cmp(first_child)) {
                        (HeapType::Min, Ordering::Greater) | (HeapType::Max, Ordering::Less) => {
                            self.items.swap(curr_index, first_child_index);
                            curr_index = first_child_index;
                        }
                        _ => break,
                    }
                }
                // both children exist; swap current index item and one of child items
                // under following conditions:
                // - for min heap, if current index item is greater than the smaller child item
                // - for max heap, if current index item is less than the larger child item
                Ordering::Greater => {
                    let first_child = &self.items[first_child_index];
                    let second_child = &self.items[second_child_index];

                    // get child index to swap based on heap type and comparison result between
                    // the two children
                    let child_index_to_swap = match (&self.heap_type, first_child.cmp(second_child))
                    {
                        (HeapType::Min, Ordering::Less) => first_child_index,
                        (HeapType::Min, _) => second_child_index,
                        (HeapType::Max, Ordering::Greater) => first_child_index,
                        (HeapType::Max, _) => second_child_index,
                    };

                    let curr_item = &self.items[curr_index];
                    let child_to_swap = &self.items[child_index_to_swap];

                    match (&self.heap_type, curr_item.cmp(child_to_swap)) {
                        (HeapType::Min, Ordering::Greater) | (HeapType::Max, Ordering::Less) => {
                            self.items.swap(curr_index, child_index_to_swap);
                            curr_index = child_index_to_swap
                        }
                        _ => break,
                    }
                }
            }
        }
    }

    /// Pop an item from heap then push an item in a single pass
    ///
    /// * `item`: item to push
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// assert_eq!(heap.pop_push(5), None);
    /// assert_eq!(heap.pop_push(6), Some(5));
    /// assert_eq!(heap.pop(), Some(6));
    /// assert_eq!(heap.peek(), None);
    /// ```
    pub fn pop_push(&mut self, item: T) -> Option<T> {
        match self.is_empty() {
            true => {
                self.items.push(item);
                None
            }
            false => {
                self.items.push(item);
                self.pop()
            }
        }
    }

    /// Immutable peek min/max item in heap
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// assert_eq!(heap.pop_push(5), None);
    /// assert_eq!(heap.peek(), Some(&5));
    /// assert_eq!(heap.pop_push(6), Some(5));
    /// assert_eq!(heap.peek(), Some(&6));
    /// assert_eq!(heap.pop(), Some(6));
    /// assert_eq!(heap.peek(), None);
    /// ```
    pub fn peek(&self) -> Option<&T> {
        match self.is_empty() {
            true => None,
            false => Some(&self.items[0]),
        }
    }

    /// Mutable peek min/max item in heap
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::binary_heap::BinaryHeap;
    /// let mut heap = BinaryHeap::<i32>::new_max_heap();
    /// assert_eq!(heap.pop_push(5), None);
    /// assert_eq!(heap.peek_mut(), Some(&mut 5));
    /// assert_eq!(heap.pop_push(6), Some(5));
    /// assert_eq!(heap.peek_mut(), Some(&mut 6));
    /// assert_eq!(heap.pop(), Some(6));
    /// assert_eq!(heap.peek_mut(), None);
    /// ```
    pub fn peek_mut(&mut self) -> Option<&mut T> {
        match self.is_empty() {
            true => None,
            false => Some(&mut self.items[0]),
        }
    }

    /// Get parent index;
    /// if index is 0, parent does not exist
    ///
    /// * `index`: index
    fn get_parent_index(index: usize) -> Option<usize> {
        match index {
            0 => None,
            index => Some((index - 1) / 2),
        }
    }

    /// Get child index;
    /// if index is 0, parent does not exist
    ///
    /// * `index`: index
    fn get_child_indices(index: usize) -> (usize, usize) {
        (index * 2 + 1, index * 2 + 2)
    }
}

impl<T: Debug + Ord> Default for BinaryHeap<T> {
    fn default() -> Self {
        BinaryHeap::new_max_heap()
    }
}

pub struct IntoIter<T>(BinaryHeap<T>);

impl<T: Debug + Ord> IntoIterator for BinaryHeap<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

impl<T: Debug + Ord> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{self, Value};
    use std::fs;
    use std::path;

    fn get_random_items() -> Vec<i32> {
        vec![1, 10, 2, 9, 3, 8, 4, 7, 5, 6]
    }

    fn get_ascending_items() -> Vec<i32> {
        (1..=10).collect::<Vec<i32>>()
    }

    fn get_descending_items() -> Vec<i32> {
        (1..=10).rev().collect::<Vec<i32>>()
    }

    fn get_heap_items() -> Vec<(String, Vec<i32>)> {
        vec![
            ("random".to_string(), get_random_items()),
            ("ascending".to_string(), get_ascending_items()),
            ("descending".to_string(), get_descending_items()),
        ]
    }

    fn read_json_data() -> Value {
        let json_string = fs::read_to_string(path::Path::new("./unit_test_data/binary_heap.json"))
            .expect("Unable to read file");
        serde_json::from_str(json_string.as_str()).unwrap()
    }

    fn deserialize_list(list: &Value) -> Vec<i32> {
        list.as_array()
            .unwrap()
            .iter()
            .map(|i| i32::try_from(i.as_i64().unwrap()).unwrap())
            .collect()
    }

    fn validate_heap<T: Debug + Ord>(heap: &BinaryHeap<T>) {
        let size = heap.size();
        // for each item, ensure child items are not less than parents for min heap,
        // and not greater than parents for max heap.
        for (index, item) in heap.items.iter().enumerate() {
            let (first_child_index, second_child_index) =
                BinaryHeap::<i32>::get_child_indices(index);

            if first_child_index < size {
                match &heap.heap_type {
                    HeapType::Min => assert!(item <= &heap.items[first_child_index]),
                    HeapType::Max => assert!(item >= &heap.items[first_child_index]),
                }
            }

            if second_child_index < size {
                match &heap.heap_type {
                    HeapType::Min => assert!(item <= &heap.items[second_child_index]),
                    HeapType::Max => assert!(item >= &heap.items[second_child_index]),
                }
            }
        }
    }

    #[test]
    fn test_new() {
        // min heap
        let mut heap = BinaryHeap::<usize>::new_min_heap();
        assert_eq!(
            heap,
            BinaryHeap {
                items: Vec::<usize>::new(),
                heap_type: HeapType::Min
            }
        );
        assert!(heap.is_empty());
        assert_eq!(heap.size(), 0);
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.peek_mut(), None);
        validate_heap(&heap);

        // min heap
        let mut heap = BinaryHeap::<usize>::new_max_heap();
        assert_eq!(
            heap,
            BinaryHeap {
                items: Vec::<usize>::new(),
                heap_type: HeapType::Max
            }
        );
        assert!(heap.is_empty());
        assert_eq!(heap.size(), 0);
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.peek_mut(), None);
        validate_heap(&heap);

        // default
        let mut heap = BinaryHeap::<usize>::default();
        assert_eq!(
            heap,
            BinaryHeap {
                items: Vec::<usize>::new(),
                heap_type: HeapType::Max
            }
        );
        assert!(heap.is_empty());
        assert_eq!(heap.size(), 0);
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.peek_mut(), None);
        validate_heap(&heap);
    }

    #[test]
    fn test_min_heap_push() {
        let heap_items = get_heap_items();
        let expected_heap_orders = read_json_data();
        let expected_orders = &expected_heap_orders["push"]["min"];

        // test all item orders
        for (order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_min_heap();
            for (index, item) in items.iter().enumerate() {
                // push and validate size and heap properties
                heap.push(*item);
                assert!(!heap.is_empty());
                assert_eq!(heap.size(), index + 1);
                validate_heap(&heap);

                // validate peek and orders
                let mut expected_orders = deserialize_list(&expected_orders[&order][index]);
                assert_eq!(heap.peek(), Some(&expected_orders[0]));
                assert_eq!(heap.peek_mut(), Some(&mut expected_orders[0]));
                assert_eq!(
                    heap,
                    BinaryHeap {
                        items: expected_orders,
                        heap_type: HeapType::Min
                    }
                );
            }
        }
    }

    #[test]
    fn test_max_heap_push() {
        let heap_items = get_heap_items();
        let expected_heap_orders = read_json_data();
        let expected_orders = &expected_heap_orders["push"]["max"];

        // test all item orders
        for (order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_max_heap();
            for (index, item) in items.iter().enumerate() {
                // push and validate size and heap properties
                heap.push(*item);
                assert!(!heap.is_empty());
                assert_eq!(heap.size(), index + 1);
                validate_heap(&heap);

                // validate peek and orders
                let mut expected_orders = deserialize_list(&expected_orders[&order][index]);
                assert_eq!(heap.peek(), Some(&expected_orders[0]));
                assert_eq!(heap.peek_mut(), Some(&mut expected_orders[0]));
                assert_eq!(
                    heap,
                    BinaryHeap {
                        items: expected_orders,
                        heap_type: HeapType::Max
                    }
                );
            }
        }
    }

    #[test]
    fn test_min_heap_pop() {
        let heap_items = get_heap_items();
        let expected_heap_orders = read_json_data();
        let expected_orders = &expected_heap_orders["pop"]["min"];

        // test all item orders
        for (order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_min_heap();

            // push all items
            for item in items {
                heap.push(item);
            }

            // validate each pop
            for i in 0..10 {
                // validate size
                let i_as_i32 = i32::try_from(i).unwrap();
                assert!(!heap.is_empty());
                assert_eq!(heap.size(), 10 - i);

                // pop and validate heap properties
                assert_eq!(heap.pop(), Some(i_as_i32 + 1));
                validate_heap(&heap);

                // validate peek and orders
                let mut expected_orders = deserialize_list(&expected_orders[&order][i]);
                if i != 9 {
                    assert_eq!(heap.peek(), Some(&expected_orders[0]));
                    assert_eq!(heap.peek_mut(), Some(&mut expected_orders[0]));
                } else {
                    assert_eq!(heap.peek(), None);
                    assert_eq!(heap.peek_mut(), None);
                }
                assert_eq!(
                    heap,
                    BinaryHeap {
                        items: expected_orders,
                        heap_type: HeapType::Min
                    }
                );
            }

            // validate heap is empty
            assert!(heap.is_empty());
            assert_eq!(heap.size(), 0);
            assert_eq!(heap.pop(), None);
        }
    }

    #[test]
    fn test_max_heap_pop() {
        let heap_items = get_heap_items();
        let expected_heap_orders = read_json_data();
        let expected_orders = &expected_heap_orders["pop"]["max"];

        // test all item orders
        for (order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_max_heap();

            // push all items
            for item in items {
                heap.push(item);
            }

            // validate each pop
            for i in 0..10 {
                // validate size
                let i_as_i32 = i32::try_from(i).unwrap();
                assert!(!heap.is_empty());
                assert_eq!(heap.size(), 10 - i);

                // pop and validate heap properties
                assert_eq!(heap.pop(), Some(10 - i_as_i32));
                validate_heap(&heap);

                // validate peek and orders
                let mut expected_orders = deserialize_list(&expected_orders[&order][i]);
                if i != 9 {
                    assert_eq!(heap.peek(), Some(&expected_orders[0]));
                    assert_eq!(heap.peek_mut(), Some(&mut expected_orders[0]));
                } else {
                    assert_eq!(heap.peek(), None);
                    assert_eq!(heap.peek_mut(), None);
                }
                assert_eq!(
                    heap,
                    BinaryHeap {
                        items: expected_orders,
                        heap_type: HeapType::Max
                    }
                );
            }

            // validate heap is empty
            assert!(heap.is_empty());
            assert_eq!(heap.size(), 0);
            assert_eq!(heap.pop(), None);
            validate_heap(&heap);
        }
    }

    #[test]
    fn test_empty_min_heap_pop_push() {
        let mut heap = BinaryHeap::<i32>::new_min_heap();
        assert_eq!(heap.pop_push(5), None);
        assert_eq!(
            heap,
            BinaryHeap {
                items: vec![5],
                heap_type: HeapType::Min
            }
        );
        validate_heap(&heap);
    }

    #[test]
    fn test_empty_max_heap_pop_push() {
        let mut heap = BinaryHeap::<i32>::new_max_heap();
        assert_eq!(heap.pop_push(5), None);
        assert_eq!(
            heap,
            BinaryHeap {
                items: vec![5],
                heap_type: HeapType::Max
            }
        );
        validate_heap(&heap);
    }

    #[test]
    fn test_min_heap_pop_push() {
        let heap_items = get_heap_items();
        let expected_heap_orders = read_json_data();
        let expected_orders = &expected_heap_orders["pop_push"]["min"];

        // test each item order
        for (order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_min_heap();

            // push 5 items and validate size
            for item in &items[0..5] {
                heap.push(*item);
            }
            assert!(!heap.is_empty());
            assert_eq!(heap.size(), 5);

            // pop-push rest of the items
            for index in 5..10 {
                let expected_popped_item = if index == 5 {
                    items[0..5].to_vec().iter().min().copied()
                } else {
                    Some(deserialize_list(&expected_orders[&order][index - 6])[0])
                };

                // pop-push and validate size and heap properties
                let push_item = items[index];
                assert_eq!(heap.pop_push(push_item), expected_popped_item);
                assert!(!heap.is_empty());
                assert_eq!(heap.size(), 5);
                validate_heap(&heap);

                // validate order
                let mut expected_orders = deserialize_list(&expected_orders[&order][index - 5]);
                assert_eq!(heap.peek(), Some(&expected_orders[0]));
                assert_eq!(heap.peek_mut(), Some(&mut expected_orders[0]));
                assert_eq!(
                    heap,
                    BinaryHeap {
                        items: expected_orders,
                        heap_type: HeapType::Min
                    }
                );
            }
        }
    }

    #[test]
    fn test_max_heap_pop_push() {
        let heap_items = get_heap_items();
        let expected_heap_orders = read_json_data();
        let expected_orders = &expected_heap_orders["pop_push"]["max"];

        // test each item order
        for (order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_max_heap();

            // push 5 items and validate size
            for item in &items[0..5] {
                heap.push(*item);
            }
            assert!(!heap.is_empty());
            assert_eq!(heap.size(), 5);

            // pop-push rest of the items
            for index in 5..10 {
                let expected_popped_item = if index == 5 {
                    items[0..5].to_vec().iter().max().copied()
                } else {
                    Some(deserialize_list(&expected_orders[&order][index - 6])[0])
                };

                // pop-push and validate size and heap properties
                let push_item = items[index];
                assert_eq!(heap.pop_push(push_item), expected_popped_item);
                assert!(!heap.is_empty());
                assert_eq!(heap.size(), 5);
                validate_heap(&heap);

                // validate order
                let mut expected_orders = deserialize_list(&expected_orders[&order][index - 5]);
                assert_eq!(heap.peek(), Some(&expected_orders[0]));
                assert_eq!(heap.peek_mut(), Some(&mut expected_orders[0]));
                assert_eq!(
                    heap,
                    BinaryHeap {
                        items: expected_orders,
                        heap_type: HeapType::Max
                    }
                );
            }
        }
    }

    #[test]
    fn test_min_heap_into_iter() {
        let heap_items = get_heap_items();
        for (_order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_min_heap();
            for item in items {
                heap.push(item);
            }
            // verify order is ascending
            assert_eq!(
                heap.into_iter().collect::<Vec<i32>>(),
                (1..=10).collect::<Vec<i32>>()
            );
        }
    }

    #[test]
    fn test_max_heap_into_iter() {
        let heap_items = get_heap_items();
        for (_order, items) in heap_items {
            let mut heap = BinaryHeap::<i32>::new_max_heap();
            for item in items {
                heap.push(item);
            }
            // verify order is descending
            assert_eq!(
                heap.into_iter().collect::<Vec<i32>>(),
                (1..=10).rev().collect::<Vec<i32>>()
            );
        }
    }

    #[test]
    fn test_min_heap_with_duplicate() {
        // test push 2 duplicate items then pop both
        let mut heap = BinaryHeap::<i32>::new_min_heap();
        heap.push(5);
        heap.push(5);
        validate_heap(&heap);
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);

        // test push 2 duplicate items then pop-push both
        let mut heap = BinaryHeap::<i32>::new_min_heap();
        heap.push(5);
        heap.push(5);
        validate_heap(&heap);
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop_push(6), Some(5));
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop_push(6), Some(5));
        validate_heap(&heap);
        assert_eq!(heap.peek(), Some(&6));
        assert_eq!(heap.pop(), Some(6));
        assert_eq!(heap.peek(), Some(&6));
        assert_eq!(heap.pop(), Some(6));
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn test_max_heap_with_duplicate() {
        // test push 2 duplicate items then pop both
        let mut heap = BinaryHeap::<i32>::new_max_heap();
        heap.push(5);
        heap.push(5);
        validate_heap(&heap);
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop(), Some(5));
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);

        // test push 2 duplicate items then pop-push both
        let mut heap = BinaryHeap::<i32>::new_max_heap();
        heap.push(5);
        heap.push(5);
        validate_heap(&heap);
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop_push(4), Some(5));
        assert_eq!(heap.peek(), Some(&5));
        assert_eq!(heap.pop_push(4), Some(5));
        validate_heap(&heap);
        assert_eq!(heap.peek(), Some(&4));
        assert_eq!(heap.pop(), Some(4));
        assert_eq!(heap.peek(), Some(&4));
        assert_eq!(heap.pop(), Some(4));
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.pop(), None);
    }
}
