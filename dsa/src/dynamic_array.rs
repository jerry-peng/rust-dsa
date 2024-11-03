const INDEX_OUT_OF_BOUND_MSG: &str = "Index out of bound";
#[derive(Debug, PartialEq)]
pub struct DynamicArray<T> {
    placeholder: T,
    data: Vec<T>,
    capacity: usize,
    size: usize,
}

impl<T> DynamicArray<T> {
    /// Creates new sized dynamic array.
    ///
    /// * `capacity`: capacity of dynamic array
    /// * `placeholder`: placeholder value for unutilized spaces
    ///
    /// # Examples
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let arr = DynamicArray::new(2, 0);
    /// assert!(arr.is_empty());
    /// ```
    pub fn new(capacity: usize, placeholder: T) -> DynamicArray<T>
    where
        T: Clone,
    {
        let mut data = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            data.push(placeholder.clone())
        }
        DynamicArray {
            placeholder,
            data,
            capacity,
            size: 0,
        }
    }

    /// Creates new dynamic array from array slice.
    ///
    /// * `arr`: array slice
    /// * `placeholder`: placeholder value for unutilized spaces
    ///
    /// # Examples
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let arr = DynamicArray::from_array(&["a", "bc", "def"], "12");
    /// assert_eq!(arr.len(), 3);
    /// ```
    pub fn from_array(arr: &[T], placeholder: T) -> DynamicArray<T>
    where
        T: Clone,
    {
        DynamicArray {
            placeholder,
            data: arr.to_vec(),
            capacity: arr.len(),
            size: arr.len(),
        }
    }

    /// Get reference to item at index.
    ///
    /// * `index`: index of item
    ///
    /// # Example
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let mut arr = DynamicArray::from_array(&[1], 0);
    /// let item = *arr.get_ref(0).unwrap();
    /// assert_eq!(item, 1);
    /// let mut item = *arr.get_ref(0).unwrap();
    /// item += 2;
    /// assert_eq!(item, 3);
    /// let item = arr.get_ref(1);
    /// assert_eq!(item, None);
    /// ```
    pub fn get_ref(&self, index: usize) -> Option<&T> {
        if index < self.size {
            Some(&self.data[index])
        } else {
            None
        }
    }

    /// Get mutable reference to item at index.
    ///
    /// * `index`: index of item
    ///
    /// # Example
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let mut arr = DynamicArray::from_array(&[1], 0);
    /// if let Some(item) = arr.get_mut_ref(0){
    ///     *item += 2
    /// }
    /// let item = *arr.get_ref(0).unwrap();
    /// assert_eq!(item, 3);
    /// let item = arr.get_mut_ref(1);
    /// assert_eq!(item, None);
    /// ```
    pub fn get_mut_ref(&mut self, index: usize) -> Option<&mut T> {
        if index < self.size {
            Some(&mut self.data[index])
        } else {
            None
        }
    }

    /// Get length of dynamic array.
    ///
    /// # Examples
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let arr = DynamicArray::from_array(&[], 0);
    /// assert_eq!(arr.len(), 0);
    /// let arr = DynamicArray::from_array(&[1], 0);
    /// assert_eq!(arr.len(), 1);
    /// let arr = DynamicArray::from_array(&["a", "b"], "c");
    /// assert_eq!(arr.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.size
    }

    /// Get whether dynamic array is empty.
    ///
    /// # Example
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let arr = DynamicArray::from_array(&[], 0);
    /// assert!(arr.is_empty());
    /// let arr = DynamicArray::from_array(&["a"], "o");
    /// assert!(!arr.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// return whether dynamic array contains an item
    ///
    /// * `item`: item
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let arr = DynamicArray::from_array(&[1], 0);
    /// assert!(arr.contains(1));
    /// assert!(!arr.contains(0));
    /// ```
    pub fn contains(&self, item: T) -> bool
    where
        T: PartialEq,
    {
        let slice = &self.data[0..self.size];
        slice.iter().any(|x| *x == item)
    }

    /// get position of an item
    ///
    /// * `item`: item
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let arr = DynamicArray::from_array(&[1], 0);
    /// assert_eq!(arr.position(1), Some(0));
    /// assert_eq!(arr.position(2), None);
    /// ```
    pub fn position(&self, item: T) -> Option<usize>
    where
        T: PartialEq,
    {
        (0..self.size).position(|index| self.data[index] == item)
    }

    /// Expands capacity of dynamic array.
    /// Accomplished by creating a new vector with doubled capacity,
    /// and then copying over data from old to new vector.
    fn expand_capacity(&mut self)
    where
        T: Clone,
    {
        // get new capacity
        let new_capacity = if self.capacity == 0 {
            1
        } else {
            self.capacity * 2
        };
        // create vec with new capacity, copy over data, then populate
        // the rest of vec with placeholder
        let mut new_data = Vec::with_capacity(new_capacity);
        for i in 0..self.size {
            new_data.push(self.data[i].clone());
        }
        for _ in self.size..new_capacity {
            new_data.push(self.placeholder.clone());
        }
        // re-assign data to new vec
        self.data = new_data;
        self.capacity = new_capacity;
    }

    /// Push an item to the end of dynamic array
    ///
    /// * `item`: item to push
    ///
    /// # Example
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let mut arr = DynamicArray::new(0, 0);
    /// assert_eq!(arr.len(), 0);
    /// arr.push(1);
    /// assert_eq!(arr.len(), 1);
    /// arr.push(2);
    /// assert_eq!(arr.len(), 2);
    /// ```
    pub fn push(&mut self, item: T)
    where
        T: Clone,
    {
        if self.size == self.capacity {
            self.expand_capacity();
        }
        self.data[self.size] = item;
        self.size += 1
    }

    /// Insert an item to dynamic array at an index.
    ///
    /// * `item`: item to insert
    /// * `index`: index to insert
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bound
    ///
    /// # Example
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let mut arr = DynamicArray::new(0, 0);
    /// assert_eq!(arr.len(), 0);
    /// arr.insert(2, 0);
    /// assert_eq!(arr.len(), 1);
    /// arr.insert(3, 1);
    /// assert_eq!(arr.len(), 2);
    /// assert_eq!(arr.pop(), Some(3));
    /// assert_eq!(arr.pop(), Some(2));
    /// ```
    pub fn insert(&mut self, item: T, index: usize)
    where
        T: Clone,
    {
        if index > self.size {
            panic!("{}", INDEX_OUT_OF_BOUND_MSG);
        }
        if self.size == self.capacity {
            self.expand_capacity();
        }
        for i in (index..self.size).rev() {
            self.data[i + 1] = self.data[i].clone();
        }
        self.data[index] = item;
        self.size += 1
    }

    /// Pop an item from the end of dynamic array.
    ///
    /// # Example
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let mut arr = DynamicArray::new(0, 0);
    /// assert_eq!(arr.pop(), None);
    /// assert!(arr.is_empty());
    /// arr.push(1);
    /// assert_eq!(arr.pop(), Some(1));
    /// assert!(arr.is_empty());
    pub fn pop(&mut self) -> Option<T>
    where
        T: Clone,
    {
        if self.size > 0 {
            self.size -= 1;
            Some(self.data[self.size].clone())
        } else {
            None
        }
    }

    /// Remove an item from dynamic array at index.
    ///
    /// * `index`: index to remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bound
    ///
    /// # Example
    /// ```
    /// use dsa::dynamic_array::DynamicArray;
    /// let mut arr = DynamicArray::from_array(&[1, 2, 3], 0);
    /// assert_eq!(arr.remove(1), 2);
    /// assert_eq!(arr.pop(), Some(3));
    /// assert_eq!(arr.pop(), Some(1));
    pub fn remove(&mut self, index: usize) -> T
    where
        T: Clone,
    {
        if index >= self.size {
            panic!("{}", INDEX_OUT_OF_BOUND_MSG);
        }
        let item = self.data[index].clone();
        for i in index..self.size - 1 {
            self.data[i] = self.data[i + 1].clone();
        }
        self.size -= 1;
        item
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let arr = DynamicArray::new(0, 1);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 1,
                data: vec![],
                capacity: 0,
                size: 0
            }
        );
        let arr = DynamicArray::new(2, 0);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![0, 0],
                capacity: 2,
                size: 0,
            }
        );
        let arr = DynamicArray::new(3, "a");
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: "a",
                data: vec!["a", "a", "a"],
                capacity: 3,
                size: 0
            }
        );
    }

    #[test]
    fn test_from_array() {
        let arr = DynamicArray::from_array(&[], 0);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![],
                capacity: 0,
                size: 0
            }
        );
        let arr = DynamicArray::from_array(&[1, 2, 3], 1);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 1,
                data: vec![1, 2, 3],
                capacity: 3,
                size: 3
            }
        );
        let arr = DynamicArray::from_array(&["a", "b", "c"], "def");
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: "def",
                data: vec!["a", "b", "c"],
                capacity: 3,
                size: 3
            }
        );
    }

    #[test]
    fn test_get_ref_some() {
        let arr = DynamicArray::from_array(&[1, 2, 3], 0);
        assert_eq!(arr.get_ref(0), Some(1).as_ref());
        assert_eq!(arr.get_ref(1), Some(2).as_ref());
        assert_eq!(arr.get_ref(2), Some(3).as_ref());
        assert_eq!(arr.get_ref(3), None);
        assert_eq!(arr.get_ref(4), None);
    }

    #[test]
    fn test_get_mut_ref_some() {
        let mut arr = DynamicArray::from_array(&[1, 2, 3], 0);
        for index in 0..3 {
            if let Some(item) = arr.get_mut_ref(index) {
                *item += 2;
            }
        }
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![3, 4, 5],
                capacity: 3,
                size: 3
            }
        );
        assert_eq!(arr.get_mut_ref(3), None);
        assert_eq!(arr.get_mut_ref(4), None);
    }

    #[test]
    fn test_len() {
        assert_eq!(DynamicArray::from_array(&[1, 2, 3], 0).len(), 3);
        assert_eq!(DynamicArray::from_array(&[], 0).len(), 0);
    }

    #[test]
    fn test_is_empty() {
        assert!(!DynamicArray::from_array(&[1, 2, 3], 0).is_empty());
        assert!(DynamicArray::from_array(&[], 0).is_empty());
    }

    #[test]
    fn test_contains() {
        assert!(DynamicArray::from_array(&[1, 2, 3], 0).contains(1));
        assert!(!DynamicArray::from_array(&[1, 2, 3], 0).contains(0));
        assert!(!DynamicArray::from_array(&[], 0).contains(1));
    }

    #[test]
    fn test_position() {
        let arr = DynamicArray::from_array(&[1, 2, 3], 0);
        assert_eq!(arr.position(1), Some(0));
        assert_eq!(arr.position(2), Some(1));
        assert_eq!(arr.position(3), Some(2));
        assert_eq!(arr.position(4), None);
    }

    #[test]
    fn test_push() {
        let mut arr = DynamicArray::new(0, 0);
        arr.push(1);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1],
                capacity: 1,
                size: 1,
            }
        );
        arr.push(2);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2],
                capacity: 2,
                size: 2,
            }
        );
        arr.push(3);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2, 3, 0],
                capacity: 4,
                size: 3,
            }
        );
        arr.push(4);
        arr.push(5);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2, 3, 4, 5, 0, 0, 0],
                capacity: 8,
                size: 5,
            }
        )
    }

    #[test]
    fn test_insert() {
        let mut arr = DynamicArray::new(0, 0);
        arr.insert(1, 0);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1],
                capacity: 1,
                size: 1,
            }
        );
        arr.insert(2, 1);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2],
                capacity: 2,
                size: 2,
            }
        );
        arr.insert(3, 1);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 3, 2, 0],
                capacity: 4,
                size: 3,
            }
        );
        arr.insert(4, 3);
        arr.insert(5, 0);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![5, 1, 3, 2, 4, 0, 0, 0],
                capacity: 8,
                size: 5,
            }
        )
    }

    #[test]
    #[should_panic(expected = "Index out of bound")]
    fn test_insert_out_of_bound_error_empty_array() {
        let mut arr = DynamicArray::new(0, 0);
        arr.insert(1, 1)
    }

    #[test]
    #[should_panic(expected = "Index out of bound")]
    fn test_insert_out_of_bound_error_non_empty_array() {
        let mut arr = DynamicArray::from_array(&[1, 2, 3], 0);
        arr.insert(1, 4)
    }

    #[test]
    fn test_pop() {
        let mut arr = DynamicArray::from_array(&[1, 2, 3], 0);
        arr.insert(5, 3);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2, 3, 5, 0, 0],
                capacity: 6,
                size: 4
            }
        );
        assert_eq!(arr.pop(), Some(5));
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2, 3, 5, 0, 0],
                capacity: 6,
                size: 3
            }
        );
        assert_eq!(arr.pop(), Some(3));
        assert_eq!(arr.pop(), Some(2));
        assert_eq!(arr.pop(), Some(1));
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2, 3, 5, 0, 0],
                capacity: 6,
                size: 0
            }
        );
        assert_eq!(arr.pop(), None);
    }

    #[test]
    fn test_remove() {
        let mut arr = DynamicArray::from_array(&[1, 2, 3], 0);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 2, 3],
                capacity: 3,
                size: 3
            }
        );
        assert_eq!(arr.remove(1), 2);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 3, 3],
                capacity: 3,
                size: 2
            }
        );
        assert_eq!(arr.remove(1), 3);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 3, 3],
                capacity: 3,
                size: 1
            }
        );
        assert_eq!(arr.remove(0), 1);
        assert_eq!(
            arr,
            DynamicArray {
                placeholder: 0,
                data: vec![1, 3, 3],
                capacity: 3,
                size: 0
            }
        );
    }

    #[test]
    #[should_panic(expected = "Index out of bound")]
    fn test_remove_out_of_bound_error_empty_array() {
        let mut arr = DynamicArray::new(2, 0);
        arr.remove(0);
    }

    #[test]
    #[should_panic(expected = "Index out of bound")]
    fn test_remove_out_of_bound_error_non_empty_array() {
        let mut arr = DynamicArray::from_array(&[1, 2, 3], 0);
        arr.remove(3);
    }
}
