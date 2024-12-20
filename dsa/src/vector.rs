//! Vector implemented with unsafe rust

use std::{alloc, ops, ptr, slice};

/// Vector struct
///
/// * `ptr`: NonNull pointer at start of vector
/// * `cap`: capacity of vector
/// * `len`: length of vector
#[derive(Debug, PartialEq)]
pub struct Vector<T> {
    ptr: ptr::NonNull<T>,
    cap: usize,
    len: usize,
}

/// Index out of bound error used in `Result::Err`
#[derive(Debug, PartialEq)]
pub struct IndexOutOfBoundError;

impl<T> Vector<T> {
    /// Creates new empty vector
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let vec = Vector::<usize>::new();
    /// assert!(vec.is_empty());
    /// ```
    pub fn new() -> Vector<T> {
        Vector {
            ptr: ptr::NonNull::dangling(),
            cap: 0,
            len: 0,
        }
    }

    /// Creates new vector with allocated capacity
    ///
    /// * `cap`: capacity of vector
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let vec = Vector::<usize>::new_with_cap(5);
    /// assert!(vec.is_empty());
    /// ```
    pub fn new_with_cap(cap: usize) -> Vector<T> {
        let ptr = if cap == 0 {
            ptr::NonNull::dangling()
        } else {
            Vector::alloc(cap)
        };
        Vector { ptr, cap, len: 0 }
    }

    /// Creates new vector from array
    ///
    /// * `arr`: array slice
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let vec = Vector::from_array(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.len(), 5);
    /// ```
    pub fn from_array(arr: &[T]) -> Vector<T> {
        let len = arr.len();
        let ptr = if len == 0 {
            ptr::NonNull::dangling()
        } else {
            Vector::alloc(len)
        };
        // copy data from array to vector
        unsafe {
            ptr::copy(arr.as_ptr(), ptr.as_ptr(), len);
        };
        Vector { ptr, cap: len, len }
    }

    /// Returns the NonNull raw pointer to the vector data
    /// DANGER! The raw pointer can be dangling
    fn raw_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    /// Creates new vector from array
    ///
    /// * `arr`: array slice
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let vec = Vector::<usize>::new();
    /// assert_eq!(vec.len(), 0);
    /// let vec = Vector::from_array(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Creates new vector from array
    ///
    /// * `arr`: array slice
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let vec = Vector::<usize>::new();
    /// assert!(vec.is_empty());
    /// let vec = Vector::from_array(&[1, 2, 3, 4, 5]);
    /// assert!(!vec.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Helper function that allocates memory with specified capacity
    ///
    /// * `cap`: capacity of memory allocation, in count of T, must be greater than 0
    fn alloc(cap: usize) -> ptr::NonNull<T> {
        // create memory layout
        let layout = alloc::Layout::array::<T>(cap).unwrap();
        // allocate memory
        let raw_ptr = unsafe { alloc::alloc(layout) };
        // if memory allocation fails, signal error
        if raw_ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }
        // create non-null pointer
        unsafe { ptr::NonNull::new_unchecked(raw_ptr as *mut T) }
    }

    /// Helper function that expands memory capacity
    /// if capacity is 0, memory with capacity 1 is allocated
    /// otherwise, double memory capacity and reallocate memory
    fn expand(&mut self) {
        let old_cap = self.cap;
        let (new_ptr, new_cap) = if self.is_empty() {
            // If dynamic array is empty, the pointer is dangling, need to allocate new memory.
            let new_cap = 1;
            let new_ptr: ptr::NonNull<T> = Vector::alloc(new_cap);
            (new_ptr, new_cap)
        } else {
            /*
            No need to check new capacity overflow.
            Old capacity cannot exceed isize::MAX due to layout array constraint.
            Therefore, it is impossible for new capacity to exceed usize::MAX.
            */
            let new_cap = old_cap * 2;
            // create old & new memory layout
            let old_layout = alloc::Layout::array::<T>(old_cap).unwrap();
            let new_layout = alloc::Layout::array::<T>(new_cap).unwrap();
            // reallocate memory
            let new_raw_ptr =
                unsafe { alloc::realloc(self.raw_ptr() as *mut u8, old_layout, new_layout.size()) };
            // if memory allocation fails, signal error
            if new_raw_ptr.is_null() {
                alloc::handle_alloc_error(new_layout);
            }
            // create non-null pointer
            let new_ptr = unsafe { ptr::NonNull::new_unchecked(new_raw_ptr as *mut T) };
            (new_ptr, new_cap)
        };
        // update memory pointer and capacity
        self.ptr = new_ptr;
        self.cap = new_cap;
    }

    /// Push item to end of vector
    ///
    /// * `item`: item
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::new();
    /// vec.push(5);
    /// assert_eq!(vec.len(), 1);
    /// assert_eq!(vec[0], 5);
    /// ```
    pub fn push(&mut self, item: T) {
        // expand memory if full
        if self.len == self.cap {
            self.expand();
        }
        // write item
        unsafe {
            ptr::write(self.raw_ptr().add(self.len), item);
        }
        // increment length
        self.len += 1
    }

    /// Pop item from the end of vector
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.pop(), Some(5));
    /// assert_eq!(vec.len(), 4);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.len -= 1;
            // read item
            unsafe { Some(self.raw_ptr().add(self.len).read()) }
        }
    }

    /// Insert item to vector
    ///
    /// * `index`: index to insert
    /// * `item`: item to insert
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// vec.insert(3, 6);
    /// assert_eq!(vec.len(), 6);
    /// assert_eq!(vec[3], 6);
    /// ```
    pub fn insert(&mut self, index: usize, item: T) -> Result<(), IndexOutOfBoundError> {
        if index > self.len {
            return Err(IndexOutOfBoundError);
        }
        // expand memory if full
        if self.len == self.cap {
            self.expand();
        }
        // shift items
        unsafe {
            ptr::copy(
                self.raw_ptr().add(index),
                self.raw_ptr().add(index + 1),
                self.len - index,
            )
        }
        // insert item
        unsafe {
            ptr::write(self.raw_ptr().add(index), item);
        }
        // increment length
        self.len += 1;
        Ok(())
    }

    /// Remove item from vector
    ///
    /// * `index`: index to remove
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.remove(3), Ok(4));
    /// assert_eq!(vec.len(), 4);
    /// assert_eq!(vec[3], 5);
    /// ```
    pub fn remove(&mut self, index: usize) -> Result<T, IndexOutOfBoundError> {
        if index >= self.len {
            return Err(IndexOutOfBoundError);
        }
        // load item
        let item = unsafe { self.raw_ptr().add(index).read() };
        // shift items
        unsafe {
            ptr::copy(
                self.raw_ptr().add(index + 1),
                self.raw_ptr().add(index),
                self.len - index - 1,
            );
        }
        // decrement length
        self.len -= 1;
        Ok(item)
    }

    /// Get immutable reference to item at index
    ///
    /// * `index`: index of item
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// let item = vec.get_ref(2).unwrap();
    /// assert_eq!(*item, 3);
    /// ```
    pub fn get_ref(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            None
        } else {
            unsafe { self.raw_ptr().add(index).as_ref() }
        }
    }

    /// Get immutable reference to item at index
    ///
    /// * `index`: index of item
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// let item = vec.get_mut(2).unwrap();
    /// *item += 3;
    /// assert_eq!(*item, 6);
    /// ```
    pub fn get_mut(&self, index: usize) -> Option<&mut T> {
        if index >= self.len {
            None
        } else {
            unsafe { self.raw_ptr().add(index).as_mut() }
        }
    }

    /// Get immutable reference to item at index
    ///
    /// * `index`: index of item
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// let mut iter = vec.iter();
    /// for i in 1..=5 {
    ///     assert_eq!(iter.next(), Some(&i));
    /// }
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            vec: self,
            index: 0,
        }
    }

    /// Get immutable reference to item at index
    ///
    /// * `index`: index of item
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// let mut iter_mut = vec.iter_mut();
    /// for i in 1..=5 {
    ///     let item = iter_mut.next().unwrap();
    ///     *item += 2;
    /// }
    /// assert_eq!(iter_mut.next(), None);
    ///
    /// let mut iter = vec.iter();
    /// for i in 1..=5 {
    ///     assert_eq!(iter.next(), Some(&(i + 2)));
    /// }
    /// ```
    pub fn iter_mut(&self) -> IterMut<T> {
        IterMut {
            vec: self,
            index: 0,
        }
    }
}

impl<T> Default for Vector<T> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Iter<'a, T> {
    vec: &'a Vector<T>,
    index: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.vec.len {
            None
        } else {
            let item = self.vec.get_ref(self.index);
            self.index += 1;
            item
        }
    }
}

pub struct IterMut<'a, T> {
    vec: &'a Vector<T>,
    index: usize,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.vec.len {
            None
        } else {
            let item = self.vec.get_mut(self.index);
            self.index += 1;
            item
        }
    }
}

impl<T> IntoIterator for Vector<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    /// IntoIter implementation
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2]);
    /// let mut iter = vec.into_iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next_back(), Some(2));
    /// assert_eq!(iter.next(), None);
    /// assert_eq!(iter.next_back(), None);
    fn into_iter(self) -> Self::IntoIter {
        let len = self.len;
        IntoIter {
            vec: self,
            head_idx: 0,
            // it's easier to keep idx as usize, but (len - 1) can underflow,
            // so we'll set tail_idx as 0 instead of -1, and manually check
            // if vector is empty before indexing on tail.
            tail_idx: if len == 0 { 0 } else { len - 1 },
        }
    }
}

pub struct IntoIter<T> {
    vec: Vector<T>,
    head_idx: usize,
    tail_idx: usize,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        // if vector is empty or head is ahead of tail index, return `None`
        if self.vec.is_empty() || self.head_idx > self.tail_idx {
            None
        } else {
            let item = unsafe { self.vec.raw_ptr().add(self.head_idx).read() };
            self.head_idx += 1;
            Some(item)
        }
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // if vector is empty or head is ahead of tail index, return `None`
        if self.vec.is_empty() || self.head_idx > self.tail_idx {
            None
        } else {
            let item = unsafe { self.vec.raw_ptr().add(self.tail_idx).read() };
            self.tail_idx -= 1;
            Some(item)
        }
    }
}

impl<T, I> ops::Index<I> for Vector<T>
where
    I: slice::SliceIndex<[T]>,
{
    type Output = I::Output;
    /// `Index` implementation
    ///
    /// * `index`: index that implements `SliceIndex`
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec[2], 3);
    /// assert_eq!(vec[2..4], [3, 4]);
    fn index(&self, index: I) -> &I::Output {
        let slice = unsafe { slice::from_raw_parts(self.raw_ptr(), self.len) };
        index.index(slice)
    }
}

impl<T, I> ops::IndexMut<I> for Vector<T>
where
    I: slice::SliceIndex<[T]>,
{
    /// `IndexMut` implementation
    ///
    /// * `index`: index that implements `SliceIndex`
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector::Vector;
    /// let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
    /// vec[2] += 3;
    /// assert_eq!(vec[2], 6);
    /// for item in &mut vec[2..5] {
    ///     *item += 2;
    /// }
    /// assert_eq!(vec[..], [1, 2, 8, 6, 7]);
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        let slice = unsafe { slice::from_raw_parts_mut(self.raw_ptr(), self.len) };
        index.index_mut(slice)
    }
}

impl<T> Drop for Vector<T> {
    fn drop(&mut self) {
        if self.cap > 0 {
            let layout = alloc::Layout::array::<T>(self.cap).unwrap();
            unsafe { alloc::dealloc(self.raw_ptr() as *mut u8, layout) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create() {
        // Vector::new()
        assert_eq!(
            Vector::<usize>::new(),
            Vector {
                ptr: ptr::NonNull::dangling(),
                cap: 0,
                len: 0
            }
        );
        assert_eq!(
            Vector::<String>::new(),
            Vector {
                ptr: ptr::NonNull::dangling(),
                cap: 0,
                len: 0
            }
        );

        // Vector::new_with_cap()
        let vec = Vector::<usize>::new_with_cap(100);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.cap, 100);
        assert!(vec.is_empty());
        let vec = Vector::<usize>::new_with_cap(0);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.cap, 0);
        assert!(vec.is_empty());

        // Vector::from_array()
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        assert_eq!(vec.len(), 5);
        assert_eq!(vec.cap, 5);
        assert!(!vec.is_empty());
        let vec = Vector::<usize>::from_array(&[]);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.cap, 0);
        assert!(vec.is_empty());
    }

    #[test]
    fn test_default() {
        assert_eq!(
            Vector::<usize>::default(),
            Vector {
                ptr: ptr::NonNull::dangling(),
                cap: 0,
                len: 0
            }
        );
    }

    #[test]
    fn test_push_pop() {
        let mut vec = Vector::<usize>::new();
        // test push
        for i in 1..=100 {
            vec.push(i);
        }
        // verify vector capacity is expanded correctly
        assert_eq!(vec.cap, 128);
        assert_eq!(vec.len(), 100);

        // test pop
        for i in (1..=100).rev() {
            assert_eq!(vec.pop(), Some(i));
        }
        // verify vector capacity is unchanged
        assert_eq!(vec.cap, 128);
        assert_eq!(vec.len(), 0);

        // verify pop returns None for empty vector
        assert_eq!(vec.pop(), None);
    }

    #[test]
    fn test_insert_remove() {
        let mut vec = Vector::<usize>::new();
        // test insert at the end
        for i in 1..=100 {
            vec.insert(i - 1, i).unwrap();
        }
        // test remove at the end
        for i in (1..=100).rev() {
            assert_eq!(vec.remove(i - 1).unwrap(), i);
        }

        // test insert at the start
        for i in 1..=100 {
            vec.insert(0, i).unwrap();
        }
        // test remove at the start
        for i in (1..=100).rev() {
            assert_eq!(vec.remove(0).unwrap(), i);
        }

        // test random insert/remove
        let mut vec = Vector::from_array(&[1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(vec.remove(3).unwrap(), 4);
        vec.insert(5, 10).unwrap();
        assert_eq!(vec.remove(5).unwrap(), 10);
        vec.insert(7, 11).unwrap();
        assert_eq!(vec.remove(6).unwrap(), 8);
        assert_eq!(vec.remove(6).unwrap(), 11);
    }

    #[test]
    fn test_insert_remove_out_of_bound() {
        let mut vec = Vector::<usize>::new();
        assert_eq!(vec.insert(1, 0), Err(IndexOutOfBoundError));
        assert_eq!(vec.remove(0), Err(IndexOutOfBoundError));
        let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        assert_eq!(vec.insert(6, 0), Err(IndexOutOfBoundError));
        assert_eq!(vec.remove(5), Err(IndexOutOfBoundError));
    }

    #[test]
    fn test_references() {
        // test ref empty vector
        let vec = Vector::<usize>::new();
        assert_eq!(vec.get_ref(0), None);
        assert_eq!(vec.get_ref(1), None);

        // test mut ref empty vector
        assert_eq!(vec.get_mut(0), None);
        assert_eq!(vec.get_mut(1), None);

        // test ref non-empty vector
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        assert_eq!(vec.get_ref(0), Some(&1));
        assert_eq!(vec.get_ref(4), Some(&5));
        assert_eq!(vec.get_ref(5), None);

        // test mut ref non-empty vector
        assert_eq!(vec.get_mut(0), Some(&mut 1));
        assert_eq!(vec.get_mut(4), Some(&mut 5));
        assert_eq!(vec.get_mut(5), None);

        // test mut ref mutation
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        for i in 0..=4 {
            let item = vec.get_mut(i).unwrap();
            *item += 1;
        }
        for i in 0..=4 {
            assert_eq!(vec.get_ref(i), Some(&(i + 2)));
        }
    }

    #[test]
    fn test_iterators() {
        // iter empty
        let vec = Vector::<usize>::new();
        let mut iter = vec.iter();
        assert_eq!(iter.next(), None);

        // iter non-empty
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let mut iter = vec.iter();
        for i in 1..=5 {
            assert_eq!(iter.next(), Some(&i));
        }
        assert_eq!(iter.next(), None);

        // iter_mut empty
        let vec = Vector::<usize>::new();
        let mut iter = vec.iter_mut();
        assert_eq!(iter.next(), None);

        // iter_mut non-empty
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let mut iter = vec.iter_mut();
        for mut i in 1..=5 {
            assert_eq!(iter.next(), Some(&mut i));
        }
        assert_eq!(iter.next(), None);

        // into_iter empty
        let vec = Vector::<usize>::new();
        let mut iter = vec.into_iter();
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        // into_iter non_empty
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let mut iter = vec.into_iter();
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next_back(), Some(5));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next_back(), Some(4));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);

        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let mut iter = vec.into_iter();
        assert_eq!(iter.next_back(), Some(5));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next_back(), Some(4));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next_back(), Some(3));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_index() {
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        for i in 0..=4 {
            assert_eq!(vec[i], i + 1);
        }
    }

    #[test]
    #[should_panic(expected = "index out of bound")]
    fn test_index_out_of_bound_empty_vec() {
        let vec = Vector::<usize>::new();
        let _item = vec[0];
    }

    #[test]
    #[should_panic(expected = "index out of bound")]
    fn test_index_out_of_bound_non_empty_vec() {
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let _item = vec[5];
    }

    #[test]
    fn test_index_mut() {
        let mut vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        for i in 0..=4 {
            vec[i] += 1;
        }
        for i in 0..=4 {
            assert_eq!(vec[i], i + 2);
        }
    }
    #[test]
    #[should_panic(expected = "index out of bound")]
    fn test_index_mut_out_of_bound_empty_vec() {
        let vec = Vector::<usize>::new();
        let mut _item = vec[0];
    }

    #[test]
    #[should_panic(expected = "index out of bound")]
    fn test_index_mut_out_of_bound_non_empty_vec() {
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let mut _item = vec[5];
    }

    #[test]
    fn test_range() {
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let slice = &vec[0..5];
        (0..=4).for_each(|i| {
            assert_eq!(slice[i], i + 1);
        });
    }

    #[test]
    #[should_panic(expected = "out of range for slice")]
    fn test_range_out_of_bound_empty_vec() {
        let vec = Vector::<usize>::new();
        let _slice = &vec[0..1];
    }

    #[test]
    #[should_panic(expected = "out of range for slice")]
    fn test_range_out_of_bound_non_empty_vec() {
        let vec = Vector::<usize>::from_array(&[1, 2, 3, 4, 5]);
        let _slice = &vec[0..=5];
    }
}
