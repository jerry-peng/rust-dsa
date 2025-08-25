//! Various sort implementation
//!
//! Included sort algorithms:
//! - bubble sort
//! - selection sort
//! - insertion sort
//! - merge sort
//! - quick sort

use rand::Rng;
use std::fmt::Debug;

#[derive(Clone, Debug)]
pub enum Order {
    Ascend,
    Descend,
}

#[derive(Clone, Debug)]
pub enum SortMethod {
    Bubble,
    Selection,
    Insertion,
    Merge,
    Quick,
}

/// Sort function
///
/// * `items`: items
/// * `order`: sort order
/// * `sort_method`: sort method
///
/// # Example
/// ```
/// use dsa::sorter::{sort, Order, SortMethod};
/// for sort_method in [
///     SortMethod::Bubble,
///     SortMethod::Selection,
///     SortMethod::Insertion,
///     SortMethod::Merge,
///     SortMethod::Quick,
/// ] {
///     for sort_order in [Order::Ascend, Order::Descend] {
///         let mut items = [4, 2, 5, 1, 3, 1];
///         sort(&mut items, sort_order.clone(), sort_method.clone());
///         match sort_order {
///             Order::Ascend => assert_eq!(items, [1, 1, 2, 3, 4, 5]),
///             Order::Descend => assert_eq!(items, [5, 4, 3, 2, 1, 1]),
///         }
///     }
/// }
/// ```
pub fn sort<T>(items: &mut [T], order: Order, sort_method: SortMethod)
where
    T: Ord + Default + Clone + Debug,
{
    match sort_method {
        SortMethod::Bubble => bubble_sort(items, order),
        SortMethod::Selection => selection_sort(items, order),
        SortMethod::Insertion => insertion_sort(items, order),
        SortMethod::Merge => merge_sort(items, order),
        SortMethod::Quick => quick_sort(items, order),
    }
}

/// Bubble sort
/// Sort by bubbling largest item to the end of list. After n pass,
/// there should be n sorted items at the end of list.
///
/// * `items`: items
/// * `order`: sort order
fn bubble_sort<T>(items: &mut [T], order: Order)
where
    T: Ord + Default + Clone + Debug,
{
    for i in (1..items.len()).rev() {
        let mut is_sorted = true;
        for j in 0..i {
            match order {
                Order::Ascend if items[j] > items[j + 1] => {
                    items.swap(j, j + 1);
                    is_sorted = false
                }
                Order::Descend if items[j] < items[j + 1] => {
                    items.swap(j, j + 1);
                    is_sorted = false
                }
                _ => {}
            }
        }
        if is_sorted {
            break;
        }
    }
}

/// Selection sort
/// Sort by selecting largest item in unsorted portion of list, and swap it with last
/// item of unsorted portion. After n pass, there should be n sorted items at the end
/// of list
///
/// * `items`: items
/// * `order`: sort order
fn selection_sort<T>(items: &mut [T], order: Order)
where
    T: Ord + Default + Clone + Debug,
{
    for i in (1..items.len()).rev() {
        let unsorted_items_iter = items[..=i].iter().enumerate();
        let unsorted_max_index = match order {
            Order::Ascend => unsorted_items_iter
                .max_by(|(_, a), (_, b)| a.cmp(b))
                .map(|item| item.0)
                .unwrap(),
            Order::Descend => unsorted_items_iter
                .min_by(|(_, a), (_, b)| a.cmp(b))
                .map(|item| item.0)
                .unwrap(),
        };
        if unsorted_max_index != i {
            items.swap(unsorted_max_index, i);
        }
    }
}

/// Insertion sort
/// sort by selecting first item in unsorted portion at the end of list, and bubble
/// it into sorted portion After n pass, there should be n sorted item at the start of list
///
/// * `items`: items
/// * `order`: sort order
fn insertion_sort<T>(items: &mut [T], order: Order)
where
    T: Ord + Default + Clone + Debug,
{
    for i in 1..items.len() {
        for j in (1..=i).rev() {
            match order {
                Order::Ascend => {
                    if items[j - 1] > items[j] {
                        items.swap(j - 1, j);
                    } else {
                        break;
                    }
                }
                Order::Descend => {
                    if items[j - 1] < items[j] {
                        items.swap(j - 1, j);
                    } else {
                        break;
                    }
                }
            }
        }
    }
}

/// Merge sort
/// divide and conquer; first split vectors in half repeatedly, then
/// join them using two pointer to repeatedly produce sorted sub-vectors,
/// eventually producing sorted vector
///
/// * `items`: items
/// * `order`: sort order
fn merge_sort<T>(items: &mut [T], order: Order)
where
    T: Ord + Default + Clone + Debug,
{
    let len = items.len();
    let mut temp_items: Vec<T> = std::iter::repeat_n(T::default(), len).collect();
    split(items, &mut temp_items, order);
}

fn split<T>(items: &mut [T], temp: &mut [T], order: Order)
where
    T: Ord + Default + Clone + Debug,
{
    let len = items.len();
    match len {
        0 | 1 => {}
        len => {
            let (lower_slice, upper_slice) = items.split_at_mut(len / 2);
            let (lower_temp_slice, upper_temp_slice) = temp.split_at_mut(len / 2);
            // recursively split lower and upper slices
            split(lower_slice, lower_temp_slice, order.clone());
            split(upper_slice, upper_temp_slice, order.clone());
            // the lower/upper slices should be sorted, merge using two-pointers
            merge(lower_slice, upper_slice, temp, order);
        }
    }
}

/// Given two sorted slices, produce merged sorted slice
///
/// * `lower_slice`: lower slice
/// * `upper_slice`: upper slice
/// * `temp_slice`: temp slice
/// * `order`: sort order
fn merge<T>(lower_slice: &mut [T], upper_slice: &mut [T], temp_slice: &mut [T], order: Order)
where
    T: Ord + Default + Clone + Debug,
{
    let mut lower_iter = lower_slice.iter().peekable();
    let mut upper_iter = upper_slice.iter().peekable();
    // # of items copied to temp slice
    let mut sorted_count = 0;

    loop {
        match (lower_iter.peek(), upper_iter.peek()) {
            // lower/upper slices are both exhausted
            (None, None) => break,
            // lower slice exhausted, copy rest of upper slice to temp slice
            (None, Some(_)) => {
                for item in upper_iter.by_ref() {
                    temp_slice[sorted_count] = item.clone();
                    sorted_count += 1;
                }
            }
            // upper slice exhausted, copy rest of lower slice to temp slice
            (Some(_), None) => {
                for item in lower_iter.by_ref() {
                    temp_slice[sorted_count] = item.clone();
                    sorted_count += 1;
                }
            }
            // both lower/upper slices are not exhausted. Peek next item from both slices,
            // if ascending, copy smaller item, or else, pick larger item
            (Some(lower_item), Some(upper_item)) => {
                let item_to_clone = if lower_item < upper_item {
                    match order {
                        Order::Ascend => lower_iter.next().unwrap(),
                        Order::Descend => upper_iter.next().unwrap(),
                    }
                } else {
                    match order {
                        Order::Ascend => upper_iter.next().unwrap(),
                        Order::Descend => lower_iter.next().unwrap(),
                    }
                };

                temp_slice[sorted_count] = item_to_clone.clone();
                sorted_count += 1;
            }
        }
    }

    // clone items from temp slice back to lower/upper slices
    let lower_len = lower_slice.len();
    lower_slice.clone_from_slice(&temp_slice[..lower_len]);
    upper_slice.clone_from_slice(&temp_slice[lower_len..]);
}

/// Quick sort
/// divide and conquer; first choose an item from slice as pivot, then
/// partition slice into two slices around pivot, one with items smaller than pivot,
/// and the other with items larger than pivot. Eventually the items are sorted.
///
/// * `items`: items
/// * `order`: sort order
fn quick_sort<T>(items: &mut [T], order: Order)
where
    T: Ord + Default + Clone + Debug,
{
    let len = items.len();
    match len {
        // if item has a single item or empty, return as there is nothing to sort
        0 | 1 => {}
        len => {
            // pick a random item in slice as pivot, then swap pivot to back of slice
            let pivot_index: usize = rand::rng().random_range(0..len);
            items.swap(pivot_index, len - 1);

            // go through non-pivot items, and swap them to both end of slice based on
            // comparison with pivot
            let mut lower_index = 0;
            let mut upper_index = len - 1;
            for _ in 0..len - 1 {
                match order {
                    Order::Ascend => {
                        if items[lower_index] <= items[len - 1] {
                            lower_index += 1;
                        } else {
                            upper_index -= 1;
                            items.swap(lower_index, upper_index);
                        }
                    }
                    Order::Descend => {
                        if items[lower_index] >= items[len - 1] {
                            lower_index += 1;
                        } else {
                            upper_index -= 1;
                            items.swap(lower_index, upper_index);
                        }
                    }
                }
            }

            // swap pivot back to position in between organized non-pivot items
            items.swap(lower_index, len - 1);

            // quick sort on items smaller than pivot
            quick_sort(&mut items[..lower_index], order.clone());
            // quick sort on items larger than pivot
            quick_sort(&mut items[lower_index + 1..], order.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rng;
    use rand::seq::SliceRandom;

    fn gen_shuffled_items(size: u64) -> Vec<u64> {
        let mut vec: Vec<u64> = (0..size / 2).collect();
        let mut vec2: Vec<u64> = (0..size - size / 2).collect();
        vec.append(&mut vec2);
        vec.shuffle(&mut rng());
        vec
    }

    fn is_sorted(items: &[u64], order: Order) -> bool {
        match order {
            Order::Ascend => items.is_sorted(),
            Order::Descend => items.is_sorted_by(|a, b| a >= b),
        }
    }

    #[test]
    fn test_naive_sort() {
        for sort_method in [
            SortMethod::Bubble,
            SortMethod::Selection,
            SortMethod::Insertion,
        ] {
            for _i in 0..3 {
                for len in [0, 1, 2, 3, 4, 5, 10, 100, 1000, 10000] {
                    for order in [Order::Ascend, Order::Descend] {
                        let mut items = gen_shuffled_items(len);
                        sort(&mut items, order.clone(), sort_method.clone());
                        assert!(is_sorted(&items, order));
                    }
                }
            }
        }
    }

    #[test]
    fn test_optimized_sort() {
        for sort_method in [SortMethod::Quick, SortMethod::Merge] {
            for _i in 0..3 {
                for len in [0, 1, 2, 3, 4, 5, 10, 100, 1000, 10000, 1000000] {
                    for order in [Order::Ascend, Order::Descend] {
                        let mut items = gen_shuffled_items(len);
                        sort(&mut items, order.clone(), sort_method.clone());
                        assert!(is_sorted(&items, order));
                    }
                }
            }
        }
    }
}
