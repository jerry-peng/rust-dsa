//! Hashmap implementation (with open addressing, quadratic probing, and auto-resize)
//! hash algorithm: FNV1a

use std::{
    hash::{Hash, Hasher},
    mem,
};

// Use prime number as initial capacity to reduce probe cycles
const INITIAL_CAPACITY: usize = 11;
// Load factor = 0.6
const MAX_LOAD_FACTOR_NUMERATOR: usize = 3;
const MAX_LOAD_FACTOR_DENOMINATOR: usize = 5;
// FNV1a hash algorithm constants
const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
const FNV_PRIME: u64 = 0x100000001b3;

/// FNV1a hasher state;
/// hashing algorithm implemented from https://en.wikipedia.org/wiki/Fowler–Noll–Vo_hash_function
///
/// * `hash`: stored hash
struct FNV1aHasher {
    hash: u64,
}

impl FNV1aHasher {
    /// Creates a new FNV1a Hasher with offset basis as stored hash
    fn new() -> FNV1aHasher {
        FNV1aHasher {
            hash: FNV_OFFSET_BASIS,
        }
    }
}

impl Hasher for FNV1aHasher {
    /// Emit stored hash
    fn finish(&self) -> u64 {
        self.hash
    }

    /// Hash bytes
    ///
    /// * `bytes`: list of bytes to hash
    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.hash ^= u64::from(*byte);
            self.hash = self.hash.wrapping_mul(FNV_PRIME);
        }
    }
}

#[derive(Debug)]
/// Used when no slot found due to probing cycles
struct SlotNotFoundErr;

#[derive(Debug, PartialEq, Clone)]
enum Slot<K, V> {
    Empty,       // empty slot
    Tombstone,   // removed entry leaves tombstone
    Entry(K, V), // entry slot stores key/value pair
}

#[derive(Debug, PartialEq)]
/// Hash map struct
///
/// * `slots`: vector of slots
/// * `size`: number of stored key/value pair
pub struct HashMap<K, V> {
    slots: Vec<Slot<K, V>>,
    size: usize,
}

impl<K, V> HashMap<K, V>
where
    K: Hash + PartialEq + Clone,
    V: Clone,
{
    /// Creates new empty hash map with initial capacity
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// assert_eq!(hashmap.size(), 0);
    /// assert!(hashmap.is_empty());
    /// ```
    pub fn new() -> HashMap<K, V> {
        let slots: Vec<Slot<K, V>> = vec![Slot::Empty; INITIAL_CAPACITY];
        HashMap { slots, size: 0 }
    }

    /// Get number of key/value pair stored in hash map
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// assert_eq!(hashmap.size(), 0);
    /// hashmap.insert("a".to_string(), 1);
    /// assert_eq!(hashmap.size(), 1);
    /// hashmap.insert("b".to_string(), 1);
    /// assert_eq!(hashmap.size(), 2);
    /// hashmap.remove(&"a".to_string());
    /// ```
    pub fn size(&self) -> usize {
        self.size
    }

    /// Get hash map capacity
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<usize, usize>::new();
    /// assert_eq!(hashmap.capacity(), 11);
    /// for i in 1..=6 {
    ///     hashmap.insert(i, i);
    ///     assert_eq!(hashmap.capacity(), 11);
    /// }
    /// hashmap.insert(7, 7);
    /// assert_eq!(hashmap.capacity(), 22);
    /// ```
    pub fn capacity(&self) -> usize {
        self.slots.capacity()
    }

    /// Get hash map capacity
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// assert!(hashmap.is_empty());
    /// hashmap.insert("a".to_string(), 11);
    /// assert!(!hashmap.is_empty());
    /// hashmap.remove(&"a".to_string());
    /// assert!(hashmap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Insert key/value pair to hashmap
    ///
    /// * `key`: key
    /// * `val`: value
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// hashmap.insert("a".to_string(), 5);
    /// assert_eq!(hashmap.get(&"a".to_string()), Some(&5));
    /// hashmap.insert("b".to_string(), 10);
    /// assert_eq!(hashmap.get(&"b".to_string()), Some(&10));
    /// ```
    pub fn insert(&mut self, key: K, val: V) -> Option<V> {
        let size = self.size;
        let mut capacity = self.slots.capacity();

        // find available slot
        let slot_mut = self.find_slot_mut(&key);

        // if slot is not found due to probing cycle, expand hashmap vector by doubling capacity,
        // and retry finding available slot
        let slot_mut = match slot_mut {
            Ok(slot_mut) => slot_mut,
            Err(SlotNotFoundErr) => {
                self.expand();
                capacity *= 2;
                self.find_slot_mut(&key)
                    .expect("Slot look-up exhausted for new entry after expansion")
            }
        };

        if let Slot::Entry(..) = slot_mut {
            // key exists in hashmap, so found slot is an entry;
            // swap old value with new and return old value
            let old_entry = mem::replace(slot_mut, Slot::Entry(key, val));
            if let Slot::Entry(_, val) = old_entry {
                Some(val)
            } else {
                unreachable!("Slot was occupied and must be of type Slot::Entry");
            }
        } else {
            // key does not exist in hashmap;
            let reached_max_load =
                size >= capacity / MAX_LOAD_FACTOR_DENOMINATOR * MAX_LOAD_FACTOR_NUMERATOR;

            // if load factor reached, expand hashmap vector by doubling capacity, and retry
            // finding available slot
            let slot_mut = if reached_max_load {
                self.expand();
                self.find_slot_mut(&key)
                    .expect("Slot look-up exhausted for new entry after expansion")
            } else {
                slot_mut
            };

            // insert key/value pair to slot and increment hash map size
            *slot_mut = Slot::Entry(key, val);
            self.size += 1;
            None
        }
    }

    /// Expand hashmap's slot vector and re-calculate hash index for all key/value pairs
    fn expand(&mut self) {
        // swap out slot vector with new initialized vector with double capacity
        let capacity = self.slots.capacity() * 2;
        let old_slots = mem::replace(&mut self.slots, vec![Slot::Empty; capacity]);

        // for each key/value pair in old slot vector,
        // re-calculate hash index under new capacity and move pair to new slot vector
        for slot in old_slots {
            match slot {
                Slot::Empty | Slot::Tombstone => continue,
                Slot::Entry(key, val) => {
                    let slot_mut = self
                        .find_slot_mut(&key)
                        .expect("Slot look-up exhausted while expansion");
                    *slot_mut = Slot::Entry(key, val);
                }
            }
        }
    }

    /// Remove key/value pair from hashmap
    ///
    /// * `key`: key
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// hashmap.insert("a".to_string(), 5);
    /// hashmap.insert("b".to_string(), 10);
    /// assert_eq!(hashmap.get(&"a".to_string()), Some(&5));
    /// hashmap.remove(&"a".to_string());
    /// assert_eq!(hashmap.get(&"a".to_string()), None);
    /// assert_eq!(hashmap.get(&"b".to_string()), Some(&10));
    /// hashmap.remove(&"b".to_string());
    /// assert_eq!(hashmap.get(&"b".to_string()), None);
    /// ```
    pub fn remove(&mut self, key: &K) -> Option<V> {
        // find available slot;
        // if no slot found due to reference cycle, the key/value pair does not exist
        let slot_mut = self.find_slot_mut(key).ok()?;

        // if entry found, replace it with tombstone, decrement hash map size,
        // and return entry value
        if let Slot::Entry(..) = slot_mut {
            let old_entry = mem::replace(slot_mut, Slot::Tombstone);
            if let Slot::Entry(_, val) = old_entry {
                self.size -= 1;
                Some(val)
            } else {
                unreachable!("Slot was occupied and must be of type Slot::Entry");
            }
        } else {
            None
        }
    }

    /// Get immutable reference to value using key
    ///
    /// * `key`: key
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// hashmap.insert("a".to_string(), 5);
    /// assert_eq!(hashmap.get(&"a".to_string()), Some(&5));
    /// hashmap.remove(&"a".to_string());
    /// assert_eq!(hashmap.get(&"a".to_string()), None);
    /// ```
    pub fn get(&self, k: &K) -> Option<&V> {
        // if slot entry found, return immutable reference to value
        // if no slot found error, probing cycle, the key/value pair does not exist
        match self.find_slot(k) {
            Ok(slot) => match slot {
                Slot::Empty | Slot::Tombstone => None,
                Slot::Entry(_, val) => Some(val),
            },
            Err(_) => None,
        }
    }

    /// Get mutable reference to value using key
    ///
    /// * `key`: key
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// hashmap.insert("a".to_string(), 5);
    /// assert_eq!(hashmap.get_mut(&"a".to_string()), Some(&mut 5));
    /// hashmap.remove(&"a".to_string());
    /// assert_eq!(hashmap.get_mut(&"a".to_string()), None);
    /// ```
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        // if slot entry found, return mutable reference to value
        // if no slot found error, probing cycle, the key/value pair does not exist
        match self.find_slot_mut(k) {
            Ok(slot) => match slot {
                Slot::Empty | Slot::Tombstone => None,
                Slot::Entry(_, val) => Some(val),
            },
            Err(_) => None,
        }
    }

    /// Generate hash index from key
    ///
    /// * `key`: key
    fn gen_hash_index(&self, key: &K) -> usize {
        // generate key hash, then get slot index by mod slot vector capacity
        let mut hasher: FNV1aHasher = FNV1aHasher::new();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        let capacity = u64::try_from(self.slots.capacity()).unwrap();
        usize::try_from(hash % capacity).unwrap()
    }

    /// Find slot for `insert`/`remove`/`get_mut`, and return mutable reference to slot.
    /// If probing cycle is encountered, SlotNotFoundErr is returned.
    ///
    /// * `key`: key
    fn find_slot_mut(&mut self, key: &K) -> Result<&mut Slot<K, V>, SlotNotFoundErr> {
        let capacity = self.slots.capacity();
        // get key hash index
        let hash_index: usize = self.gen_hash_index(key);
        // used to record index of first encountered tombstone;
        // if no entry found with key, and tombstone is encountered,
        // return mutable reference to slot at index of first encountered tombstone
        let mut first_tombstone_index: Option<usize> = None;

        for i in 0..=capacity {
            let index = (hash_index + i * i) % capacity;
            match &self.slots[index] {
                // slot is empty, so no entry found;
                // if encountered tombstones, return mutable reference to slot
                // at index of first encountered tombstones;
                // otherwise return mutable reference to slot at current index
                Slot::Empty => {
                    let index = match first_tombstone_index {
                        Some(index) => index,
                        None => index,
                    };
                    return Ok(&mut self.slots[index]);
                }
                // set first tombstone index if it's None, continue searching
                Slot::Tombstone => {
                    if first_tombstone_index.is_none() {
                        first_tombstone_index = Some(index);
                    }
                    continue;
                }
                // if slot has entry and keys match, return entry slot
                Slot::Entry(entry_key, _) if entry_key == key => {
                    return Ok(&mut self.slots[index]);
                }
                // slot has entry but keys do not match, continue searching
                Slot::Entry(_, _) => continue,
            }
        }
        // slot not found due to probing cycle
        Err(SlotNotFoundErr)
    }

    /// Find slot for `get`, return immutable reference to slot.
    /// If probing cycle is encountered, SlotNotFoundErr is returned.
    ///
    /// * `key`: key
    fn find_slot(&self, key: &K) -> Result<&Slot<K, V>, SlotNotFoundErr> {
        let capacity = self.slots.capacity();
        // get key hash index
        let hash_index: usize = self.gen_hash_index(key);

        for i in 0..=capacity {
            let index = (hash_index + i * i) % capacity;

            match &self.slots[index] {
                // slot is empty, so no entry found, return mutable reference
                // to slot at current index
                Slot::Empty => {
                    return Ok(&self.slots[index]);
                }
                // slot is tombstone, continue searching
                Slot::Tombstone => continue,
                // if slot has entry and keys match, return entry slot
                Slot::Entry(entry_key, _) if entry_key == key => {
                    return Ok(&self.slots[index]);
                }
                // slot has entry but keys do not match, continue searching
                Slot::Entry(_, _) => continue,
            }
        }
        // slot not found due to probing cycle
        Err(SlotNotFoundErr)
    }

    /// Create iterator for hash map
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// hashmap.insert("J".to_string(), 1);
    /// hashmap.insert("Q".to_string(), 2);
    /// hashmap.insert("a".to_string(), 3);
    /// hashmap.insert("l".to_string(), 4);
    /// hashmap.insert("r".to_string(), 5);
    /// hashmap.insert("y".to_string(), 6);
    ///
    /// let pairs = vec![("l", 4), ("J", 1), ("Q", 2), ("y", 6), ("a", 3), ("r", 5)];
    /// let mut iter = hashmap.iter();
    /// for (key, val) in pairs {
    ///     assert_eq!(iter.next(), Some((&key.to_string(), &val)));
    /// }
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            curr_index: 0,
            slots: &self.slots,
        }
    }

    /// Create iterator for hash map
    ///
    /// # Example
    ///
    /// ```
    /// use dsa::hashmap::HashMap;
    /// let mut hashmap = HashMap::<String, usize>::new();
    /// hashmap.insert("J".to_string(), 1);
    /// hashmap.insert("Q".to_string(), 2);
    /// hashmap.insert("a".to_string(), 3);
    /// hashmap.insert("l".to_string(), 4);
    /// hashmap.insert("r".to_string(), 5);
    /// hashmap.insert("y".to_string(), 6);
    ///
    /// let mut iter = hashmap.iter_mut();
    /// for (_, val) in iter {
    ///     *val += 1;
    /// }
    /// let pairs = vec![("l", 5), ("J", 2), ("Q", 3), ("y", 7), ("a", 4), ("r", 6)];
    /// let mut iter = hashmap.iter();
    /// for (key, val) in pairs {
    ///     assert_eq!(iter.next(), Some((&key.to_string(), &val)));
    /// }
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            curr_index: 0,
            slots: &mut self.slots,
        }
    }
}

impl<K, V> Default for HashMap<K, V>
where
    K: Hash + PartialEq + Clone,
    V: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

/// Immutable iterator struct
///
/// * `curr_index`: current index in slot vector
/// * `slots`: immutable reference to slot vector
pub struct Iter<'a, K, V> {
    curr_index: usize,
    slots: &'a Vec<Slot<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    /// Get next item in iterator
    fn next(&mut self) -> Option<Self::Item> {
        let capacity = self.slots.capacity();
        // iterate through slot vector from current index, if entry found,
        // save next index, and return reference to key/value pair
        for (index, slot) in self.slots[self.curr_index..].iter().enumerate() {
            match slot {
                Slot::Empty | Slot::Tombstone => (),
                Slot::Entry(key, val) => {
                    self.curr_index = self.curr_index + index + 1;
                    return Some((key, val));
                }
            }
        }
        // if nothing found, iterator is exhausted, set current index to capacity
        // and return None
        self.curr_index = capacity;
        None
    }
}

/// Mutable iterator struct
///
/// * `curr_index`: current index in slot vector
/// * `slots`: mutable reference to slot vector
pub struct IterMut<'a, K, V> {
    curr_index: usize,
    slots: &'a mut Vec<Slot<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    /// Get next item in mutable iterator
    fn next(&mut self) -> Option<Self::Item> {
        let capacity = self.slots.capacity();
        // iterate through slot vector from current index, if entry found,
        // save next index, and return reference to key/value pair
        for (index, slot) in self.slots[self.curr_index..].iter_mut().enumerate() {
            match slot {
                Slot::Empty | Slot::Tombstone => (),
                Slot::Entry(key, val) => {
                    self.curr_index = self.curr_index + index + 1;
                    // Recast key/value reference to pointer then back to reference. This operation
                    // can be dangerous, but is needed in this case and does not cause memory
                    // unsafety.
                    //
                    // Without recast, compiler will complain about lifetime, because &mut self
                    // lifetime is limited to this function scope, while 'a lifetime is beyond
                    // that. This is only the symptom of a bigger problem: the IterMut struct keeps
                    // a mutable reference to vector, so yielding a mutable reference to individual
                    // slot would violate borrow rule.
                    //
                    // However, in this case, memory unsafety is not a concern. The mutable
                    // reference to slot vector guarantees only this function and the mutable
                    // references yielded can mutate the vector. This function does not actually
                    // modify the underlying data, and the yielded mutable reference to individual
                    // slots are distinct, so there is no memory unsafety.
                    //
                    // Unbounded lifetime is also not a problem, as recasted references are bounded
                    // by return type which is annotated with lifetime 'a.
                    //
                    // A more elegant solution would be to just call `iter_mut()` and store the
                    // std::slice::IterMut type as inner iterator in our custom IterMut. The inner
                    // iterator is stored as immutable, and as a result, no lifetime issue. But
                    // this is implemented using unsafe Rust because it's fun to do these mental
                    // gymnastics.
                    //
                    // Reference:
                    // https://users.rust-lang.org/t/the-mutable-reference-lifetime-problem-of-iterators/92988
                    let key_ptr: *const K = key;
                    let val_ptr: *mut V = val;
                    let entry = unsafe { (key_ptr.as_ref().unwrap(), val_ptr.as_mut().unwrap()) };
                    return Some(entry);
                }
            }
        }
        self.curr_index = capacity;
        None
    }
}

/// Into-iterator struct
///
/// * `curr_index`: current index in slot vector
/// * `slots`: slot vector
pub struct IntoIter<K, V> {
    curr_index: usize,
    slots: Vec<Slot<K, V>>,
}

impl<K, V> IntoIterator for HashMap<K, V> {
    type Item = (K, V);

    type IntoIter = IntoIter<K, V>;

    /// Creates into-iterator for hashmap
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            curr_index: 0,
            slots: self.slots,
        }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    /// Get next item in into-iterator
    fn next(&mut self) -> Option<Self::Item> {
        let capacity = self.slots.capacity();
        // iterate through slot vector from current index, if entry found,
        // save next index, and return reference to key/value pair
        for (index, slot) in self.slots[self.curr_index..].iter_mut().enumerate() {
            match mem::replace(slot, Slot::Empty) {
                Slot::Empty | Slot::Tombstone => (),
                Slot::Entry(key, val) => {
                    self.curr_index = self.curr_index + index + 1;
                    return Some((key, val));
                }
            }
        }
        // if nothing found, iterator is exhausted, set current index to capacity
        // and return None
        self.curr_index = capacity;
        None
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, path, vec};

    use serde_json::Value;

    use super::*;

    #[test]
    fn test_fnv1a_hasher() {
        // verify FNV1a hasher actually works
        let strings_and_hashes: Vec<(&str, u64)> = vec![
            ("Lorem", 0x6bb546c779a7f7a0),
            ("ipsum", 0x771a8ce2c3afe78f),
            ("dolor", 0x4a96c9ab771f5a95),
            ("sit", 0x824887195cec987f),
            ("amet,", 0x90c965c2633732ea),
            ("consectetur", 0x1b3513c210870cf2),
            ("adipiscing", 0x8558d89c0bdfcdf2),
            ("elit,", 0xf2d4abad2e32c60f),
            ("sed", 0x823b77195ce1f2f3),
            ("do", 0x08915907b53bb494),
            ("eiusmod", 0x7039ee0db9592ad9),
            ("tempor", 0x407245d72a32dcbe),
            ("incididunt", 0xc764823272fce874),
            ("ut", 0x08c43e07b566e04c),
            ("labore", 0xa27897f887b9db84),
            ("et", 0x088e3e07b53950dc),
            ("dolore", 0xdd939e5b6a4785d0),
            ("magna", 0x3392e9a53d6a243d),
            ("aliqua.", 0x7e8f90f5c7f07d0a),
            ("Ut", 0x09313e07b5c3b22c),
            ("enim", 0x90ffc6605d70ff5c),
        ];

        for (string, hash) in strings_and_hashes {
            let mut hasher = FNV1aHasher::new();
            hasher.write(string.as_bytes());
            assert_eq!(hasher.finish(), hash);
        }
    }

    fn read_json_data() -> Value {
        let json_string = fs::read_to_string(path::Path::new("./unit_test_data/hashmap.json"))
            .expect("Unable to read file");
        serde_json::from_str(json_string.as_str()).unwrap()
    }

    #[derive(Debug)]
    /// Test representation of hash map shape
    ///
    /// * `entry`: key/value pair to remove
    /// * `capacity`: capacity of the hashmap
    /// * `entries`: list of (index, key, value) of hashmap entries
    /// * `tombstones`: list of index of hashmap tombstones
    struct HashMapShape {
        entry: (String, usize),
        capacity: usize,
        entries: Vec<(usize, String, usize)>,
        tombstones: Vec<usize>,
    }

    /// Deserialize hashmap entries
    ///
    /// * `entry`: json data value for one hashmap entry
    fn deserialize_entry(entry: &Value) -> (usize, String, usize) {
        let entry = entry.as_object().unwrap();
        let index = usize::try_from(entry["index"].as_i64().unwrap()).unwrap();
        let key = entry["key"].as_str().unwrap().to_string();
        let value = usize::try_from(entry["value"].as_i64().unwrap()).unwrap();
        (index, key, value)
    }

    /// Deserialize individual hashmap shape in json data
    ///
    /// * `shape`: json data value for one hashmap shape
    fn deserialize_map_shape(shape: &Value) -> HashMapShape {
        let shape = shape.as_object().unwrap();

        // process entry (used for entry removal)
        let entry = if shape.contains_key("entry") {
            let entry = shape["entry"].as_object().unwrap();
            let key = entry["key"].as_str().unwrap().to_string();
            let value = usize::try_from(entry["value"].as_i64().unwrap()).unwrap();
            (key, value)
        } else {
            (String::new(), 0)
        };

        // process hashmap entries
        let hashmap = shape["hashmap"].as_object().unwrap();
        let size = usize::try_from(hashmap["capacity"].as_i64().unwrap()).unwrap();
        let entries = hashmap["entries"]
            .as_array()
            .unwrap()
            .iter()
            .map(deserialize_entry)
            .collect();

        // process hashmap tombstones
        let tombstones = hashmap["tombstones"]
            .as_array()
            .unwrap()
            .iter()
            .map(|i| usize::try_from(i.as_i64().unwrap()).unwrap())
            .collect();

        HashMapShape {
            entry,
            capacity: size,
            entries,
            tombstones,
        }
    }

    /// Deserialize hashmap shapes in json data
    ///
    /// * `order_data`: json data value for list of hashmap shapes
    fn deserialize_map_shapes(order_data: &Value) -> Vec<HashMapShape> {
        order_data
            .as_array()
            .unwrap()
            .iter()
            .map(deserialize_map_shape)
            .collect()
    }

    /// Converts hash map shape to slot vector
    ///
    /// * `shape`: hash map shape
    fn gen_slots(shape: HashMapShape) -> Vec<Slot<String, usize>> {
        // initialize slot vector
        let capacity = shape.capacity;
        let mut slots: Vec<Slot<String, usize>> = vec![Slot::Empty; capacity];
        // assign entries
        for (index, key, val) in shape.entries {
            slots[index] = Slot::Entry(key, val);
        }
        // assign tombstones
        for index in shape.tombstones {
            slots[index] = Slot::Tombstone;
        }

        slots
    }

    /// Get entries with keys that hash same hash index (hash % 11 == 4)
    /// These values are used throughout all unit tests
    fn get_entries_with_same_index() -> Vec<(String, usize)> {
        vec![
            ("J".to_string(), 10),
            ("Q".to_string(), 20),
            ("a".to_string(), 30),
            ("l".to_string(), 40),
            ("r".to_string(), 50),
            ("y".to_string(), 60),
        ]
    }

    #[test]
    fn test_new() {
        // new()
        let map: HashMap<char, u32> = HashMap::new();
        let slots = vec![Slot::Empty; INITIAL_CAPACITY];
        assert_eq!(map, HashMap { slots, size: 0 });

        // default()
        let map: HashMap<char, u32> = HashMap::default();
        let slots = vec![Slot::Empty; INITIAL_CAPACITY];
        assert_eq!(map, HashMap { slots, size: 0 });
    }

    #[test]
    fn test_quadratic_probing_insert_remove() {
        // prepare for insert
        let expected_shapes =
            deserialize_map_shapes(&read_json_data()["quadratic_probing"]["insert"]);
        let expected_shapes = get_entries_with_same_index()
            .into_iter()
            .zip(expected_shapes);
        let mut entries_to_insert = get_entries_with_same_index();

        // verify hashmap empty
        let mut map: HashMap<String, usize> = HashMap::new();
        assert!(map.is_empty());
        assert_eq!(map.size(), 0);

        // test insert entries
        for (index, (entry, shape)) in expected_shapes.into_iter().enumerate() {
            // insert
            let (ref key, mut value) = entry;
            map.insert(key.clone(), value);
            // verify map size
            assert!(!map.is_empty());
            assert_eq!(map.size(), index + 1);
            // verify get/get_mut returns correct value
            assert_eq!(map.get(key), Some(&value));
            assert_eq!(map.get_mut(key), Some(&mut value));
            // remove entry from entries_to_insert, and verify entries to insert do not exist
            entries_to_insert.retain(|value| *value != entry);
            for (key, _) in entries_to_insert.iter() {
                assert_eq!(map.get(key), None);
                assert_eq!(map.get_mut(key), None);
            }
            // verify hashmap shape
            assert_eq!(
                map,
                HashMap {
                    slots: gen_slots(shape),
                    size: index + 1
                }
            )
        }

        // prepare for remove
        let expected_shapes =
            deserialize_map_shapes(&read_json_data()["quadratic_probing"]["remove"]);
        let mut existing_entries = get_entries_with_same_index();

        // test remove entries
        for (index, mut shape) in expected_shapes.into_iter().enumerate() {
            // verify map size
            assert!(!map.is_empty());
            assert_eq!(map.size(), 6 - index);
            // remove
            let (key, value) = &mut shape.entry;
            assert_eq!(map.remove(key), Some(*value));
            assert_eq!(map.remove(key), None);
            // verify get/get_mut returns None
            assert_eq!(map.get(key), None);
            assert_eq!(map.get_mut(key), None);
            // remove entry from existing entries, and verify existing entries exist
            existing_entries.retain(|value| value != &mut shape.entry);
            for (key, value) in existing_entries.iter_mut() {
                assert_eq!(map.get(key), Some(&*value));
                assert_eq!(map.get_mut(key), Some(value));
            }
            // verify hashmap shape
            assert_eq!(
                map,
                HashMap {
                    slots: gen_slots(shape),
                    size: 5 - index
                }
            )
        }

        // verify hashmap empty
        assert!(map.is_empty());
        assert_eq!(map.size(), 0);
    }

    #[test]
    fn test_insert_expand() {
        // test for insert expand once load factor reached
        let mut map: HashMap<String, usize> = HashMap::new();
        for (key, value) in get_entries_with_same_index() {
            map.insert(key, value);
        }

        // verify hashmap capacity/shape before expansion
        assert_eq!(map.capacity(), 11);
        assert_eq!(
            map,
            HashMap {
                slots: gen_slots(deserialize_map_shape(
                    &read_json_data()["insert_expand"]["before"]
                )),
                size: 6
            }
        );

        // insert extra item to trigger expansion
        map.insert("B".to_string(), 70);

        // verify hashmap capacity/shape after expansion
        assert_eq!(map.capacity(), 22);
        assert_eq!(
            map,
            HashMap {
                slots: gen_slots(deserialize_map_shape(
                    &read_json_data()["insert_expand"]["after"]
                )),
                size: 7
            }
        );
    }

    #[test]
    fn test_insert_probe_cycle_expand() {
        // test for insert expand caused by probe cycle
        let mut map: HashMap<String, usize> = HashMap::new();
        for (key, value) in get_entries_with_same_index() {
            map.insert(key, value);
        }

        // verify hashmap capacity/shape before expansion
        assert_eq!(map.capacity(), 11);
        assert_eq!(
            map,
            HashMap {
                slots: gen_slots(deserialize_map_shape(
                    &read_json_data()["insert_probe_cycle"]["before"]
                )),
                size: 6
            }
        );

        // insert extra item to trigger probe cycle (hash % 11 == 4)
        map.insert("ab".to_string(), 70);

        // verify hashmap capacity/shape after expansion
        assert_eq!(map.capacity(), 22);
        assert_eq!(
            map,
            HashMap {
                slots: gen_slots(deserialize_map_shape(
                    &read_json_data()["insert_probe_cycle"]["after"]
                )),
                size: 7
            }
        );
    }

    #[test]
    fn test_insert_tombstones() {
        // test insert on tombtones
        let mut map: HashMap<String, usize> = HashMap::new();
        let mut entries = get_entries_with_same_index();
        entries.truncate(5);
        // insert 5 items with same hash index then remove all of them to leave behind tombstones
        for (key, value) in entries.iter() {
            map.insert(key.clone(), *value);
        }
        for (key, _) in entries.iter() {
            map.remove(key);
        }

        // verify hashmap shape before insert
        assert_eq!(
            map,
            HashMap {
                slots: gen_slots(deserialize_map_shape(
                    &read_json_data()["insert_tombstones"]["initial"]
                )),
                size: 0
            }
        );

        // prepare for insert
        let expected_shapes =
            deserialize_map_shapes(&read_json_data()["insert_tombstones"]["insert"]);
        let expected_shapes = entries.into_iter().zip(expected_shapes);

        // test insert and verify hashmap shape
        for (index, (entry, shape)) in expected_shapes.into_iter().enumerate() {
            let (key, value) = entry;
            map.insert(key.to_string(), value);
            assert_eq!(
                map,
                HashMap {
                    slots: gen_slots(shape),
                    size: index + 1
                }
            )
        }
    }

    #[test]
    fn test_insert_replace() {
        // test replace existing entries and verify old value is returned
        let mut map: HashMap<String, usize> = HashMap::new();
        let entries = get_entries_with_same_index();
        for (key, value) in entries.iter() {
            map.insert(key.clone(), *value);
        }

        for (key, value) in entries.iter() {
            map.insert(key.to_string(), *value);
            assert_eq!(map.size(), 6);
            assert_eq!(map.get(key), Some(value));
        }
    }

    #[test]
    fn test_insert_tombstone_cycle() {
        // test insert succeeds even if there is probing cycle from tombstones
        let mut map: HashMap<String, usize> = HashMap::new();
        let entries = get_entries_with_same_index();
        for (key, value) in entries.iter() {
            map.insert(key.clone(), *value);
        }
        for (key, _) in entries.iter() {
            map.remove(key);
        }
        // insert again
        map.insert("a".to_string(), 10);
        assert_eq!(map.get(&"a".to_string()), Some(&10));
    }

    #[test]
    fn test_remove_tombstone_cycle() {
        // test remove returns None even if there is probing cycle from tombstones
        let mut map: HashMap<String, usize> = HashMap::new();
        let entries = get_entries_with_same_index();
        for (key, value) in entries.iter() {
            map.insert(key.clone(), *value);
        }
        for (key, _) in entries.iter() {
            map.remove(key);
        }
        // remove again
        assert_eq!(map.remove(&"test".to_string()), None);
    }

    #[test]
    fn test_iter() {
        // test immutable iterator returns key/value pair in correct order
        // even if there are tombstones.
        let mut map: HashMap<String, usize> = HashMap::new();
        let entries = get_entries_with_same_index();
        for (key, value) in entries.iter() {
            map.insert(key.clone(), *value);
        }
        for key in ["Q", "l", "r"] {
            map.remove(&key.to_string());
        }

        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&"J".to_string(), &10)));
        assert_eq!(iter.next(), Some((&"y".to_string(), &60)));
        assert_eq!(iter.next(), Some((&"a".to_string(), &30)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_mut() {
        // test mutable iterator returns key/value pair in correct order
        // even if there are tombstones.
        let mut map: HashMap<String, usize> = HashMap::new();
        let entries = get_entries_with_same_index();
        for (key, value) in entries.iter() {
            map.insert(key.clone(), *value);
        }
        for key in ["Q", "l", "r"] {
            map.remove(&key.to_string());
        }

        // for each key/value pair, increase value by 10
        let mut iter = map.iter_mut();
        let next = iter.next();
        assert_eq!(next, Some((&"J".to_string(), &mut 10)));
        *next.unwrap().1 += 10;
        let next = iter.next();
        assert_eq!(next, Some((&"y".to_string(), &mut 60)));
        *next.unwrap().1 += 10;
        let next = iter.next();
        assert_eq!(next, Some((&"a".to_string(), &mut 30)));
        *next.unwrap().1 += 10;
        assert_eq!(iter.next(), None);

        // verify value are mutated
        let mut iter = map.iter();
        assert_eq!(iter.next(), Some((&"J".to_string(), &20)));
        assert_eq!(iter.next(), Some((&"y".to_string(), &70)));
        assert_eq!(iter.next(), Some((&"a".to_string(), &40)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_into_iter() {
        // test into-iterator returns key/value pair in correct order
        // even if there are tombstones
        let mut map: HashMap<String, usize> = HashMap::new();
        let entries = get_entries_with_same_index();
        for (key, value) in entries.iter() {
            map.insert(key.clone(), *value);
        }
        for key in ["Q", "l", "r"] {
            map.remove(&key.to_string());
        }

        let mut iter = map.into_iter();
        assert_eq!(iter.next(), Some(("J".to_string(), 10)));
        assert_eq!(iter.next(), Some(("y".to_string(), 60)));
        assert_eq!(iter.next(), Some(("a".to_string(), 30)));
        assert_eq!(iter.next(), None);
    }
}
