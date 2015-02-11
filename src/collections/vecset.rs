/**
 * A set implemented as a binary vector.
 */
use std::borrow::BorrowFrom;
use std::cmp::Ordering;
use std::iter::{range_step, repeat};
use std::iter::FromIterator;
use std::default::Default;
use std::slice;

use test::Bencher;

/**
 * A set implemented using a sorted vector. Due to memory locality and 
 * caching, this set implementation will generally be faster than the 
 * HashSet for moderately-sized sets with smallish keys. 
 *
 * Benchmarks show that it outperforms the HashSet up to around 
 * 10,000 items; but your mileage may vary depending on the size of 
 * your cache and the sixe of the elements you store.
 */
#[derive(Clone, PartialEq, Eq)]
pub struct VecSet<T> {
    items: Vec<T>
}

/**
 * It is assumed that comparing T's for ordering is cheap.
 */
impl<T: Ord> VecSet<T> {
    pub fn new() -> VecSet<T> {
        VecSet { items: Vec::new() }
    }

    pub fn with_capacity(n: usize) -> VecSet<T> {
        VecSet { items: Vec::with_capacity(n) }
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    /**
     * Inserts an element into the set. Returns true if the element was added, 
     * or false if it already existed in the set.
     */
    pub fn insert(&mut self, v: T) -> bool {
        if self.items.is_empty() || (v > self.items[self.items.len()-1]) {
            self.items.push(v);
            true
        }
        else {
            let index = lower_bound(self.items.as_slice(), &v);
            if self.items[index] == v {
                false
            } 
            else {
                self.items.insert(index, v);
                true
            }
        }
    }

    /**
     * Removes an element from the set. Returns true if the element was removed
     * and false if the element was not in the set to remove.
     */
    pub fn remove(&mut self, v: &T) -> bool {
        if !self.items.is_empty() {
            let index = lower_bound(self.items.as_slice(), v);
            if (index < self.items.len()) && (self.items[index] == *v) {
                self.items.remove(index);
                return true;
            }
        }
        return false;
    }

    pub fn contains(&self, v: &T) -> bool {
        if self.items.is_empty() { return false }

        let index = lower_bound(self.items.as_slice(), v);
        if (index < self.items.len()) && (self.items[index] == *v) {
            true 
        }
        else {
            false
        }    
    }

    /**
     * 
     */
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> slice::Iter<T> {
        self.items.iter()
    }
}

#[test]
fn new_vecset_is_empty() {
    let s = VecSet::<isize>::new();
    assert!(s.is_empty());
    assert!(s.len() == 0);
}

#[test]
fn inserting_elements_affects_size() {
    let mut s : VecSet<usize> = VecSet::new();
    for x in range(0, 100) {
        s.insert(x);
        assert_eq!(x+1, s.len());
    }
}

#[test]
fn inserting_duplicates_does_not_affect_size() {
    let mut s : VecSet<isize> = FromIterator::from_iter(range(1,5));
    s.insert(1);
    s.insert(2);
    s.insert(3);
    s.insert(4);
    assert_eq!(4, s.len());
}

#[test]
fn inserting_in_random_order_creates_valid_set() {
    let mut s : VecSet<isize> = FromIterator::from_iter(
        [3, 1, 2, 6, 5, 4, 0].iter().map(|& i| i));
    s.insert(1);
    s.insert(2);
    s.insert(3);
    s.insert(4);
    assert_eq!(7, s.len());
}

#[test]
fn removing_items_from_empty_set_returns_false(){
    let mut set : VecSet<isize> = VecSet::new();
    assert_eq!(false, set.remove(&42))
}

#[test]
fn removing_item_returns_true() {
    let mut set : VecSet<isize> = FromIterator::from_iter(range(0,5));
    assert_eq!(5, set.len());
    assert_eq!(true, set.remove(&3));
    assert_eq!(4, set.len());
    assert_eq!(false, set.remove(&3));
    assert_eq!(4, set.len());
}

#[test]
fn removing_first_item_returns_true() {
    let mut set : VecSet<isize> = FromIterator::from_iter(range(0,5));
    assert_eq!(5, set.len());
    assert_eq!(true, set.remove(&0));
    assert_eq!(4, set.len());
    assert_eq!(false, set.remove(&0));
    assert_eq!(4, set.len());
}

#[test]
fn removing_last_item_returns_true() {
    let mut set : VecSet<isize> = FromIterator::from_iter(range(0,5));
    assert_eq!(5, set.len());
    assert_eq!(true, set.remove(&4));
    assert_eq!(4, set.len());
    assert_eq!(false, set.remove(&4));
    assert_eq!(4, set.len());
}
#[test]
fn removing_non_existant_items_returns_false(){
    let mut set : VecSet<isize> = FromIterator::from_iter(range(0,5));
    assert_eq!(5, set.len());
    assert_eq!(false, set.remove(&42));
    assert_eq!(5, set.len());
}


#[config(test)]
static RandomTestData : &'static [usize] = &[
    57,  84,  22,  88,  21,
    71,  71,  10,  3,   56,
     9,  81,  78,  46,  84,
    73,  28,  54,  40,  70,
     9,  86,  6,   7,   53,
    52,   5,  6,   68,  78,
    20,  13,  91,  6,   57,
    50,  95,  18,  64,  95,
    78,  39,  56,  91,  43,
    20,  98,  87,  46,  10,
    44,  20,  90,  10,  49,
    51,  93,  9,   41,  13,
    5,   53,  83,  39,  46,
    99,  14,  66,  94,  77,
    76,  91,  52,  67,  41,
    12,  58,  11,  76,  72,
    88,  63,  7,   82,  8,
    68,  78,  46,  4,   25,
    44,  3,   82,  6,   2,
    32,  7,   100, 94,  87,
];

#[bench]
fn insert_1000_32_vecset(b: &mut Bencher) {
    b.iter(|| {
        let mut v : VecSet<(u64, u64)> = VecSet::new();
        for i in range(0, 10) {
            for x in RandomTestData.iter() {
                let val : u64 = (*x as u64) * 100 * (i+1) as u64; 
                v.insert((val, val));
            }
        }
    })
}

//Comparison benchmark using HashSet 
// #[bench]
// fn insert_1000_32_hashset(b: &mut Bencher) {
//     use std::collections::HashSet;
//
//     b.iter(|| {
//         let mut v : HashSet<(u64, u64)> = HashSet::new();
//         for i in range(0, 10) {
//             for x in RandomTestData.iter() {
//                 let val : u64 = (*x as u64) * 100 * (i+1) as u64; 
//                 v.insert((val, val));
//             }
//         }
//     })
// }

#[bench]
fn remove_1000_32_vecset(b: &mut Bencher) {
    let mut s : VecSet<(u64, u64)> = VecSet::new();
    for i in range(0, 50) {
        for x in RandomTestData.iter() {
            let val : u64 = (*x as u64) * 100 * (i+1) as u64; 
            s.insert((val, val));
        }
    }

    b.iter(|| {
        let mut v = s.clone();
        for i in range(0, 50) {
            for x in RandomTestData.iter() {
                let val : u64 = (*x as u64) * 100 * (i+1) as u64; 
                v.remove(&(val, val));
            }
        }
    })
}

// #[bench]
// fn remove_1000_32_hashset(b: &mut Bencher) {
//     use std::collections::HashSet;
//
//     let mut s : HashSet<(u64, u64)> = HashSet::new();
//     for i in range(0, 50) {
//         for x in RandomTestData.iter() {
//             let val : u64 = (*x as u64) * 100 * (i+1) as u64; 
//             s.insert((val, val));
//         }
//     }
//
//     b.iter(|| {
//         let mut v = s.clone();
//         for i in range(0, 50) {
//             for x in RandomTestData.iter() {
//                 let val : u64 = (*x as u64) * 100 * (i+1) as u64; 
//                 v.remove(&(val, val));
//             }
//         }
//     })
// }


// ----------------------------------------------------------------------------
// Default Trait
// ----------------------------------------------------------------------------

impl<T: Ord> Default for VecSet<T> {
    #[inline]
    fn default() -> VecSet<T> { VecSet::new() }
}

#[test]
fn default_vecset_is_empty() {
    let s : VecSet<usize> = Default::default();
    assert!(s.is_empty());
    assert!(s.len() == 0);  
}

// ----------------------------------------------------------------------------
// FromIterator trait
// ----------------------------------------------------------------------------

impl<T: Ord> FromIterator<T> for VecSet<T> {
    fn from_iter<I: Iterator<Item=T>>(iter: I) -> VecSet<T> {
        let mut result = VecSet::new();
        result.extend(iter);
        result
    }
}

// ----------------------------------------------------------------------------
// Extend trait
// ----------------------------------------------------------------------------

impl<T: Ord> Extend<T> for VecSet<T> {
    fn extend<I: Iterator<Item=T>>(&mut self, mut iter: I) {
        for v in iter {
            self.insert(v);
        }
    }
}

#[test]
fn extending_inserts_elements() {
    let mut s = VecSet::<usize>::new();
    s.extend(range(0,100));
    assert_eq!(100, s.len());
}

#[test]
fn extending_does_not_insert_duplicates_elements() {
    let mut s = VecSet::<usize>::new();
    s.extend(range(0,100));
    s.extend(range(0,100));
    assert_eq!(100, s.len());
}


// ----------------------------------------------------------------------------
// Helper functions
// ----------------------------------------------------------------------------

/**
 * Analogue of the C++ std::lower_bound algorithm.
 *
 * Searches a slice for the smallest item not less than the supplied value. The 
 * slice is assumed to be non-empty and sorted. Uses a binary search to make 
 * things a bit faster.
 *
 * Behaviour is undefied for an unsorted slice.
 */
fn lower_bound<T:Ord>(items: &[T], val: &T) -> usize {
    if items.is_empty() { panic!("Empty slice passed to lower_bound"); }

    let mut limit = items.len();
    let mut base = 0;
    while limit > 0 {
        let index = base + (limit >> 1);
        match items[index].cmp(val) {
            Ordering::Equal => return index,
            Ordering::Greater => (),
            Ordering::Less => {
                base = index + 1;
                limit -= 1; 
            }
        }
        limit = limit >> 1;
    }
    base
}

#[test]
fn lower_bound_finds_single_element() {
    assert!(lower_bound(&[42], &42) == 0);
}

#[test]
fn lower_bound_gives_sensible_bound_on_smaller_single_element() {
    assert!(lower_bound(&[42], &41) == 0);
}

#[test]
fn lower_bound_gives_sensible_bound_on_larger_than_largest_element() {
    assert!(lower_bound(&[42], &43) == 1);
}

#[test]
fn lower_bound_finds_existing_elements() {
    let data : Vec<usize> = FromIterator::from_iter(range(0, 100));
    for x in range(0, 100) {
        assert_eq!(x, lower_bound(data.as_slice(), &x));
    }
}

#[test]
fn lower_bound_finds_appropriate_bound() {
    let data : Vec<usize> = FromIterator::from_iter(range_step(0, 100, 3));
    for x in range(0, 100) {
        assert_eq!((2 + x)/3, lower_bound(data.as_slice(), &x));
    }
}