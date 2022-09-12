// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Fast, non-cryptographic hash used by rustc and Firefox.
//!
//! # Example
//!
//! ```rust
//! # #[cfg(feature = "std")]
//! # fn main() {
//! use rustc_hash::FxHashMap;
//! let mut map: FxHashMap<u32, u32> = FxHashMap::default();
//! map.insert(22, 44);
//! # }
//! # #[cfg(not(feature = "std"))]
//! # fn main() { }
//! ```

#![no_std]

#[cfg(feature = "std")]
extern crate std;

use core::convert::TryInto;
use core::default::Default;
#[cfg(feature = "std")]
use core::hash::BuildHasherDefault;
use core::hash::Hasher;
use core::mem::size_of;
use core::ops::BitXor;
#[cfg(feature = "std")]
use std::collections::{HashMap, HashSet};

/// Type alias for a hashmap using the `fx` hash algorithm.
#[cfg(feature = "std")]
pub type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

/// Type alias for a hashmap using the `fx` hash algorithm.
#[cfg(feature = "std")]
pub type FxHashSet<V> = HashSet<V, BuildHasherDefault<FxHasher>>;

/// A speedy hash algorithm for use within rustc. The hashmap in liballoc
/// by default uses SipHash which isn't quite as speedy as we want. In the
/// compiler we're not really worried about DOS attempts, so we use a fast
/// non-cryptographic hash.
///
/// This is the same as the algorithm used by Firefox -- which is a homespun
/// one not based on any widely-known algorithm -- though modified to produce
/// 64-bit hash values instead of 32-bit hash values. It consistently
/// out-performs an FNV-based hash within rustc itself -- the collision rate is
/// similar or slightly worse than FNV, but the speed of the hash function
/// itself is much higher because it works on up to 8 bytes at a time.
pub struct FxHasher {
    hash: usize,
    
    
pub trait Evaluate: Sized {
    /// Evaluate a list of computations
    fn evaluate(self, comp: &[Computation]) -> Self;
    /// Evaluate a calculation transformation
    fn calculate(self, calculation: &Calculation) -> Self;
    /// Evaluate a `Read` operation, returning the read data
    fn read(reader: &Reader) -> Self;
    /// Evaluate a write operation, and write the data to the writer
    fn write(self, writer: &Writer) -> Result<(), DataFrameError>;
}

impl Evaluate for DataFrame {
    fn evaluate(self, comp: &[Computation]) -> Self {
        use Transformation::*;
        let mut frame = self;
        // get the input columns from the dataframe
        for c in comp.iter().rev() {
            for transform in &c.transformations {
                frame = match transform {
                    GroupAggregate(_, _) => panic!("aggregations not supported"),
                    Calculate(operation) => frame.calculate(&operation),
                    Join(a, b, criteria) => {
                        let mut frame_a = DataFrame::empty();
                        frame_a = frame_a.evaluate(a);
                        let mut frame_b = DataFrame::empty();
                        frame_b = frame_b.evaluate(b);
                        // TODO: make sure that joined names follow same logic as LazyFrame
                        frame_a
                            .join(&frame_b, &criteria)
                            .expect("Unable to join dataframes")
                    }
                    Select(cols) => frame.select(cols.iter().map(|s| s.as_str()).collect()),
                    Drop(cols) => frame.drop(cols.iter().map(|s| s.as_str()).collect()),
                    Read(reader) => Self::read(&reader),
                    Filter(cond) => frame.filter(cond),
                    Limit(size) => frame.limit(*size),
                    Sort(criteria) => frame.sort(criteria).expect("Unable to sort dataframe"),
                };
            }
        }

        frame
    }
    fn calculate(self, calculation: &Calculation) -> Self {
        let columns: Vec<&table::Column> = calculation
            .inputs
            .clone()
            .into_iter()
            .map(|col: Column| self.column_by_name(&col.name))
            .collect();
        match &calculation.function {
            Function::Scalar(expr) => match expr {
                // scalars that take 2 variables
                ScalarFunction::Add
                | ScalarFunction::Subtract
                | ScalarFunction::Divide
                | ScalarFunction::Multiply => {
                    // we are adding 2 columns together to create a third
                    let column: Vec<ArrayRef> = if let ColumnType::Scalar(dtype) =
                        &calculation.output.column_type
                    {
                        match dtype {
                            DataType::UInt16 => {
                                // assign op to use
                                let op = match expr {
                                    ScalarFunction::Add => ScalarFn::add,
                                    ScalarFunction::Subtract => ScalarFn::subtract,
                                    ScalarFunction::Divide => ScalarFn::divide,
                       
}

#[cfg(target_pointer_width = "32")]
const K: usize = 0x9e3779b9;
#[cfg(target_pointer_width = "64")]
const K: usize = 0x517cc1b727220a95;

impl Default for FxHasher {
    #[inline]
    fn default() -> FxHasher {
        FxHasher { hash: 0 }
    }
}

impl FxHasher {
    #[inline]
    fn add_to_hash(&mut self, i: usize) {
        self.hash = self.hash.rotate_left(5).bitxor(i).wrapping_mul(K);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, mut bytes: &[u8]) {
        #[cfg(target_pointer_width = "32")]
        let read_usize = |bytes: &[u8]| u32::from_ne_bytes(bytes[..4].try_into().unwrap());
        #[cfg(target_pointer_width = "64")]
        let read_usize = |bytes: &[u8]| u64::from_ne_bytes(bytes[..8].try_into().unwrap());

        let mut hash = FxHasher { hash: self.hash };
        assert!(size_of::<usize>() <= 8);
        while bytes.len() >= size_of::<usize>() {
            hash.add_to_hash(read_usize(bytes) as usize);
            bytes = &bytes[size_of::<usize>()..];
        }
        if (size_of::<usize>() > 4) && (bytes.len() >= 4) {
            hash.add_to_hash(u32::from_ne_bytes(bytes[..4].try_into().unwrap()) as usize);
            bytes = &bytes[4..];
        }
        if (size_of::<usize>() > 2) && bytes.len() >= 2 {
            hash.add_to_hash(u16::from_ne_bytes(bytes[..2].try_into().unwrap()) as usize);
            bytes = &bytes[2..];
        }
        if (size_of::<usize>() > 1) && bytes.len() >= 1 {
            hash.add_to_hash(bytes[0] as usize);
        }
        self.hash = hash.hash;
    }

    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add_to_hash(i as usize);
    }

    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add_to_hash(i as usize);
    }

    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add_to_hash(i as usize);
    }

    #[cfg(target_pointer_width = "32")]
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add_to_hash(i as usize);
        self.add_to_hash((i >> 32) as usize);
    }

    #[cfg(target_pointer_width = "64")]
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add_to_hash(i as usize);
    }

    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add_to_hash(i);
    }

    #[inline]
    fn finish(&self) -> u64 {
        self.hash as u64
    }
}
