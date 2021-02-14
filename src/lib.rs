#![no_std]
#![allow(clippy::derive_hash_xor_eq)]

extern crate alloc;

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::convert::TryInto;
use core::hash::{BuildHasher, Hash, Hasher};
#[allow(unused)]
use core::mem::{replace, swap, take};
use core::ops::Neg;
use hashbrown::raw::RawTable;
use ordered_float::OrderedFloat;
use serde::Serialize;

macro_rules! hash {
    ( $h:expr ; $( $x:expr ),+ ) => {
        $( $x.hash($h); )*
    };
}

macro_rules! digest {
    ( $h:expr ; $( $x:expr ),+ ) => {
        #[allow(clippy::unnecessary_mut_passed)]
        {
            hash! { $h; $( $x ),* }
            $h.finish()
        }
    };
}

macro_rules! build_digest {
    ( $b:expr ; $( $x:expr ),+ ) => {
        {
            let mut hasher = $b.build_hasher();
            digest!(&mut hasher; $( $x ),*)
        }
    };
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Key {
    /// Represents the `bool` primitive type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use std::collections::hash_map::DefaultHasher;
    /// assert_eq!(to_key(&true).unwrap(), Key::Bool(true));
    /// ```
    Bool(bool),
    /// A “normal” integer value.
    ///
    /// Any integer data that fits in an `i128` will be serialized to this variant, including
    /// `u128` values below `1 << 127`. It encompasses all the primitive integer types from the
    /// Serde data model, other than (in part) `u128`.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// assert_eq!(to_key(&5_i8).unwrap(), Key::Integer(5_i128));
    /// assert_eq!(to_key(&17_u64).unwrap(), Key::Integer(17_i128));
    /// assert_eq!(to_key(&101_u128).unwrap(), Key::Integer(101_i128));
    /// ```
    Integer(i128),
    /// A `u128` value that's not representable by `i128`.
    ///
    /// Only `u128` values `>= 1 << 127` will be serialized to this variant.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// assert_eq!(to_key(&(1_u128 << 127)).unwrap(), Key::HighU128(1_u128 << 127));
    /// ```
    HighU128(u128),
    /// Represents the `f32` primitive type in the Serde data model.
    ///
    /// [`ordered_float::OrderedFloat`] is used to enable flexible comparisons and hashing.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use ordered_float::OrderedFloat;
    /// assert_eq!(to_key(&2.5_f32).unwrap(), Key::F32(OrderedFloat(2.5_f32)));
    /// assert_eq!(to_key(&f32::NAN).unwrap(), Key::F32(OrderedFloat(f32::NAN)));
    /// ```
    F32(OrderedFloat<f32>),
    /// Represents the `f64` primitive type in the Serde data model.
    ///
    /// [`ordered_float::OrderedFloat`] is used to enable flexible comparisons and hashing.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use ordered_float::OrderedFloat;
    /// assert_eq!(to_key(&2.5_f64).unwrap(), Key::F64(OrderedFloat(2.5_f64)));
    /// assert_eq!(to_key(&f64::NAN).unwrap(), Key::F64(OrderedFloat(f64::NAN)));
    /// ```
    F64(OrderedFloat<f64>),
    /// Represents the `char` primitive type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// assert_eq!(to_key(&'ξ').unwrap(), Key::Char('ξ'));
    /// ```
    Char(char),
    /// Represents the `string` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use std::borrow::ToOwned;
    /// assert_eq!(
    ///     to_key("Hurr durr I'ma sheep").unwrap(),
    ///     Key::String("Hurr durr I'ma sheep".to_owned().into_boxed_str()),
    /// );
    /// ```
    String(Box<str>),
    /// Represents the `bytes` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use serde::{Serialize, Serializer};
    /// struct B(Vec<u8>);
    ///
    /// impl Serialize for B {
    ///     fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    ///         serializer.serialize_bytes(&self.0)
    ///     }
    /// }
    ///
    /// assert_eq!(
    ///     to_key(&B(vec![0xde, 0xad, 0xbe, 0xef])).unwrap(),
    ///     Key::Bytes(vec![0xde, 0xad, 0xbe, 0xef].into_boxed_slice()),
    /// );
    /// ```
    Bytes(Box<[u8]>),
    /// Represents the `option` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// assert_eq!(to_key(&None::<()>).unwrap(), Key::Option(None));
    /// assert_eq!(
    ///     to_key(&Some(17)).unwrap(),
    ///     Key::Option(Some(Box::new(Key::Integer(17)))),
    /// );
    /// ```
    Option(Option<Box<Self>>),
    /// Represents the `unit` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// assert_eq!(to_key(&()).unwrap(), Key::Unit);
    /// ```
    Unit,
    ///
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use serde_derive::Serialize;
    /// #[derive(Serialize)]
    /// struct X;
    /// assert_eq!(to_key(&X).unwrap(), Key::UnitStruct("X"));
    /// ```
    UnitStruct(&'static str),
    /// Represents the `unit_variant` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use serde_derive::Serialize;
    /// #[derive(Serialize)]
    /// enum Y {
    ///     P,
    /// }
    /// assert_eq!(to_key(&Y::P).unwrap(), Key::UnitVariant("Y", 0));
    /// ```
    UnitVariant(&'static str, u32),
    NewtypeStruct(&'static str, Box<Self>),
    /// Represents the `newtype_variant` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use serde_derive::Serialize;
    /// #[derive(Serialize)]
    /// enum Z {
    ///     Q(u32),
    /// }
    /// assert_eq!(
    ///     to_key(&Z::Q(26)).unwrap(),
    ///     Key::NewtypeVariant("Z", 0, Box::new(Key::Integer(26)))
    /// );
    /// ```
    NewtypeVariant(&'static str, u32, Box<Self>),
    /// Represents the `seq` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use std::borrow::ToOwned;
    /// # use serde_derive::Serialize;
    /// # use ordered_float::OrderedFloat;
    /// assert_eq!(
    ///     to_key([1, 1, 2, 3].as_ref()).unwrap(),
    ///     Key::Seq(vec![
    ///         Key::Integer(1), Key::Integer(1), Key::Integer(2), Key::Integer(3),
    ///     ].into_boxed_slice()),
    /// );
    /// ```
    Seq(Box<[Self]>),
    /// Represents the `tuple` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use std::borrow::ToOwned;
    /// # use ordered_float::OrderedFloat;
    /// # use serde_derive::Serialize;
    /// assert_eq!(
    ///     to_key(&(15, "spang", 99.6_f32)).unwrap(),
    ///     Key::Tuple(vec![
    ///         Key::Integer(15),
    ///         Key::String("spang".to_owned().into_boxed_str()),
    ///         Key::F32(OrderedFloat(99.6))
    ///     ].into_boxed_slice()),
    /// );
    /// ```
    Tuple(Box<[Self]>),
    ///
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use ordered_float::OrderedFloat;
    /// # use serde_derive::Serialize;
    /// #[derive(Serialize)]
    /// struct Cartesian(f32, f32);
    /// assert_eq!(
    ///     to_key(&Cartesian(1.0, 2.0)).unwrap(),
    ///     Key::TupleStruct("Cartesian",
    ///         vec![
    ///             Key::F32(OrderedFloat(1.0)), Key::F32(OrderedFloat(2.0)),
    ///         ].into_boxed_slice()
    ///     ),
    /// );
    ///
    /// #[derive(Serialize)]
    /// struct Polar {
    ///     r: f32,
    ///     theta: f32,
    /// }
    /// assert_eq!(
    ///     to_key(&Polar { r: 10.0, theta: std::f32::consts::PI }).unwrap(),
    ///     Key::TupleStruct("Polar", vec![
    ///         Key::F32(OrderedFloat(10.0)),
    ///         Key::F32(OrderedFloat(std::f32::consts::PI)),
    ///     ].into_boxed_slice()),
    /// );
    /// ```
    TupleStruct(&'static str, Box<[Self]>),
    /// Represents the `tuple_variant` and `struct_variant` types in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use serde_derive::Serialize;
    /// #[derive(Serialize)]
    /// enum V {
    ///    This(i32, i32),
    ///    That { first: i32, second: i32 },
    /// }
    /// assert_eq!(
    ///     to_key(&V::This(1, -1)).unwrap(),
    ///     Key::TupleVariant("V", 0, vec![
    ///         Key::Integer(1), Key::Integer(-1)
    ///     ].into_boxed_slice()),
    /// );
    /// assert_eq!(
    ///     to_key(&V::That { first: 1, second: -1 }).unwrap(),
    ///     Key::TupleVariant("V", 1, vec![
    ///         Key::Integer(1), Key::Integer(-1)
    ///     ].into_boxed_slice()),
    /// );
    /// ```
    TupleVariant(&'static str, u32, Box<[Self]>),
    /// Represents the `map` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use std::collections::BTreeMap;
    /// assert!(matches!(
    ///     to_key(&vec![
    ///         ("Bodleian Library", "Oxford"),
    ///         ("Athenæum", "Boston"),
    ///         ("Herzogin Anna Amalia Library", "Weimar"),
    ///     ].into_iter().collect::<BTreeMap<_, _>>()).unwrap(),
    ///     Key::Map(_),
    /// ));
    Map(Box<[(Self, Self)]>),
}

impl Key {
    fn as_integer(&self) -> Option<i128> {
        if let Self::Integer(x) = self {
            Some(*x)
        } else {
            None
        }
    }
}

impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Bool(x) => {
                0_u32.hash(state);
                x.hash(state);
            }
            Self::Integer(x) => {
                1_u32.hash(state);
                x.hash(state);
            }
            Self::HighU128(x) => {
                2_u32.hash(state);
                x.hash(state);
            }
            Self::F32(x) => {
                3_u32.hash(state);
                x.hash(state);
            }
            Self::F64(x) => {
                4_u32.hash(state);
                x.hash(state);
            }
            Self::Char(x) => {
                5_u32.hash(state);
                x.hash(state);
            }
            Self::String(x) => {
                6_u32.hash(state);
                x.hash(state);
            }
            Self::Bytes(x) => {
                7_u32.hash(state);
                x.hash(state);
            }
            Self::Option(None) => {
                8_u32.hash(state);
            }
            Self::Option(Some(x)) => {
                9_u32.hash(state);
                x.hash(state);
            }
            Self::Unit => {
                10_u32.hash(state);
            }
            Self::UnitStruct(name) => {
                11_u32.hash(state);
                name.hash(state);
            }
            Self::UnitVariant(name, i) => {
                12_u32.hash(state);
                name.hash(state);
                i.hash(state);
            }
            Self::NewtypeStruct(name, x) => {
                13_u32.hash(state);
                name.hash(state);
                x.hash(state);
            }
            Self::NewtypeVariant(name, i, x) => {
                14_u32.hash(state);
                name.hash(state);
                i.hash(state);
                x.hash(state);
            }
            Self::Seq(x) => {
                15_u32.hash(state);
                for u in x.as_ref() {
                    u.hash(state);
                }
                x.len().hash(state);
            }
            Self::Tuple(x) => {
                16_u32.hash(state);
                for u in x.as_ref() {
                    u.hash(state);
                }
            }
            Self::TupleStruct(name, x) => {
                17_u32.hash(state);
                name.hash(state);
                for u in x.as_ref() {
                    u.hash(state);
                }
            }
            Self::TupleVariant(name, i, x) => {
                18_u32.hash(state);
                name.hash(state);
                i.hash(state);
                for t in x.as_ref() {
                    t.hash(state);
                }
            }
            Self::Map(x) => {
                19_u32.hash(state);
                for (t, u) in x.as_ref() {
                    t.hash(state);
                    u.hash(state);
                }
                x.len().hash(state);
            }
        }
    }
}

pub mod ser;

pub use crate::ser::{to_key, Serializer};
pub use crate::ser::{Error, Result};

use crate::ser::hash::to_index;
use crate::ser::integer::to_integer;

#[derive(Clone, Copy)]
struct Offset(usize);

impl Offset {
    fn translate_index(self, i: usize) -> i128 {
        i as i128 - self.0 as i128
    }

    fn translate_index_inv(self, x: i128) -> Option<usize> {
        (self.0 as i128).checked_add(x)?.try_into().ok()
    }
}

pub struct Table<T, S = ahash::RandomState> {
    offset_of_zero: Offset,
    slice_part: Vec<Option<T>>,
    hash_builder: S,
    hash_part: RawTable<(Key, T)>,
}

impl<T, S: Default> Default for Table<T, S> {
    fn default() -> Self {
        Self {
            offset_of_zero: Offset(0),
            slice_part: Vec::new(),
            hash_builder: Default::default(),
            hash_part: RawTable::new(),
        }
    }
}

#[derive(Clone, Copy)]
pub enum Pair<'a, T> {
    Implicit(i128, &'a T),
    Explicit(&'a Key, &'a T),
}

impl<'a, T> Pair<'a, T> {
    pub fn value(self) -> &'a T {
        match self {
            Self::Implicit(_, val) => val,
            Self::Explicit(_, val) => val,
        }
    }
}

pub enum PairMut<'a, T> {
    Implicit(i128, &'a mut T),
    Explicit(&'a Key, &'a mut T),
}

impl<'a, T> PairMut<'a, T> {
    pub fn value(self) -> &'a mut T {
        match self {
            Self::Implicit(_, val) => val,
            Self::Explicit(_, val) => val,
        }
    }
}

const SIZE_BITS: usize = core::mem::size_of::<usize>() * 8;

struct Counts {
    pub nonneg: [usize; SIZE_BITS],
    pub neg: [usize; SIZE_BITS],
}

impl Counts {
    fn new() -> Self {
        Self {
            nonneg: [0; SIZE_BITS],
            neg: [0; SIZE_BITS],
        }
    }

    fn tally(&mut self, ints: impl Iterator<Item = i128>) {
        for x in ints {
            if x >= 0 {
                self.nonneg[SIZE_BITS - x.leading_zeros() as usize] += 1;
            } else {
                self.neg[SIZE_BITS - x.neg().leading_zeros() as usize - 1] += 1;
            }
        }
    }

    fn nonneg_size(&self) -> usize {
        compute_size(&self.nonneg)
    }

    fn neg_size(&self) -> usize {
        compute_size(&self.neg)
    }
}

fn compute_size(counts: &[usize]) -> usize {
    counts
        .iter()
        .copied()
        .enumerate()
        .fold((0, 0), |(tot, z), (i, n)| {
            if n > 0 && 2 * (tot + n) >= 1 << i {
                (tot + n, 1 << i)
            } else {
                (tot + n, z)
            }
        })
        .1
}

enum Iter<'a, T> {
    InSlice(
        i128,
        core::slice::Iter<'a, Option<T>>,
        &'a RawTable<(Key, T)>,
    ),
    InHash(hashbrown::raw::RawIter<(Key, T)>),
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = Pair<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::InSlice(x, it, h) => {
                let v = loop {
                    match it.next() {
                        None => unsafe {
                            *self = Self::InHash(h.iter());
                            return self.next();
                        },
                        Some(None) => *x += 1,
                        Some(Some(v)) => break v,
                    }
                };

                let cur = *x;
                *x += 1;
                Some(Pair::Implicit(cur, v))
            }
            Self::InHash(it) => unsafe {
                it.next()
                    .map(|bkt| bkt.as_ref())
                    .map(|(k, v)| Pair::Explicit(k, v))
            },
        }
    }
}

enum IterMut<'a, T> {
    InSlice(
        i128,
        core::slice::IterMut<'a, Option<T>>,
        &'a mut RawTable<(Key, T)>,
    ),
    InHash(hashbrown::raw::RawIter<(Key, T)>),
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = PairMut<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::InSlice(x, it, h) => {
                let v = loop {
                    match it.next() {
                        None => unsafe {
                            *self = Self::InHash(h.iter());
                            return self.next();
                        },
                        Some(None) => *x += 1,
                        Some(Some(v)) => break v,
                    }
                };

                let cur = *x;
                *x += 1;
                Some(PairMut::Implicit(cur, v))
            }
            Self::InHash(it) => unsafe {
                it.next()
                    .map(|bkt| bkt.as_mut())
                    .map(|(k, v)| PairMut::Explicit(k, v))
            },
        }
    }
}

enum _IntoIter<T> {
    InSlice(i128, alloc::vec::IntoIter<Option<T>>, RawTable<(Key, T)>),
    InHash(hashbrown::raw::RawIntoIter<(Key, T)>),
}

pub struct IntoIter<T>(_IntoIter<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = (Key, T);

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.0 {
            _IntoIter::InSlice(x, it, h) => {
                let v = loop {
                    match it.next() {
                        None => {
                            self.0 = _IntoIter::InHash(replace(h, RawTable::new()).into_iter());
                            return self.next();
                        }
                        Some(None) => *x += 1,
                        Some(Some(v)) => break v,
                    }
                };

                let cur = *x;
                *x += 1;
                Some((Key::Integer(cur), v))
            }
            _IntoIter::InHash(it) => it.next(),
        }
    }
}

impl<T, S: BuildHasher> Table<T, S> {
    pub fn new() -> Self
    where
        S: Default,
    {
        Default::default()
    }

    pub fn iter(&self) -> impl Iterator<Item = Pair<'_, T>> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_part,
            ..
        } = self;

        Iter::InSlice(
            offset_of_zero.translate_index(0),
            slice_part.iter(),
            &hash_part,
        )
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = PairMut<'_, T>> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_part,
            ..
        } = self;

        IterMut::InSlice(
            offset_of_zero.translate_index(0),
            slice_part.iter_mut(),
            hash_part,
        )
    }

    pub fn get_pair<K: Serialize + ?Sized>(&self, key: &K) -> Option<Pair<'_, T>> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_builder,
            hash_part,
        } = self;

        if let Some(x) = to_integer(key) {
            if let Some(i) = offset_of_zero
                .translate_index_inv(x)
                .filter(|&i| i < slice_part.len())
            {
                return slice_part[i].as_ref().map(|v| Pair::Implicit(x, v));
            }
        }

        let index = to_index(&mut hash_builder.build_hasher(), key).unwrap();
        let mut ser = None;
        hash_part
            .get(index.hash, |(k, _)| {
                k == ser.get_or_insert_with(|| to_key(key).unwrap())
            })
            .map(|(k, v)| Pair::Explicit(k, v))
    }

    pub fn get_pair_mut<K: Serialize + ?Sized>(&mut self, key: &K) -> Option<PairMut<'_, T>> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_builder,
            hash_part,
        } = self;

        if let Some(x) = to_integer(key) {
            if let Some(i) = offset_of_zero
                .translate_index_inv(x)
                .filter(|&i| i < slice_part.len())
            {
                return slice_part[i].as_mut().map(|v| PairMut::Implicit(x, v));
            }
        }

        let index = to_index(&mut hash_builder.build_hasher(), key).unwrap();
        let mut ser = None;
        hash_part
            .get_mut(index.hash, |(k, _)| {
                k == ser.get_or_insert_with(|| to_key(key).unwrap())
            })
            .map(|(k, v)| PairMut::Explicit(k, v))
    }

    pub fn insert<K: Serialize + ?Sized>(&mut self, key: &K, value: T) -> Option<T> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_builder,
            hash_part,
        } = self;

        if let Some(i) = to_integer(key).and_then(|x| {
            offset_of_zero
                .translate_index_inv(x)
                .filter(|&i| i < slice_part.len())
        }) {
            return replace(&mut slice_part[i], Some(value));
        }

        let make_ser = || to_key(key).unwrap();
        let index = to_index(&mut hash_builder.build_hasher(), key).unwrap();
        let mut ser = None;
        if let Some((_, v)) =
            hash_part.get_mut(index.hash, |(k, _)| k == ser.get_or_insert_with(make_ser))
        {
            return Some(replace(v, value));
        }

        let ser = ser.unwrap_or_else(make_ser);
        if let Err((ser, value)) = hash_part.try_insert_no_grow(index.hash, (ser, value)) {
            /* 0. count up the integer entries in each size range */
            let mut counts = Counts::new();
            counts.tally(
                slice_part
                    .iter()
                    .enumerate()
                    .filter_map(|(i, v)| v.as_ref().and(Some(i)))
                    .map(|i| offset_of_zero.translate_index(i)),
            );
            counts.tally(unsafe {
                hash_part
                    .iter()
                    .filter_map(|bkt| bkt.as_ref().0.as_integer())
            });
            counts.tally(ser.as_integer().into_iter());

            let (nonneg_size, neg_size) = (counts.nonneg_size(), counts.neg_size());
            let total_size = nonneg_size + neg_size;
            let old_neg_size = replace(&mut offset_of_zero.0, neg_size);
            let old_total_size = slice_part.len();
            let old_nonneg_size = old_total_size - old_neg_size;

            /* 1. move the ejected elements from the slice part to the hash part */
            let mut move_from_index_to_hash_part = |i: usize| {
                if let Some(v) = slice_part[i].take() {
                    let x = Offset(old_neg_size).translate_index(i);
                    hash_part.insert(
                        build_digest!(hash_builder; Key::Integer(x)),
                        (Key::Integer(x), v),
                        |(k, _)| build_digest!(hash_builder; k),
                    );
                }
            };
            (0..old_neg_size.saturating_sub(neg_size)).for_each(&mut move_from_index_to_hash_part);
            ((old_neg_size + nonneg_size)..(old_neg_size + old_nonneg_size))
                .for_each(&mut move_from_index_to_hash_part);

            /* 2. shrink or grow the slice part */
            if total_size <= old_total_size {
                slice_part.truncate(total_size);
                slice_part.shrink_to_fit();
            } else {
                slice_part.reserve_exact(total_size - old_total_size);
                slice_part.resize_with(total_size, Default::default);
            }

            /* 3. rotate the slice part to match the new offset */
            if neg_size <= old_neg_size {
                slice_part.rotate_left(old_neg_size - neg_size);
            } else {
                slice_part.rotate_right(neg_size - old_neg_size);
            }

            /* 4. move any suitable elements from the hash part to the slice part */
            unsafe {
                for bkt in hash_part.iter() {
                    match bkt.as_ref() {
                        (Key::Integer(x), _)
                            if offset_of_zero.translate_index_inv(*x).unwrap_or(usize::MAX)
                                < total_size =>
                        {
                            let i = offset_of_zero.translate_index_inv(*x).unwrap();
                            assert!(replace(&mut slice_part[i], Some(hash_part.remove(bkt).1))
                                .is_none());
                        }
                        _ => {}
                    }
                }
            }

            /* 5. insert the given pair in the right place */
            hash_part.insert(
                index.hash,
                (ser, value),
                |(k, _)| build_digest!(hash_builder; k),
            );
        }

        None
    }

    pub fn remove_pair<K: Serialize + ?Sized>(&mut self, key: &K) -> Option<(Key, T)> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_builder,
            hash_part,
        } = self;

        if let Some(x) = to_integer(key) {
            if let Some(i) = offset_of_zero
                .translate_index_inv(x)
                .filter(|&i| i < slice_part.len())
            {
                return take(&mut slice_part[i]).map(|v| (Key::Integer(x), v));
            }
        }

        let make_ser = || to_key(key).unwrap();
        let index = to_index(&mut hash_builder.build_hasher(), key).unwrap();
        let mut ser = None;
        if let Some((k, v)) =
            hash_part.remove_entry(index.hash, |(k, _)| k == ser.get_or_insert_with(make_ser))
        {
            return Some((k, v));
        }

        None
    }

    pub fn clear(&mut self) {
        self.slice_part.iter_mut().filter_map(take).for_each(drop);
        self.hash_part.clear();
    }
}

impl<T, S> IntoIterator for Table<T, S> {
    type Item = (Key, T);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(_IntoIter::InSlice(
            self.offset_of_zero.translate_index(0),
            self.slice_part.into_iter(),
            self.hash_part,
        ))
    }
}

#[cfg(test)]
mod tests {
    mod hash_consistent {
        use crate::*;
        use ahash::AHasher;
        use alloc::borrow::ToOwned;
        use alloc::collections::BTreeMap;
        use alloc::vec::Vec;
        use alloc::string::String;
        use core::hash::{Hash, Hasher};
        use serde::{Serialize, Serializer};
        use serde_derive::Serialize;

        macro_rules! test_hash_consistent {
            ( $name:ident ; $( $e:expr ),+ ) => {
                #[test]
                fn $name() {
                    $(
                        assert_eq!(to_index(&mut AHasher::default(), &$e).unwrap().hash, {
                            let mut h = AHasher::default();
                            to_key(&$e).unwrap().hash(&mut h);
                            h.finish()
                        });
                    )*
                }
            };
        }

        struct B(Vec<u8>);

        impl Serialize for B {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                serializer.serialize_bytes(&self.0)
            }
        }

        #[derive(Serialize)]
        struct Z;

        #[derive(Serialize)]
        enum U {
            P(String),
            Q,
            R(i8, i16, f64),
        }

        test_hash_consistent! { r#bool; false, true }
        test_hash_consistent! { integer; 0_i8, 17_u64, 101_u128 }
        test_hash_consistent! { high_u128; 1_u128 << 127 }
        test_hash_consistent! { r#f32; 17.5_f32, 0.0_f32, f32::NAN }
        test_hash_consistent! { r#f64; 101.25_f64, 0.0_f64, f64::NAN }
        test_hash_consistent! { r#char; 'ξ', 'e', '&' }
        test_hash_consistent! { string; "Hurr durr I'ma sheep", "" }
        test_hash_consistent! { bytes; B(alloc::vec![0xde, 0xad, 0xbe, 0xef]), B(Vec::new()) }
        test_hash_consistent! { none; None::<()> }
        test_hash_consistent! { some; Some((17, "splang", 1.6)) }
        test_hash_consistent! { unit; (), Z }
        test_hash_consistent! { unit_variant; U::Q }
        test_hash_consistent! { newtype_variant; U::P("all the news that's fit to print".to_owned()) }
        test_hash_consistent! { seq; alloc::vec![1, 1, 2, 3, 5, 8, 13] }
        test_hash_consistent! { tuple; (18, (22, ("Lua", 9), "serde", 8.86)) }
        test_hash_consistent! { tuple_variant; U::R(17, -1, 0.0006) }
        test_hash_consistent! { map;
            alloc::vec![
                ("foo", 16), ("bar", 0), ("qux", -8), ("splang", 111),
            ].into_iter().collect::<BTreeMap<_, _>>()
        }
    }
}
