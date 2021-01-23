#![no_std]

extern crate alloc;

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::convert::TryInto;
use core::hash::{BuildHasher, Hash, Hasher};
use hashbrown::HashMap;
use ordered_float::OrderedFloat;

pub enum GenericKey<S, B> {
    Bool(bool),
    Integer(i128),
    F32(f32),
    F64(f64),
    Char(char),
    String(S),
    ByteArray(B),
    Option(Option<Box<Self>>),
    Unit,
    Newtype(Box<Self>),
    Seq(Vec<Self>),
    Map(BTreeMap<Self, Self>),
}

impl<S, B> GenericKey<S, B> {
    fn discriminant(&self) -> usize {
        match self {
            GenericKey::Bool(..) => 0,
            GenericKey::Integer(..) => 1,
            GenericKey::F32(..) => 2,
            GenericKey::F64(..) => 3,
            GenericKey::Char(..) => 4,
            GenericKey::String(..) => 5,
            GenericKey::ByteArray(..) => 6,
            GenericKey::Option(..) => 7,
            GenericKey::Unit => 8,
            GenericKey::Newtype(..) => 9,
            GenericKey::Seq(..) => 10,
            GenericKey::Map(..) => 11,
        }
    }
}

pub type Key<'a> = GenericKey<&'a str, &'a [u8]>;

pub type OwnedKey = GenericKey<String, Vec<u8>>;

impl<S: AsRef<str>, B: AsRef<[u8]>> PartialEq for GenericKey<S, B> {
    fn eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Bool(x), Self::Bool(y)) if x == y => true,
            (Self::Integer(x), Self::Integer(y)) if x == y => true,
            (Self::F32(x), Self::F32(y)) if OrderedFloat(*x) == OrderedFloat(*y) => true,
            (Self::F64(x), Self::F64(y)) if OrderedFloat(*x) == OrderedFloat(*y) => true,
            (Self::Char(x), Self::Char(y)) if x == y => true,
            (Self::String(x), Self::String(y)) if x.as_ref() == y.as_ref() => true,
            (Self::ByteArray(x), Self::ByteArray(y)) if x.as_ref() == y.as_ref() => true,
            (Self::Option(x), Self::Option(y)) if x == y => true,
            (Self::Unit, Self::Unit) => true,
            (Self::Newtype(x), Self::Newtype(y)) if x == y => true,
            (Self::Seq(x), Self::Seq(y)) if x == y => true,
            (Self::Map(x), Self::Map(y)) if x == y => true,
            _ => false,
        }
    }
}

impl<S: AsRef<str>, B: AsRef<[u8]>> Eq for GenericKey<S, B> {}

impl<S: AsRef<str>, B: AsRef<[u8]>> PartialOrd for GenericKey<S, B> {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl<S: AsRef<str>, B: AsRef<[u8]>> Ord for GenericKey<S, B> {
    fn cmp(&self, rhs: &Self) -> Ordering {
        match (self, rhs) {
            (Self::Bool(x), Self::Bool(y)) => x.cmp(y),
            (Self::Integer(x), Self::Integer(y)) => x.cmp(y),
            (Self::F32(x), Self::F32(y)) => OrderedFloat(*x).cmp(&OrderedFloat(*y)),
            (Self::F64(x), Self::F64(y)) => OrderedFloat(*x).cmp(&OrderedFloat(*y)),
            (Self::Char(x), Self::Char(y)) => x.cmp(y),
            (Self::String(x), Self::String(y)) => x.as_ref().cmp(y.as_ref()),
            (Self::ByteArray(x), Self::ByteArray(y)) => x.as_ref().cmp(y.as_ref()),
            (Self::Option(x), Self::Option(y)) => x.cmp(y),
            (Self::Unit, Self::Unit) => Ordering::Equal,
            (Self::Newtype(x), Self::Newtype(y)) => x.cmp(y),
            (Self::Seq(x), Self::Seq(y)) => x.cmp(y),
            (Self::Map(x), Self::Map(y)) => x.cmp(y),
            (x, y) => x.discriminant().cmp(&y.discriminant()),
        }
    }
}

impl<S: AsRef<str>, B: AsRef<[u8]>> Hash for GenericKey<S, B> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.discriminant().hash(hasher);
        match self {
            Self::Bool(x) => x.hash(hasher),
            Self::Integer(x) => x.hash(hasher),
            Self::F32(x) => OrderedFloat(*x).hash(hasher),
            Self::F64(x) => OrderedFloat(*x).hash(hasher),
            Self::Char(x) => x.hash(hasher),
            Self::String(x) => x.as_ref().hash(hasher),
            Self::ByteArray(x) => x.as_ref().hash(hasher),
            Self::Option(x) => x.hash(hasher),
            Self::Unit => ().hash(hasher),
            Self::Newtype(x) => x.hash(hasher),
            Self::Seq(x) => x.hash(hasher),
            Self::Map(x) => x.hash(hasher),
        }
    }
}

struct Offset(usize);

impl Offset {
    fn translate_index(&self, x: i128) -> Option<usize> {
        (self.0 as i128).checked_add(x)?.try_into().ok()
    }
}

pub struct GenericTable<K, V, S = ahash::RandomState> {
    offset_of_zero: Offset,
    slice_part: Box<[Option<V>]>,
    hash_part: HashMap<K, V, S>,
}

pub type Table<'a, T, S = ahash::RandomState> = GenericTable<Key<'a>, T, S>;

pub type OwningTable<T, S = ahash::RandomState> = GenericTable<OwnedKey, T, S>;

impl<St: AsRef<str>, By: AsRef<[u8]>, T, S: BuildHasher> GenericTable<GenericKey<St, By>, T, S> {
    pub fn get(&self, key: &GenericKey<St, By>) -> Option<&T> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_part,
        } = self;

        if let GenericKey::Integer(x) = key {
            if let Some(i) = offset_of_zero.translate_index(*x) {
                if i < slice_part.len() {
                    return slice_part[i].as_ref();
                }
            }
        }

        hash_part.get(key)
    }

    pub fn get_mut(&mut self, key: &GenericKey<St, By>) -> Option<&mut T> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_part,
        } = self;

        if let GenericKey::Integer(x) = key {
            if let Some(i) = offset_of_zero.translate_index(*x) {
                if i < slice_part.len() {
                    return slice_part[i].as_mut();
                }
            }
        }

        hash_part.get_mut(key)
    }
}
