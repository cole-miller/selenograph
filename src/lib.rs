#![no_std]

extern crate alloc;

use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::convert::{TryFrom, TryInto};
use core::hash::{BuildHasher, Hash, Hasher};
use hashbrown::raw::RawTable;
use ordered_float::OrderedFloat;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Key {
    Bool(bool),
    Integer(i128),
    F32(OrderedFloat<f32>),
    F64(OrderedFloat<f64>),
    Char(char),
    String(Box<str>),
    Bytes(Box<[u8]>),
    Option(Option<Box<Self>>),
    Unit,
    Variant(u32, Box<Self>),
    Seq(Box<[Self]>),
    Map(BTreeMap<Self, Self>),
}

pub struct Serializer;

pub struct SerializeSeq(Vec<Key>);

impl serde::ser::SerializeSeq for SerializeSeq {
    type Ok = Key;

    type Error = Error;

    fn serialize_element<T: serde::Serialize + ?Sized>(
        &mut self,
        v: &T,
    ) -> Result<(), Self::Error> {
        self.0.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Seq(self.0.into()))
    }
}

impl serde::ser::SerializeTuple for SerializeSeq {
    type Ok = Key;

    type Error = Error;

    fn serialize_element<T: serde::Serialize + ?Sized>(
        &mut self,
        v: &T,
    ) -> Result<(), Self::Error> {
        self.0.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Seq(self.0.into()))
    }
}

impl serde::ser::SerializeTupleStruct for SerializeSeq {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: serde::Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Self::Error> {
        self.0.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Seq(self.0.into()))
    }
}

impl serde::ser::SerializeStruct for SerializeSeq {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: serde::Serialize + ?Sized>(
        &mut self,
        _name: &'static str,
        v: &T,
    ) -> Result<(), Self::Error> {
        self.0.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Seq(self.0.into()))
    }
}

pub struct SerializeTupleVariant(u32, Vec<Key>);

impl serde::ser::SerializeTupleVariant for SerializeTupleVariant {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: serde::Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Self::Error> {
        self.1.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Variant(self.0, Box::new(Key::Seq(self.1.into()))))
    }
}

impl serde::ser::SerializeStructVariant for SerializeTupleVariant {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: serde::Serialize + ?Sized>(
        &mut self,
        _name: &'static str,
        v: &T,
    ) -> Result<(), Self::Error> {
        self.1.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Variant(self.0, Box::new(Key::Seq(self.1.into()))))
    }
}

pub struct SerializeMap(BTreeMap<Key, Key>, Option<Key>, Option<Key>);

impl serde::ser::SerializeMap for SerializeMap {
    type Ok = Key;

    type Error = Error;

    fn serialize_key<T: serde::Serialize + ?Sized>(&mut self, key: &T) -> Result<(), Self::Error> {
        if let Some(k) = self.1.take() {
            Err(Error::OddKey(k))
        } else if let Some(v) = self.2.take() {
            self.0.insert(key.serialize(Serializer)?, v);

            Ok(())
        } else {
            self.1 = Some(key.serialize(Serializer)?);

            Ok(())
        }
    }

    fn serialize_value<T: serde::Serialize + ?Sized>(
        &mut self,
        value: &T,
    ) -> Result<(), Self::Error> {
        if let Some(v) = self.2.take() {
            Err(Error::OddValue(v))
        } else if let Some(k) = self.1.take() {
            self.0.insert(k, value.serialize(Serializer)?);

            Ok(())
        } else {
            self.2 = Some(value.serialize(Serializer)?);

            Ok(())
        }
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Map(self.0))
    }
}

#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    BigU128(u128),
    OddKey(Key),
    OddValue(Key),
    Custom(String),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl serde::ser::Error for Error {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Custom(msg.to_string())
    }
}

impl serde::Serializer for Serializer {
    type Ok = Key;

    type Error = Error;

    type SerializeSeq = SerializeSeq;

    type SerializeTuple = SerializeSeq;

    type SerializeTupleStruct = SerializeSeq;

    type SerializeTupleVariant = SerializeTupleVariant;

    type SerializeMap = SerializeMap;

    type SerializeStruct = SerializeSeq;

    type SerializeStructVariant = SerializeTupleVariant;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Bool(v))
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v))
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Integer(v as i128))
    }

    fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
        i128::try_from(v)
            .map(Key::Integer)
            .map_err(|_| Error::BigU128(v))
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        Ok(Key::F32(OrderedFloat(v)))
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        Ok(Key::F64(OrderedFloat(v)))
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Char(v))
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        Ok(Key::String(v.to_owned().into()))
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Bytes(v.to_owned().into()))
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Option(None))
    }

    fn serialize_some<T: serde::Serialize + ?Sized>(self, v: &T) -> Result<Self::Ok, Self::Error> {
        let ser = v.serialize(self)?;

        Ok(Key::Option(Some(Box::new(ser))))
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Unit)
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Variant(index, Box::new(Key::Unit)))
    }

    fn serialize_newtype_struct<T: serde::Serialize + ?Sized>(
        self,
        _name: &'static str,
        v: &T,
    ) -> Result<Self::Ok, Self::Error> {
        v.serialize(self)
    }

    fn serialize_newtype_variant<T: serde::Serialize + ?Sized>(
        self,
        _name: &'static str,
        index: u32,
        _variant: &'static str,
        v: &T,
    ) -> Result<Self::Ok, Self::Error> {
        let ser = v.serialize(self)?;

        Ok(Key::Variant(index, Box::new(ser)))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(SerializeSeq(if let Some(z) = len {
            Vec::with_capacity(z)
        } else {
            Vec::new()
        }))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(SerializeSeq(Vec::with_capacity(len)))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        self.serialize_tuple(len)
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(SerializeTupleVariant(index, Vec::with_capacity(len)))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(SerializeMap(BTreeMap::new(), None, None))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        self.serialize_tuple(len)
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        self.serialize_tuple_variant("", index, "", len)
    }

    fn collect_str<T: core::fmt::Display + ?Sized>(self, v: &T) -> Result<Self::Ok, Self::Error> {
        Ok(Key::String(v.to_string().into()))
    }
}

#[derive(Clone, Copy)]
struct Offset(usize);

impl Offset {
    fn translate_index(&self, x: i128) -> Option<usize> {
        (self.0 as i128).checked_add(x)?.try_into().ok()
    }
}

pub struct Table<T, S = ahash::RandomState> {
    offset_of_zero: Offset,
    slice_part: Box<[Option<T>]>,
    hash_builder: S,
    hash_part: RawTable<(Key, T)>,
}

fn hashit<X: Hash, S: BuildHasher>(builder: &S, val: &X) -> u64 {
    let mut state = builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

pub enum Pair<'a, T> {
    Implicit(i128, &'a T),
    Explicit(&'a (Key, T)),
}

impl<'a, T> Pair<'a, T> {
    pub fn value(self) -> &'a T {
        match self {
            Self::Implicit(_, val) => val,
            Self::Explicit((_, val)) => val,
        }
    }
}

pub enum PairMut<'a, T> {
    Implicit(i128, &'a mut T),
    Explicit(&'a mut (Key, T)),
}

impl<'a, T> PairMut<'a, T> {
    pub fn value(self) -> &'a mut T {
        match self {
            Self::Implicit(_, val) => val,
            Self::Explicit((_, val)) => val,
        }
    }
}

impl<T, S: BuildHasher> Table<T, S> {
    pub fn get(&self, key: &Key) -> Option<&T> {
        self.get_pair(key).map(Pair::value)
    }

    pub fn get_mut(&mut self, key: &Key) -> Option<&mut T> {
        self.get_pair_mut(key).map(PairMut::value)
    }

    pub fn get_pair(&self, key: &Key) -> Option<Pair<'_, T>> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_builder,
            hash_part,
        } = self;

        if let Key::Integer(x) = key {
            if let Some(i) = offset_of_zero
                .translate_index(*x)
                .filter(|&i| i < slice_part.len())
            {
                return slice_part[i].as_ref().map(|v| Pair::Implicit(*x, v));
            }
        }

        let hash = hashit(hash_builder, key);
        hash_part.get(hash, |(k, _)| k == key).map(Pair::Explicit)
    }

    pub fn get_pair_mut(&mut self, key: &Key) -> Option<PairMut<'_, T>> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_builder,
            hash_part,
        } = self;

        if let Key::Integer(x) = key {
            if let Some(i) = offset_of_zero
                .translate_index(*x)
                .filter(|&i| i < slice_part.len())
            {
                return slice_part[i].as_mut().map(|v| PairMut::Implicit(*x, v));
            }
        }

        let hash = hashit(hash_builder, key);
        hash_part
            .get_mut(hash, |(k, _)| k == key)
            .map(PairMut::Explicit)
    }

    pub fn insert(&mut self, key: Key, value: T) -> Option<T> {
        let Self {
            offset_of_zero,
            slice_part,
            hash_builder,
            hash_part,
        } = self;

        // If the key is an integer and could live in the slice part, put the value there.
        if let Key::Integer(x) = &key {
            if let Some(i) = offset_of_zero
                .translate_index(*x)
                .filter(|&i| i < slice_part.len())
            {
                return core::mem::replace(&mut slice_part[i], Some(value));
            }
        }

        // Otherwise, if the key is present in the hash part, replace the corresponding value and return it.
        let hash = hashit(hash_builder, &key);
        if let Some((_, old)) = hash_part.get_mut(hash, |(k, _)| k == &key) {
            return Some(core::mem::replace(old, value));
        }

        // Otherwise, attempt to insert the pair into the hash part without growing it.
        if let Err((key, value)) = hash_part.try_insert_no_grow(hash, (key, value)) {
            // Nope, the table needs to grow.
            todo!()
        }

        None
    }
}
