use crate::Key;
use alloc::borrow::ToOwned;
use alloc::boxed::Box;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::convert::TryFrom;
use ordered_float::OrderedFloat;
use serde::Serialize;

#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    OddKey(Key),
    OddValue(Key),
    MissingValue,
    Custom(String),
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::OddKey(k) => write!(f, "unexpected key in map: {:?}", k),
            Self::OddValue(v) => write!(f, "unexpected value in map: {:?}", v),
            Self::MissingValue => write!(f, "map ended with unpaired key"),
            Self::Custom(msg) => write!(f, "{}", msg),
        }
    }
}

impl serde::ser::Error for Error {
    fn custom<T: core::fmt::Display>(msg: T) -> Self {
        Self::Custom(msg.to_string())
    }
}

pub type Result<T, E = Error> = core::result::Result<T, E>;

pub struct Serializer;

pub struct SerializeSeq(Vec<Key>);

impl serde::ser::SerializeSeq for SerializeSeq {
    type Ok = Key;

    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Self::Error> {
        self.0.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Seq(self.0.into()))
    }
}

pub struct SerializeTuple(Vec<Key>);

impl serde::ser::SerializeTuple for SerializeTuple {
    type Ok = Key;

    type Error = Error;

    fn serialize_element<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        self.0.push(to_key(value)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Tuple(self.0.into()))
    }
}

pub struct SerializeTupleStruct(&'static str, Vec<Key>);

impl serde::ser::SerializeTupleStruct for SerializeTupleStruct {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        self.1.push(to_key(value)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::TupleStruct(self.0, self.1.into()))
    }
}

impl serde::ser::SerializeStruct for SerializeTupleStruct {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        _name: &'static str,
        value: &T,
    ) -> Result<(), Self::Error> {
        self.1.push(to_key(value)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::TupleStruct(self.0, self.1.into()))
    }
}

pub struct SerializeTupleVariant(&'static str, u32, Vec<Key>);

impl serde::ser::SerializeTupleVariant for SerializeTupleVariant {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(&mut self, v: &T) -> Result<(), Self::Error> {
        self.2.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::TupleVariant(self.0, self.1, self.2.into()))
    }
}

impl serde::ser::SerializeStructVariant for SerializeTupleVariant {
    type Ok = Key;

    type Error = Error;

    fn serialize_field<T: Serialize + ?Sized>(
        &mut self,
        _name: &'static str,
        v: &T,
    ) -> Result<(), Self::Error> {
        self.2.push(v.serialize(Serializer)?);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::TupleVariant(self.0, self.1, self.2.into()))
    }
}

pub struct SerializeMap(Vec<(Key, Key)>, Option<Key>);

impl serde::ser::SerializeMap for SerializeMap {
    type Ok = Key;

    type Error = Error;

    fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<(), Self::Error> {
        if let Some(k) = self.1.take() {
            Err(Self::Error::OddKey(k))
        } else {
            self.1 = Some(key.serialize(Serializer)?);

            Ok(())
        }
    }

    fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
        if let Some(k) = self.1.take() {
            self.0.push((k, value.serialize(Serializer)?));

            Ok(())
        } else {
            Err(Self::Error::OddValue(to_key(value)?))
        }
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        if self.1.is_none() {
            Ok(Key::Map(self.0.into()))
        } else {
            Err(Self::Error::MissingValue)
        }
    }
}

impl serde::Serializer for Serializer {
    type Ok = Key;

    type Error = Error;

    type SerializeSeq = SerializeSeq;

    type SerializeTuple = SerializeTuple;

    type SerializeTupleStruct = SerializeTupleStruct;

    type SerializeTupleVariant = SerializeTupleVariant;

    type SerializeMap = SerializeMap;

    type SerializeStruct = SerializeTupleStruct;

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
        Ok(i128::try_from(v)
            .map(Key::Integer)
            .unwrap_or(Key::HighU128(v)))
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

    fn serialize_some<T: Serialize + ?Sized>(self, v: &T) -> Result<Self::Ok, Self::Error> {
        let ser = v.serialize(self)?;

        Ok(Key::Option(Some(Box::new(ser))))
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Ok(Key::Unit)
    }

    fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
        Ok(Key::UnitStruct(name))
    }

    fn serialize_unit_variant(
        self,
        name: &'static str,
        index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok(Key::UnitVariant(name, index))
    }

    fn serialize_newtype_struct<T: Serialize + ?Sized>(
        self,
        name: &'static str,
        v: &T,
    ) -> Result<Self::Ok, Self::Error> {
        let inner = Box::new(to_key(v)?);

        Ok(Key::NewtypeStruct(name, inner))
    }

    fn serialize_newtype_variant<T: Serialize + ?Sized>(
        self,
        name: &'static str,
        index: u32,
        _variant: &'static str,
        v: &T,
    ) -> Result<Self::Ok, Self::Error> {
        let inner = Box::new(v.serialize(self)?);

        Ok(Key::NewtypeVariant(name, index, inner))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(SerializeSeq(if let Some(z) = len {
            Vec::with_capacity(z)
        } else {
            Vec::new()
        }))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(SerializeTuple(Vec::with_capacity(len)))
    }

    fn serialize_tuple_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Ok(SerializeTupleStruct(name, Vec::with_capacity(len)))
    }

    fn serialize_tuple_variant(
        self,
        name: &'static str,
        index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Ok(SerializeTupleVariant(name, index, Vec::with_capacity(len)))
    }

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(SerializeMap(
            if let Some(z) = len {
                Vec::with_capacity(z)
            } else {
                Vec::new()
            },
            None,
        ))
    }

    fn serialize_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        self.serialize_tuple_struct(name, len)
    }

    fn serialize_struct_variant(
        self,
        name: &'static str,
        index: u32,
        _variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(SerializeTupleVariant(name, index, Vec::with_capacity(len)))
    }

    fn collect_str<T: core::fmt::Display + ?Sized>(self, v: &T) -> Result<Self::Ok, Self::Error> {
        Ok(Key::String(v.to_string().into()))
    }

    fn is_human_readable(&self) -> bool {
        false
    }
}

pub fn to_key<T: Serialize + ?Sized>(v: &T) -> Result<Key> {
    v.serialize(Serializer)
}

pub mod hash {
    use core::convert::TryFrom;
    use core::hash::{Hash, Hasher};
    use ordered_float::OrderedFloat;
    use serde::Serialize;

    #[derive(Clone, Debug, Eq, PartialEq)]
    pub struct Index {
        pub hash: u64,
        pub integer: Option<i128>,
    }

    impl Index {
        fn from_hash(hash: u64) -> Self {
            Self {
                hash,
                integer: None,
            }
        }
    }

    pub struct Serializer<'a, H>(&'a mut H);

    pub struct SerializeSeq<'a, H>(&'a mut H, usize);

    impl<'a, H: Hasher> serde::ser::SerializeSeq for SerializeSeq<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        fn serialize_element<T: Serialize + ?Sized>(
            &mut self,
            value: &T,
        ) -> Result<(), Self::Error> {
            let _ = to_index(self.0, value)?;
            self.1 += 1;

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            self.1.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }
    }

    pub struct SerializeTuple<'a, H>(&'a mut H);

    impl<'a, H: Hasher> serde::ser::SerializeTuple for SerializeTuple<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        fn serialize_element<T: Serialize + ?Sized>(
            &mut self,
            value: &T,
        ) -> Result<(), Self::Error> {
            let _ = to_index(self.0, value)?;

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Index::from_hash(self.0.finish()))
        }
    }

    impl<'a, H: Hasher> serde::ser::SerializeTupleStruct for SerializeTuple<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
            let _ = to_index(self.0, value)?;

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Index::from_hash(self.0.finish()))
        }
    }

    impl<'a, H: Hasher> serde::ser::SerializeTupleVariant for SerializeTuple<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        fn serialize_field<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
            let _ = to_index(self.0, value)?;

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Index::from_hash(self.0.finish()))
        }
    }

    impl<'a, H: Hasher> serde::ser::SerializeStruct for SerializeTuple<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        fn serialize_field<T: Serialize + ?Sized>(
            &mut self,
            _name: &'static str,
            value: &T,
        ) -> Result<(), Self::Error> {
            let _ = to_index(self.0, value)?;

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Index::from_hash(self.0.finish()))
        }
    }

    impl<'a, H: Hasher> serde::ser::SerializeStructVariant for SerializeTuple<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        fn serialize_field<T: Serialize + ?Sized>(
            &mut self,
            _name: &'static str,
            value: &T,
        ) -> Result<(), Self::Error> {
            let _ = to_index(self.0, value)?;

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Index::from_hash(self.0.finish()))
        }
    }

    enum State {
        WantKey,
        WantValue,
    }

    pub struct SerializeMap<'a, H>(&'a mut H, State, usize);

    impl<'a, H: Hasher> serde::ser::SerializeMap for SerializeMap<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        fn serialize_key<T: Serialize + ?Sized>(&mut self, key: &T) -> Result<(), Self::Error> {
            if matches!(self.1, State::WantKey) {
                let _ = to_index(self.0, key);
                self.1 = State::WantValue;

                Ok(())
            } else {
                Err(Self::Error::OddKey(super::to_key(key)?))
            }
        }

        fn serialize_value<T: Serialize + ?Sized>(&mut self, value: &T) -> Result<(), Self::Error> {
            if matches!(self.1, State::WantValue) {
                let _ = to_index(self.0, value);
                self.1 = State::WantKey;
                self.2 += 1;

                Ok(())
            } else {
                Err(Self::Error::OddValue(super::to_key(value)?))
            }
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            if matches!(self.1, State::WantKey) {
                self.2.hash(self.0);

                Ok(Index::from_hash(self.0.finish()))
            } else {
                Err(Self::Error::MissingValue)
            }
        }
    }

    impl<'a, H: Hasher> serde::Serializer for Serializer<'a, H> {
        type Ok = Index;

        type Error = super::Error;

        type SerializeSeq = SerializeSeq<'a, H>;

        type SerializeTuple = SerializeTuple<'a, H>;

        type SerializeTupleStruct = SerializeTuple<'a, H>;

        type SerializeTupleVariant = SerializeTuple<'a, H>;

        type SerializeMap = SerializeMap<'a, H>;

        type SerializeStruct = SerializeTuple<'a, H>;

        type SerializeStructVariant = SerializeTuple<'a, H>;

        fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
            0_u32.hash(self.0);
            v.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
            1_u32.hash(self.0);
            let v = v as i128;
            v.hash(self.0);

            Ok(Index {
                hash: self.0.finish(),
                integer: Some(v),
            })
        }

        fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
            if let Ok(i) = i128::try_from(v) {
                1_u32.hash(self.0);
                i.hash(self.0);

                Ok(Index {
                    hash: self.0.finish(),
                    integer: Some(i),
                })
            } else {
                2_u32.hash(self.0);
                v.hash(self.0);

                Ok(Index {
                    hash: self.0.finish(),
                    integer: None,
                })
            }
        }

        fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
            3_u32.hash(self.0);
            OrderedFloat(v).hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
            4_u32.hash(self.0);
            OrderedFloat(v).hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
            5_u32.hash(self.0);
            v.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
            6_u32.hash(self.0);
            v.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
            7_u32.hash(self.0);
            v.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
            8_u32.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_some<T: Serialize + ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error> {
            9_u32.hash(self.0);

            value.serialize(Self(self.0))
        }

        fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
            10_u32.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
            11_u32.hash(self.0);
            name.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_unit_variant(
            self,
            name: &'static str,
            index: u32,
            _variant: &'static str,
        ) -> Result<Self::Ok, Self::Error> {
            12_u32.hash(self.0);
            name.hash(self.0);
            index.hash(self.0);

            Ok(Index::from_hash(self.0.finish()))
        }

        fn serialize_newtype_struct<T: Serialize + ?Sized>(
            self,
            name: &'static str,
            value: &T,
        ) -> Result<Self::Ok, Self::Error> {
            13_u32.hash(self.0);
            name.hash(self.0);

            value.serialize(self)
        }

        fn serialize_newtype_variant<T: Serialize + ?Sized>(
            self,
            name: &'static str,
            index: u32,
            _variant: &'static str,
            value: &T,
        ) -> Result<Self::Ok, Self::Error> {
            14_u32.hash(self.0);
            name.hash(self.0);
            index.hash(self.0);

            value.serialize(self)
        }

        fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
            15_u32.hash(self.0);

            Ok(SerializeSeq(self.0, 0))
        }

        fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
            16_u32.hash(self.0);

            Ok(SerializeTuple(self.0))
        }

        fn serialize_tuple_struct(
            self,
            name: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeTupleStruct, Self::Error> {
            17_u32.hash(self.0);
            name.hash(self.0);

            Ok(SerializeTuple(self.0))
        }

        fn serialize_tuple_variant(
            self,
            name: &'static str,
            index: u32,
            _variant: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeTupleVariant, Self::Error> {
            18_u32.hash(self.0);
            name.hash(self.0);
            index.hash(self.0);

            Ok(SerializeTuple(self.0))
        }

        fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
            19_u32.hash(self.0);

            Ok(SerializeMap(self.0, State::WantKey, 0))
        }

        fn serialize_struct(
            self,
            name: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeStruct, Self::Error> {
            17_u32.hash(self.0);
            name.hash(self.0);

            Ok(SerializeTuple(self.0))
        }

        fn serialize_struct_variant(
            self,
            name: &'static str,
            index: u32,
            _variant: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeStructVariant, Self::Error> {
            18_u32.hash(self.0);
            name.hash(self.0);
            index.hash(self.0);

            Ok(SerializeTuple(self.0))
        }

        fn is_human_readable(&self) -> bool {
            false
        }
    }

    pub fn to_index<H: Hasher, T: Serialize + ?Sized>(
        hasher: &mut H,
        v: &T,
    ) -> super::Result<Index> {
        v.serialize(Serializer(hasher))
    }
}

pub mod integer {
    use alloc::string::{String, ToString};
    use core::convert::TryInto;
    use serde::ser::{Impossible, Serialize};

    pub struct Serializer;

    #[derive(Debug)]
    #[non_exhaustive]
    pub enum Error {
        NotAnInteger,
        Custom(String),
    }

    impl core::fmt::Display for Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                Self::NotAnInteger => write!(f, "this serializer will only serialize integers"),
                Self::Custom(msg) => write!(f, "{}", msg),
            }
        }
    }

    impl serde::ser::Error for Error {
        fn custom<T: core::fmt::Display>(msg: T) -> Self {
            Self::Custom(msg.to_string())
        }
    }

    impl serde::Serializer for Serializer {
        type Ok = i128;

        type Error = Error;

        type SerializeSeq = Impossible<Self::Ok, Self::Error>;

        type SerializeTuple = Impossible<Self::Ok, Self::Error>;

        type SerializeTupleStruct = Impossible<Self::Ok, Self::Error>;

        type SerializeTupleVariant = Impossible<Self::Ok, Self::Error>;

        type SerializeMap = Impossible<Self::Ok, Self::Error>;

        type SerializeStruct = Impossible<Self::Ok, Self::Error>;

        type SerializeStructVariant = Impossible<Self::Ok, Self::Error>;

        fn serialize_bool(self, _v: bool) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
            Ok(v)
        }

        fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
            Ok(v as i128)
        }

        fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
            v.try_into().map_err(|_| Error::NotAnInteger)
        }

        fn serialize_f32(self, _v: f32) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_f64(self, _v: f64) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_char(self, _v: char) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_str(self, _v: &str) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_bytes(self, _v: &[u8]) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_some<T: Serialize + ?Sized>(self, _v: &T) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_unit_variant(
            self,
            _name: &'static str,
            _index: u32,
            _variant: &'static str,
        ) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_newtype_struct<T: Serialize + ?Sized>(
            self,
            _name: &'static str,
            _value: &T,
        ) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_newtype_variant<T: Serialize + ?Sized>(
            self,
            _name: &'static str,
            _index: u32,
            _variant: &'static str,
            _value: &T,
        ) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_tuple_struct(
            self,
            _name: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeTupleStruct, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_tuple_variant(
            self,
            _name: &'static str,
            _index: u32,
            _variant: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeTupleVariant, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_struct(
            self,
            _name: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeStruct, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn serialize_struct_variant(
            self,
            _name: &'static str,
            _index: u32,
            _variant: &'static str,
            _len: usize,
        ) -> Result<Self::SerializeStructVariant, Self::Error> {
            Err(Error::NotAnInteger)
        }

        fn is_human_readable(&self) -> bool {
            false
        }

        fn collect_str<T: core::fmt::Display + ?Sized>(
            self,
            _value: &T,
        ) -> Result<Self::Ok, Self::Error> {
            Err(Error::NotAnInteger)
        }
    }

    pub fn to_integer<T: Serialize + ?Sized>(v: &T) -> Option<i128> {
        v.serialize(Serializer).ok()
    }
}
