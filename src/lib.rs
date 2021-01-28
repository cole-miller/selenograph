#![no_std]

extern crate alloc;

use alloc::boxed::Box;
use alloc::string::{String, ToString};
use core::convert::TryInto;
use core::hash::{BuildHasher, Hash, Hasher};
use hashbrown::raw::RawTable;
use ordered_float::OrderedFloat;

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

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Key {
    /// Represents the `bool` primitive type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key, to_hash};
    /// # use std::collections::hash_map::DefaultHasher;
    /// # use std::hash::{Hash, Hasher};
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
    /// # use selenograph::{Key, to_key, to_hash};
    /// # use std::collections::hash_map::DefaultHasher;
    /// # use std::hash::{Hash, Hasher};
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
    /// Represents the `unit` and `unit_struct` types in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use serde_derive::Serialize;
    /// assert_eq!(to_key(&()).unwrap(), Key::Unit);
    ///
    /// #[derive(Serialize)]
    /// struct X;
    /// assert_eq!(to_key(&X).unwrap(), Key::Unit);
    /// ```
    Unit,
    /// Represents the `unit_variant` type in the Serde data model.
    ///
    /// ```
    /// # use selenograph::{Key, to_key};
    /// # use serde_derive::Serialize;
    /// #[derive(Serialize)]
    /// enum Y {
    ///     P,
    /// }
    /// assert_eq!(to_key(&Y::P).unwrap(), Key::UnitVariant(0));
    /// ```
    UnitVariant(u32),
    /// Represents the `newtype_variant` type in the Serde data model.
    ///
    /// The `newtype_struct` type is not represented: `newtype_struct` values are serialized
    /// identically to the wrapped value.
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
    ///     Key::NewtypeVariant(0, Box::new(Key::Integer(26)))
    /// );
    /// ```
    NewtypeVariant(u32, Box<Self>),
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
    /// Represents the `tuple`, `tuple_struct`, and `struct` types in the Serde data model.
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
    ///
    /// #[derive(Serialize)]
    /// struct Cartesian(f32, f32);
    /// assert_eq!(
    ///     to_key(&Cartesian(1.0, 2.0)).unwrap(),
    ///     Key::Tuple(vec![Key::F32(OrderedFloat(1.0)), Key::F32(OrderedFloat(2.0)),
    /// ].into_boxed_slice()));
    ///
    /// #[derive(Serialize)]
    /// struct Polar {
    ///     r: f32,
    ///     theta: f32,
    /// }
    /// assert_eq!(
    ///     to_key(&Polar { r: 10.0, theta: std::f32::consts::PI }).unwrap(),
    ///     Key::Tuple(vec![
    ///         Key::F32(OrderedFloat(10.0)),
    ///         Key::F32(OrderedFloat(std::f32::consts::PI)),
    ///     ].into_boxed_slice()),
    /// );
    /// ```
    Tuple(Box<[Self]>),
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
    ///     Key::TupleVariant(0, vec![
    ///         Key::Integer(1), Key::Integer(-1)
    ///     ].into_boxed_slice()),
    /// );
    /// assert_eq!(
    ///     to_key(&V::That { first: 1, second: -1 }).unwrap(),
    ///     Key::TupleVariant(1, vec![
    ///         Key::Integer(1), Key::Integer(-1)
    ///     ].into_boxed_slice()),
    /// );
    /// ```
    TupleVariant(u32, Box<[Self]>),
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
            Self::UnitVariant(x) => {
                11_u32.hash(state);
                x.hash(state);
            }
            Self::NewtypeVariant(x, y) => {
                12_u32.hash(state);
                x.hash(state);
                y.hash(state);
            }
            Self::Seq(x) => {
                13_u32.hash(state);
                for u in x.as_ref() {
                    u.hash(state);
                }
                x.len().hash(state);
            }
            Self::Tuple(x) => {
                14_u32.hash(state);
                for u in x.as_ref() {
                    u.hash(state);
                }
            }
            Self::TupleVariant(x, y) => {
                15_u32.hash(state);
                x.hash(state);
                for u in y.as_ref() {
                    u.hash(state);
                }
            }
            Self::Map(x) => {
                16_u32.hash(state);
                for (u, v) in x.as_ref() {
                    u.hash(state);
                    v.hash(state);
                }
                x.len().hash(state);
            }
        }
    }
}

pub mod ser {
    use crate::Key;
    use alloc::borrow::ToOwned;
    use alloc::boxed::Box;
    use alloc::string::ToString;
    use alloc::vec::Vec;
    use core::convert::TryFrom;
    use ordered_float::OrderedFloat;

    pub struct Serializer;

    pub struct SerializeSeq(Vec<Key>);

    impl serde::ser::SerializeSeq for SerializeSeq {
        type Ok = Key;

        type Error = crate::Error;

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

        type Error = crate::Error;

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

        type Error = crate::Error;

        fn serialize_field<T: serde::Serialize + ?Sized>(
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

    impl serde::ser::SerializeStruct for SerializeSeq {
        type Ok = Key;

        type Error = crate::Error;

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

    pub struct SerializeTuple(Vec<Key>);

    impl serde::ser::SerializeTuple for SerializeTuple {
        type Ok = Key;

        type Error = crate::Error;

        fn serialize_element<T: serde::Serialize + ?Sized>(
            &mut self,
            value: &T,
        ) -> Result<(), Self::Error> {
            self.0.push(to_key(value)?);

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Key::Tuple(self.0.into()))
        }
    }

    impl serde::ser::SerializeTupleStruct for SerializeTuple {
        type Ok = Key;

        type Error = crate::Error;

        fn serialize_field<T: serde::Serialize + ?Sized>(
            &mut self,
            value: &T,
        ) -> Result<(), Self::Error> {
            self.0.push(to_key(value)?);

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Key::Tuple(self.0.into()))
        }
    }

    impl serde::ser::SerializeStruct for SerializeTuple {
        type Ok = Key;

        type Error = crate::Error;

        fn serialize_field<T: serde::Serialize + ?Sized>(
            &mut self,
            _name: &'static str,
            value: &T,
        ) -> Result<(), Self::Error> {
            self.0.push(to_key(value)?);

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Key::Tuple(self.0.into()))
        }
    }

    pub struct SerializeTupleVariant(u32, Vec<Key>);

    impl serde::ser::SerializeTupleVariant for SerializeTupleVariant {
        type Ok = Key;

        type Error = crate::Error;

        fn serialize_field<T: serde::Serialize + ?Sized>(
            &mut self,
            v: &T,
        ) -> Result<(), Self::Error> {
            self.1.push(v.serialize(Serializer)?);

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Key::TupleVariant(self.0, self.1.into()))
        }
    }

    impl serde::ser::SerializeStructVariant for SerializeTupleVariant {
        type Ok = Key;

        type Error = crate::Error;

        fn serialize_field<T: serde::Serialize + ?Sized>(
            &mut self,
            _name: &'static str,
            v: &T,
        ) -> Result<(), Self::Error> {
            self.1.push(v.serialize(Serializer)?);

            Ok(())
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            Ok(Key::TupleVariant(self.0, self.1.into()))
        }
    }

    pub struct SerializeMap(Vec<(Key, Key)>, Option<Key>);

    impl serde::ser::SerializeMap for SerializeMap {
        type Ok = Key;

        type Error = crate::Error;

        fn serialize_key<T: serde::Serialize + ?Sized>(
            &mut self,
            key: &T,
        ) -> Result<(), Self::Error> {
            if let Some(k) = self.1.take() {
                Err(crate::Error::OddKey(k))
            } else {
                self.1 = Some(key.serialize(Serializer)?);

                Ok(())
            }
        }

        fn serialize_value<T: serde::Serialize + ?Sized>(
            &mut self,
            value: &T,
        ) -> Result<(), Self::Error> {
            if let Some(k) = self.1.take() {
                self.0.push((k, value.serialize(Serializer)?));

                Ok(())
            } else {
                Err(crate::Error::OddValue(to_key(value)?))
            }
        }

        fn end(self) -> Result<Self::Ok, Self::Error> {
            if self.1.is_none() {
                Ok(Key::Map(self.0.into()))
            } else {
                Err(crate::Error::MissingValue)
            }
        }
    }

    impl serde::Serializer for Serializer {
        type Ok = Key;

        type Error = crate::Error;

        type SerializeSeq = SerializeSeq;

        type SerializeTuple = SerializeTuple;

        type SerializeTupleStruct = SerializeTuple;

        type SerializeTupleVariant = SerializeTupleVariant;

        type SerializeMap = SerializeMap;

        type SerializeStruct = SerializeTuple;

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

        fn serialize_some<T: serde::Serialize + ?Sized>(
            self,
            v: &T,
        ) -> Result<Self::Ok, Self::Error> {
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
            Ok(Key::UnitVariant(index))
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

            Ok(Key::NewtypeVariant(index, Box::new(ser)))
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
            _name: &'static str,
            len: usize,
        ) -> Result<Self::SerializeTupleStruct, Self::Error> {
            Ok(SerializeTuple(Vec::with_capacity(len)))
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
            Ok(SerializeTupleVariant(index, Vec::with_capacity(len)))
        }

        fn collect_str<T: core::fmt::Display + ?Sized>(
            self,
            v: &T,
        ) -> Result<Self::Ok, Self::Error> {
            Ok(Key::String(v.to_string().into()))
        }
    }

    pub fn to_key<T: serde::Serialize + ?Sized>(v: &T) -> crate::Result<Key> {
        v.serialize(Serializer)
    }

    pub mod hash {
        use core::convert::TryFrom;
        use core::hash::{Hash, Hasher};
        use ordered_float::OrderedFloat;

        pub struct Serializer<'a, H>(&'a mut H);

        pub struct SerializeSeq<'a, H>(&'a mut H, usize);

        impl<'a, H: Hasher> serde::ser::SerializeSeq for SerializeSeq<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

            fn serialize_element<T: serde::Serialize + ?Sized>(
                &mut self,
                value: &T,
            ) -> Result<(), Self::Error> {
                let _ = to_hash(self.0, value)?;
                self.1 += 1;

                Ok(())
            }

            fn end(self) -> Result<Self::Ok, Self::Error> {
                self.1.hash(self.0);

                Ok(self.0.finish())
            }
        }

        pub struct SerializeTuple<'a, H>(&'a mut H);

        impl<'a, H: Hasher> serde::ser::SerializeTuple for SerializeTuple<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

            fn serialize_element<T: serde::Serialize + ?Sized>(
                &mut self,
                value: &T,
            ) -> Result<(), Self::Error> {
                let _ = to_hash(self.0, value)?;

                Ok(())
            }

            fn end(self) -> Result<Self::Ok, Self::Error> {
                Ok(self.0.finish())
            }
        }

        impl<'a, H: Hasher> serde::ser::SerializeTupleStruct for SerializeTuple<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

            fn serialize_field<T: serde::Serialize + ?Sized>(
                &mut self,
                value: &T,
            ) -> Result<(), Self::Error> {
                let _ = to_hash(self.0, value)?;

                Ok(())
            }

            fn end(self) -> Result<Self::Ok, Self::Error> {
                Ok(self.0.finish())
            }
        }

        impl<'a, H: Hasher> serde::ser::SerializeTupleVariant for SerializeTuple<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

            fn serialize_field<T: serde::Serialize + ?Sized>(
                &mut self,
                value: &T,
            ) -> Result<(), Self::Error> {
                let _ = to_hash(self.0, value)?;

                Ok(())
            }

            fn end(self) -> Result<Self::Ok, Self::Error> {
                Ok(self.0.finish())
            }
        }

        impl<'a, H: Hasher> serde::ser::SerializeStruct for SerializeTuple<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

            fn serialize_field<T: serde::Serialize + ?Sized>(
                &mut self,
                _name: &'static str,
                value: &T,
            ) -> Result<(), Self::Error> {
                let _ = to_hash(self.0, value)?;

                Ok(())
            }

            fn end(self) -> Result<Self::Ok, Self::Error> {
                Ok(self.0.finish())
            }
        }

        impl<'a, H: Hasher> serde::ser::SerializeStructVariant for SerializeTuple<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

            fn serialize_field<T: serde::Serialize + ?Sized>(
                &mut self,
                _name: &'static str,
                value: &T,
            ) -> Result<(), Self::Error> {
                let _ = to_hash(self.0, value)?;

                Ok(())
            }

            fn end(self) -> Result<Self::Ok, Self::Error> {
                Ok(self.0.finish())
            }
        }

        enum State {
            WantKey,
            WantValue,
        }

        pub struct SerializeMap<'a, H>(&'a mut H, State, usize);

        impl<'a, H: Hasher> serde::ser::SerializeMap for SerializeMap<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

            fn serialize_key<T: serde::Serialize + ?Sized>(
                &mut self,
                key: &T,
            ) -> Result<(), Self::Error> {
                if matches!(self.1, State::WantKey) {
                    let _ = to_hash(self.0, key);
                    self.1 = State::WantValue;

                    Ok(())
                } else {
                    Err(Self::Error::OddKey(super::to_key(key)?))
                }
            }

            fn serialize_value<T: serde::Serialize + ?Sized>(
                &mut self,
                value: &T,
            ) -> Result<(), Self::Error> {
                if matches!(self.1, State::WantValue) {
                    let _ = to_hash(self.0, value);
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

                    Ok(self.0.finish())
                } else {
                    Err(crate::Error::MissingValue)
                }
            }
        }

        impl<'a, H: Hasher> serde::Serializer for Serializer<'a, H> {
            type Ok = u64;

            type Error = crate::Error;

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

                Ok(self.0.finish())
            }

            fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_i128(self, v: i128) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                v.hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
                1_u32.hash(self.0);
                (v as i128).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_u128(self, v: u128) -> Result<Self::Ok, Self::Error> {
                if let Ok(i) = i128::try_from(v) {
                    1_u32.hash(self.0);
                    i.hash(self.0);
                } else {
                    2_u32.hash(self.0);
                    v.hash(self.0);
                }

                Ok(self.0.finish())
            }

            fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
                3_u32.hash(self.0);
                OrderedFloat(v).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
                4_u32.hash(self.0);
                OrderedFloat(v).hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
                5_u32.hash(self.0);
                v.hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
                6_u32.hash(self.0);
                v.hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
                7_u32.hash(self.0);
                v.hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
                8_u32.hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_some<T: serde::Serialize + ?Sized>(
                self,
                value: &T,
            ) -> Result<Self::Ok, Self::Error> {
                9_u32.hash(self.0);

                value.serialize(Self(self.0))
            }

            fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
                10_u32.hash(self.0);

                Ok(self.0.finish())
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
                11_u32.hash(self.0);
                index.hash(self.0);

                Ok(self.0.finish())
            }

            fn serialize_newtype_struct<T: serde::Serialize + ?Sized>(
                self,
                _name: &'static str,
                value: &T,
            ) -> Result<Self::Ok, Self::Error> {
                value.serialize(self)
            }

            fn serialize_newtype_variant<T: serde::Serialize + ?Sized>(
                self,
                _name: &'static str,
                index: u32,
                _variant: &'static str,
                value: &T,
            ) -> Result<Self::Ok, Self::Error> {
                12_u32.hash(self.0);
                index.hash(self.0);

                value.serialize(self)
            }

            fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
                13_u32.hash(self.0);

                Ok(SerializeSeq(self.0, 0))
            }

            fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
                14_u32.hash(self.0);

                Ok(SerializeTuple(self.0))
            }

            fn serialize_tuple_struct(
                self,
                _name: &'static str,
                _len: usize,
            ) -> Result<Self::SerializeTupleStruct, Self::Error> {
                14_u32.hash(self.0);

                Ok(SerializeTuple(self.0))
            }

            fn serialize_tuple_variant(
                self,
                _name: &'static str,
                index: u32,
                _variant: &'static str,
                _len: usize,
            ) -> Result<Self::SerializeTupleVariant, Self::Error> {
                15_u32.hash(self.0);
                index.hash(self.0);

                Ok(SerializeTuple(self.0))
            }

            fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
                16_u32.hash(self.0);

                Ok(SerializeMap(self.0, State::WantKey, 0))
            }

            fn serialize_struct(
                self,
                _name: &'static str,
                _len: usize,
            ) -> Result<Self::SerializeStruct, Self::Error> {
                14_u32.hash(self.0);

                Ok(SerializeTuple(self.0))
            }

            fn serialize_struct_variant(
                self,
                _name: &'static str,
                index: u32,
                _variant: &'static str,
                _len: usize,
            ) -> Result<Self::SerializeStructVariant, Self::Error> {
                15_u32.hash(self.0);
                index.hash(self.0);

                Ok(SerializeTuple(self.0))
            }
        }

        pub fn to_hash<H: Hasher, T: serde::Serialize + ?Sized>(
            hasher: &mut H,
            v: &T,
        ) -> crate::Result<u64> {
            v.serialize(Serializer(hasher))
        }
    }
}

pub use crate::ser::hash::to_hash;
pub use crate::ser::{to_key, Serializer};

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
        if let Err((_key, _value)) = hash_part.try_insert_no_grow(hash, (key, value)) {
            // Nope, the table needs to grow.
            todo!()
        }

        None
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
        use core::hash::{Hash, Hasher};
        use serde::{Serialize, Serializer};
        use serde_derive::Serialize;

        macro_rules! test_hash_consistent {
            ( $name:ident ; $( $e:expr ),+ ) => {
                #[test]
                fn $name() {
                    $(
                        assert_eq!(to_hash(&mut AHasher::default(), &$e).unwrap(), {
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
