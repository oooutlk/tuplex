//! Rust tuple extension.
//!
//! # Features
//!
//! 1. adding/removing element at front/back
//!
//! 2. converting heterogeneous tuples to homogeneous ones
//!
//! 3. checking the length bound of the given tuple in `where` clause
//!
//! # Examples: list operations
//!
//! ```
//! use tuplex::*;
//!
//! let tuple = ();
//! assert_eq!( tuple.len(), 0 );
//!
//! let tuple = tuple.push_front( 0 );
//! assert_eq!( tuple, (0,) );
//! assert_eq!( tuple.len(), 1 );
//!
//! let tuple = tuple.push_front( false );
//! assert_eq!( tuple, (false,0) );
//! assert_eq!( tuple.len(), 2 );
//!
//! let tuple = tuple.push_back( true );
//! assert_eq!( tuple, (false,0,true) );
//! assert_eq!( tuple.len(), 3 );
//!
//! let tuple = tuple.push_back( 1 );
//! assert_eq!( tuple, (false,0,true,1) );
//! assert_eq!( tuple.len(), 4 );
//!
//! let (front,tuple) = tuple.pop_front();
//! assert_eq!( front, false );
//! assert_eq!( tuple, (0,true,1) );
//!
//! let (back,tuple) = tuple.pop_back();
//! assert_eq!( back, 1 );
//! assert_eq!( tuple, (0,true) );
//! ```
//!
//! # Examples: homogeneous/heterogeneous conversions
//!
//! ```
//! use tuplex::*;
//!
//! // `into_homo_tuple()` works because i32 can be converted from i3, u16 and i32.
//! assert_eq!( (3_i8, 7_u16, 21_i32).into_homo_tuple(), (3_i32, 7_i32, 21_i32) );
//! ```
//!
//! # Examples: Length bound
//!
//! 3. checking the length bound of the given tuple in `where` clause
//!
//! ```
//! use tuplex::*;
//!
//! fn foo<Val,Tag>( val: Val ) where Val: LenExceeds<[();3],Tag> {}
//!
//! foo((0,0,0,0));
//! // foo((0,0,0)); // won't compile
//!
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#[cfg(not(feature = "std"))]
pub extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::{boxed::Box, vec, vec::Vec};
#[cfg(not(feature = "std"))]
use core::marker::PhantomData;
#[cfg(feature = "std")]
use std::marker::PhantomData;

/// Denotes a tuple type, the fields of which are of the same type.
/// Up to 32 fields.
#[macro_export]
macro_rules! homo_tuple {
    ($t:ty;  0) => { () };
    ($t:ty;  1) => { ($t,) };
    ($t:ty;  2) => { ($t,$t) };
    ($t:ty;  3) => { ($t,$t,$t) };
    ($t:ty;  4) => { ($t,$t,$t,$t) };
    ($t:ty;  5) => { ($t,$t,$t,$t,$t) };
    ($t:ty;  6) => { ($t,$t,$t,$t,$t,$t) };
    ($t:ty;  7) => { ($t,$t,$t,$t,$t,$t,$t) };
    ($t:ty;  8) => { ($t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty;  9) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 10) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 11) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 12) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 13) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 14) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 15) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 16) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 17) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 18) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 19) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 20) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 21) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 22) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 23) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 24) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 25) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 26) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 27) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 28) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 29) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 30) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 31) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
    ($t:ty; 32) => { ($t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t,$t) };
}

/// Indicate the amount of the tuple's fields.
pub trait Len {
    const LEN: usize;
    fn len( &self ) -> usize;
}

macro_rules! impl_len {
    ( $len:tt, $($index:tt $gen:ident)* ) => {
        #[allow( unused_parens )]
        impl<$($gen),* > Len for ($($gen,)* ) {
            const LEN: usize = $len;
            fn len( &self ) -> usize { $len }
        }

        impl<T> Len for [T; $len] {
            const LEN: usize = $len;
            fn len( &self ) -> usize { $len }
        }
    };
}

impl_len!( 0,      );
impl_len!( 1, 0 T0 );

macro_rules! impl_len_eq {
    ( $len:tt, $($index:tt $gen:ident)* ) => {
        #[allow( unused_parens )]
        impl<$($gen),* > LenEq for ($($gen,)* ) { type Array = [();$len]; }
    };
}

impl_len_eq!( 0,      );
impl_len_eq!( 1, 0 T0 );

/// Adds a `Front` value to the tuple, as the first field.
pub trait PushFront<Front> {
    type Output;
    fn push_front( self, front: Front ) -> Self::Output;
}

macro_rules! impl_push_front {
    ($($index:tt $gen:ident)*) => {
        #[allow( unused_parens )]
        impl<Front,$($gen),*> PushFront<Front> for ($($gen,)*) {
            type Output = (Front,$($gen),*);
            fn push_front( self, front: Front ) -> Self::Output { (front, $(self.$index),*) }
        }
    };
}

impl_push_front!();
impl_push_front!( 0 T0 );

/// Adds a `Back` value to the tuple, as the last field.
pub trait PushBack<Back> {
    type Output;
    fn push_back( self, back: Back ) -> Self::Output;
}

macro_rules! impl_push_back {
    ($($index:tt $gen:ident)*) => {
        #[allow( unused_parens )]
        impl<Back,$($gen),*> PushBack<Back> for ($($gen,)*) {
            type Output = ($($gen,)*Back,);
            fn push_back( self, back: Back ) -> Self::Output { ($(self.$index,)* back,) }
        }
    };
}

impl_push_back!();
impl_push_back!( 0 T0 );

/// Removes the first field of the tuple.
pub trait PopFront {
    type Remain;
    type Front;
    fn pop_front( self ) -> (Self::Front, Self::Remain);
}

macro_rules! impl_pop_front {
    ($($index:tt $gen:ident)*) => {
        #[allow( unused_parens )]
        impl<T0$(,$gen)*> PopFront for (T0,$($gen),*) {
            type Remain = ( ($($gen,)*) );
            type Front = T0;
            fn pop_front( self ) -> (Self::Front, Self::Remain) { (self.0, ($(self.$index,)*)) }
        }
    };
}

impl_pop_front!();

/// Removes the last field of the tuple.
pub trait PopBack {
    type Remain;
    type Back;
    fn pop_back( self ) -> (Self::Back, Self::Remain);
}

macro_rules! impl_pop_back {
    (($($index:tt $gen:ident)*) $($last_index:tt $last_gen:ident)* ) => {
        #[allow( unused_parens )]
        impl<$($gen,)* $($last_gen),*> PopBack for ($($gen,)* $($last_gen,)*) {
            type Remain = ( ($($gen,)*) );
            type Back = $($last_gen)*;
            fn pop_back( self ) -> (Self::Back, Self::Remain) { (self.$($last_index)*, ($(self.$index,)*)) }
        }
    };
}

impl_pop_back!( () 0 T0 );

/// Reshape the linear tuple type to a binary tree, either left associated or right associated.
///
/// # Examples
///
/// ```rust
/// use tuplex::*;
///
/// let _: ((((),bool), i32), String) = <(bool, i32, String) as BinTuple>::LeftAssociated::default();
/// let _: (bool, (i32, (String,()))) = <(bool, i32, String) as BinTuple>::RightAssociated::default();
/// ```
pub trait BinTuple {
    type LeftAssociated;
    type RightAssociated;
}

macro_rules! impl_bin_tuple {
    ($($gen:ident)*) => {
        impl<RemainL,RemainR,T0$(,$gen)*> BinTuple for (T0, $($gen,)*)
            where Self   : PopFront<Remain=RemainR>
                         + PopBack<Remain=RemainL>
                , RemainL: BinTuple
                , RemainR: BinTuple
        {
            type LeftAssociated = (<<Self as PopBack>::Remain as BinTuple>::LeftAssociated, <Self as PopBack>::Back);
            type RightAssociated = (<Self as PopFront>::Front, <<Self as PopFront>::Remain as BinTuple>::RightAssociated);
        }
    };
}

impl BinTuple for () {
    type LeftAssociated = ();
    type RightAssociated = ();
}

impl_bin_tuple!();

/// Converts a tuple from another one, the fields of which can be converted into the fields of the new tuple.
pub trait FromTuple<Tup> {
    fn from_tuple( tup: Tup ) -> Self;
}

macro_rules! impl_tuple_from_tuple {
    ($($index:tt $t:ident $u:ident)*) => {
        impl<$($t,$u),*> FromTuple<($($t,)*)> for ($($u,)*)
            where $($t: Into<$u>),*
        {
            fn from_tuple( _tup: ($($t,)*) ) -> Self {
                ( $( _tup.$index.into(), )* )
            }
        }
    };
}

impl_tuple_from_tuple!(       );
impl_tuple_from_tuple!( 0 T U );

/// Converts a tuple to a new one. This is the counterpart of `FromTuple`.
pub trait IntoTuple<Tup> {
    fn into_tuple( self ) -> Tup;
}

impl<Src,Dest> IntoTuple<Dest> for Src
    where Dest: FromTuple<Src>
{
    fn into_tuple( self ) -> Dest {
        Dest::from_tuple( self )
    }
}

/// Converts a heterogeneous tuple to a homogeneous one.
pub trait IntoHomoTuple<T> {
    type Output: HomoTuple<T>;
    fn into_homo_tuple( self ) -> Self::Output;
}

macro_rules! impl_tuple_into_homo_tuple {
    ($len:tt, $($index:tt $gen:ident)*) => {
        impl<T$(,$gen)*> IntoHomoTuple<T> for ($($gen,)*)
            where $($gen: Into<T>),*
        {
            type Output = homo_tuple!(T; $len);

            fn into_homo_tuple( self ) -> Self::Output {
                ( $( self.$index.into(), )* )
            }
        }
    };
}

impl_tuple_into_homo_tuple!( 0,      );
impl_tuple_into_homo_tuple!( 1, 0 T0 );

/// Homogeneous Tuple's trait.
pub trait HomoTuple<T>
    where Self: Len
              + IntoArray<T>
              + IntoBoxedSlice<T>
{
    /// New type of tuple after fields converted into `Option`.
    type FieldsWrapped;

    /// New type of tuple after the whole tuple has been wrapped.
    type TupleWrapped: IntoIterator<Item=T>;

    /// Converts fields into `Option`.
    fn wrap_fields( self ) -> Self::FieldsWrapped;

    /// Wraps the whole tuple and get a new type.
    fn wrap_tuple( self ) -> Self::TupleWrapped;

    /// Converts the tuple into an iterater which owns the fields, by internally converting all fields into `Option`s.
    fn wrap_into_iter( self ) -> <Self::TupleWrapped as IntoIterator>::IntoIter;
}

pub struct HTup0<T>( PhantomData<T> );

pub struct HTupIter0<T>( PhantomData<T> );

impl<T> Iterator for HTupIter0<T> {
    type Item = T;
    fn next( &mut self ) -> Option<Self::Item> { None }
}

impl<T> IntoIterator for HTup0<T> {
    type Item = T;
    type IntoIter = HTupIter0<T>;

    fn into_iter( self ) -> Self::IntoIter {
        HTupIter0( PhantomData )
    }
}

impl<T> HomoTuple<T> for () {
    type FieldsWrapped = ();
    type TupleWrapped = HTup0<T>;
    fn wrap_fields( self ) -> Self::FieldsWrapped { () }
    fn wrap_tuple( self ) -> Self::TupleWrapped { HTup0( PhantomData )}
    fn wrap_into_iter( self ) -> <Self::TupleWrapped as IntoIterator>::IntoIter { self.wrap_tuple().into_iter() }
}

macro_rules! impl_homo {
    ($wrapper:ident $wrapper_iter:ident $len:tt, $($index:tt)* ) => {
        impl<T> HomoTuple<T> for homo_tuple!( T; $len ) {
            type FieldsWrapped = homo_tuple!( Option<T>; $len );
            type TupleWrapped = $wrapper<T>;

            #[allow( unused_parens )]
            fn wrap_fields( self ) -> Self::FieldsWrapped {
                ( $( Some( self.$index ), )* )
            }

            fn wrap_tuple( self ) -> Self::TupleWrapped {
                $wrapper( self )
            }

            fn wrap_into_iter( self ) -> <Self::TupleWrapped as IntoIterator>::IntoIter { self.wrap_tuple().into_iter() }
        }

        pub struct $wrapper<T>( homo_tuple!( T; $len )) where homo_tuple!( T; $len ): HomoTuple<T>;

        pub struct $wrapper_iter<T> {
            tuple: <homo_tuple!( T; $len ) as HomoTuple<T>>::FieldsWrapped,
            index: usize,
        }

        impl<T> Iterator for $wrapper_iter<T> {
            type Item = T;
            fn next( &mut self ) -> Option<Self::Item> {
                let item = match self.index {
                    $( $index => (self.tuple.$index).take(), )*
                    _ => None,
                };
                self.index += 1;
                item
            }

            fn size_hint( &self ) -> (usize, Option<usize>) {
                let len = $len - self.index;
                (len, Some( len ))
            }
        }

        impl<T> ExactSizeIterator for $wrapper_iter<T> {}

        impl<T> IntoIterator for $wrapper<T> {
            type Item = T;
            type IntoIter = $wrapper_iter<T>;
            fn into_iter( self ) -> Self::IntoIter {
                $wrapper_iter{ tuple: self.0.wrap_fields(), index: 0 }
            }
        }
    };
}

impl_homo!( HTup1 HTupIter1 1, 0 );

/// The map adapter for homogeneous tuples
pub trait MapHomoTuple<T,U>: HomoTuple<T> + Sized {
    type Output: HomoTuple<U> + Sized;
    fn map_homo_tuple( self, f: impl Fn(T)->U ) -> <Self as MapHomoTuple<T,U>>::Output;
}

macro_rules! impl_map_homo_tuple {
    ($len:tt, $($index:tt)*) => {
        impl<T,U> MapHomoTuple<T,U> for homo_tuple!( T; $len ) {
            type Output = homo_tuple!( U; $len );
            fn map_homo_tuple( self, _f: impl Fn(T)->U ) -> <Self as MapHomoTuple<T,U>>::Output {
                ( $( _f( self.$index ), )* )
            }
        }
    };
}

impl_map_homo_tuple!( 0,   );
impl_map_homo_tuple!( 1, 0 );

macro_rules! impl_array_from_tuple {
    ($len:tt, $($index:tt $gen:ident)*) => {
        impl<T$(,$gen)*> FromTuple<($($gen,)*)> for [T; $len]
            where $($gen: Into<T>),*
        {
            fn from_tuple( _tup: ($($gen,)*) ) -> Self {
                [ $( _tup.$index.into() ),* ]
            }
        }
    };
}

impl_array_from_tuple!( 0,      );
impl_array_from_tuple!( 1, 0 T0 );

/// Converts a tuple into an array, where the fields of the tuple can be converted into the same type of the array element.
pub trait IntoArray<T> {
    type Output: Len;
    fn into_array( self ) -> Self::Output;
}

macro_rules! impl_tuple_into_array {
    ($len:tt, $($index:tt $gen:ident)*) => {
        impl<T$(,$gen)*> IntoArray<T> for ($($gen,)*)
            where $($gen: Into<T>),*
        {
            type Output = [T; $len];

            fn into_array( self ) -> Self::Output {
                [ $( (self.$index).into() ),* ]
            }
        }
    };
}

impl_tuple_into_array!( 0,      );
impl_tuple_into_array!( 1, 0 T0 );

/// Converts a tuple into a boxed slice, where the fields of the tuple can be converted into the same type of the slice element.
pub trait IntoBoxedSlice<T> {
    fn into_boxed_slice( self ) -> Box<[T]>;
}

macro_rules! impl_tuple_into_boxed_slice {
    ($len:tt, $($index:tt $gen:ident)*) => {
        impl<T$(,$gen)*> IntoBoxedSlice<T> for ($($gen,)*)
            where $($gen: Into<T>),*
        {
            fn into_boxed_slice( self ) -> Box<[T]> {
                Box::new([ $( (self.$index).into() ),* ])
            }
        }
    };
}

impl_tuple_into_boxed_slice!( 0,      );
impl_tuple_into_boxed_slice!( 1, 0 T0 );

/// Converts a tuple into a `Vec`, where the fields of the tuple can be converted into the same type of the `Vec`'s element.
pub trait IntoVec<T> {
    fn into_vec( self ) -> Vec<T>;
}

macro_rules! impl_tuple_into_vec {
    ($len:tt, $($index:tt $gen:ident)*) => {
        impl<T$(,$gen)*> IntoVec<T> for ($($gen,)*)
            where $(T: From<$gen>),*
        {
            fn into_vec( self ) -> Vec<T> {
                vec![ $( T::from( self.$index )),* ]
            }
        }
    };
}

impl_tuple_into_vec!( 0,      );
impl_tuple_into_vec!( 1, 0 T0 );

/// Marks that `Self` is a value of `T`. The purpose of this trait is for implementing `TupleOf`.
pub trait ValueOf<T> {}

/// A tuple is composed of `T` if all of its fields are values of `T`. See `ValueOf`.
pub trait TupleOf<T> {}

macro_rules! impl_tuple_of {
    ($($t:ident)*) => {
        impl<T,$($t),*> TupleOf<T> for ($($t,)*)
            where $($t: ValueOf<T> ),*
        {
        }
    };
}

impl_tuple_of!();
impl_tuple_of!( T0 );

/// Converts to another type. The purpose of this trait is for implementing `ConvertTuple`.
pub trait Convert {
    type Output;
    fn convert( self ) -> Self::Output;
}

/// Converts a tuple to another one, where the fields of the old tuple can be `Convert`-ed into the fiedls of the new tuple. See `Convert`.
pub trait ConvertTuple {
    type Output;
    fn convert_tuple( self ) -> Self::Output;
}

macro_rules! impl_convert_tuple {
    ($($index:tt $t:ident $u:ident)*) => {
        impl<$($t,$u),*> ConvertTuple for ($($t,)*)
            where $($t: Convert<Output=$u>),*
        {
            type Output = ($($u,)*);
            fn convert_tuple( self ) -> Self::Output {
                ($( Convert::convert( self.$index ),)*)
            }
        }
    };
}

impl_convert_tuple!();
impl_convert_tuple!( 0 T0 U0 );

pub trait Onion { type Type; }

impl Onion for [(); 0] { type Type = (); }
impl Onion for [(); 1] { type Type = ((),); }
impl Onion for [(); 2] { type Type = (((),),); }
impl Onion for [(); 3] { type Type = ((((),),),); }
impl Onion for [(); 4] { type Type = (((((),),),),); }
impl Onion for [(); 5] { type Type = ((((((),),),),),); }
impl Onion for [(); 6] { type Type = (((((((),),),),),),); }
impl Onion for [(); 7] { type Type = ((((((((),),),),),),),); }
impl Onion for [(); 8] { type Type = (((((((((),),),),),),),),); }
impl Onion for [(); 9] { type Type = ((((((((((),),),),),),),),),); }
impl Onion for [();10] { type Type = (((((((((((),),),),),),),),),),); }
impl Onion for [();11] { type Type = ((((((((((((),),),),),),),),),),),); }
impl Onion for [();12] { type Type = (((((((((((((),),),),),),),),),),),),); }
impl Onion for [();13] { type Type = ((((((((((((((),),),),),),),),),),),),),); }
impl Onion for [();14] { type Type = (((((((((((((((),),),),),),),),),),),),),),); }
impl Onion for [();15] { type Type = ((((((((((((((((),),),),),),),),),),),),),),),); }
impl Onion for [();16] { type Type = (((((((((((((((((),),),),),),),),),),),),),),),),); }
impl Onion for [();17] { type Type = ((((((((((((((((((),),),),),),),),),),),),),),),),),); }
impl Onion for [();18] { type Type = (((((((((((((((((((),),),),),),),),),),),),),),),),),),); }
impl Onion for [();19] { type Type = ((((((((((((((((((((),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();20] { type Type = (((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();21] { type Type = ((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();22] { type Type = (((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();23] { type Type = ((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();24] { type Type = (((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();25] { type Type = ((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();26] { type Type = (((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();27] { type Type = ((((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();28] { type Type = (((((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();29] { type Type = ((((((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();30] { type Type = (((((((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();31] { type Type = ((((((((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),); }
impl Onion for [();32] { type Type = (((((((((((((((((((((((((((((((((),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),); }

pub trait LenExceeds<A, O> {}

impl<A,B,O> LenExceeds<A, [(); 1]> for B where A : Onion<Type=O>, B : Onion<Type=(O,)> {}
impl<A,B,O> LenExceeds<A, [(); 2]> for B where A : Onion<Type=O>, B : Onion<Type=((O,),)> {}
impl<A,B,O> LenExceeds<A, [(); 3]> for B where A : Onion<Type=O>, B : Onion<Type=(((O,),),)> {}
impl<A,B,O> LenExceeds<A, [(); 4]> for B where A : Onion<Type=O>, B : Onion<Type=((((O,),),),)> {}
impl<A,B,O> LenExceeds<A, [(); 5]> for B where A : Onion<Type=O>, B : Onion<Type=(((((O,),),),),)> {}
impl<A,B,O> LenExceeds<A, [(); 6]> for B where A : Onion<Type=O>, B : Onion<Type=((((((O,),),),),),)> {}
impl<A,B,O> LenExceeds<A, [(); 7]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((O,),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [(); 8]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((O,),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [(); 9]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((O,),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();10]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((O,),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();11]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((O,),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();12]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((O,),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();13]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((O,),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();14]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((O,),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();15]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((O,),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();16]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((O,),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();17]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((O,),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();18]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((O,),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();19]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((((O,),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();20]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();21]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();22]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();23]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();24]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();25]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();26]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();27]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();28]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();29]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();30]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();31]> for B where A : Onion<Type=O>, B : Onion<Type=(((((((((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),)> {}
impl<A,B,O> LenExceeds<A, [();32]> for B where A : Onion<Type=O>, B : Onion<Type=((((((((((((((((((((((((((((((((O,),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),),)> {}

pub trait NonZeroLen<O> {}

impl<T,O> NonZeroLen<O> for T where T: LenExceeds<[();0],O> {}

pub trait LenEq {
    type Array;
}

impl<A,O,Array,Tuple> LenExceeds<A,[O;0]> for Tuple
    where Tuple : LenEq<Array=Array>
        , Array : LenExceeds<A,O>
{
}

macro_rules! impl_tuplex {
    ($($len:tt $htup:ident $htup_iter:ident => ($index0:tt $t0:ident $u0:ident ($($index:tt $t:ident $u:ident)*) $($last_index:tt $tn_1:ident $un_1:ident)*))*) => {$(
        impl_len!(                    $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_len_eq!(                 $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_push_front!(                   $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_push_back!(                    $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_pop_front!(                                    $($index $t)*    $($last_index $tn_1)*       );
        impl_pop_back!(                    ($index0 $t0     $($index $t)*)   $($last_index $tn_1)*       );
        impl_tuple_into_homo_tuple!(  $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_array_from_tuple!(       $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_tuple_into_array!(       $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_tuple_into_boxed_slice!( $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_tuple_into_vec!(         $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
        impl_bin_tuple!(                                           $($t)*                $($tn_1)*       );
        impl_tuple_of!(                             $t0            $($t)*                $($tn_1)*       );
        impl_convert_tuple!(                $index0 $t0 $u0 $($index $t $u)* $($last_index $tn_1 $un_1)* );
        impl_tuple_from_tuple!(             $index0 $t0 $u0 $($index $t $u)* $($last_index $tn_1 $un_1)* );
        impl_map_homo_tuple!(         $len, $index0         $($index   )*    $($last_index)*             );
        impl_homo!(  $htup $htup_iter $len, $index0         $($index)*       $($last_index)*             );
    )*};
}

impl_tuplex! {
     2 HTup2  HTupIter2  => (0 T0 U0()1 T1 U1)
     3 HTup3  HTupIter3  => (0 T0 U0 (1 T1 U1)2 T2 U2)
     4 HTup4  HTupIter4  => (0 T0 U0 (1 T1 U1 2 T2 U2)3 T3 U3)
     5 HTup5  HTupIter5  => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3)4 T4 U4)
     6 HTup6  HTupIter6  => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4)5 T5 U5)
     7 HTup7  HTupIter7  => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5)6 T6 U6)
     8 HTup8  HTupIter8  => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6)7 T7 U7)
     9 HTup9  HTupIter9  => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7)8 T8 U8)
    10 HTup10 HTupIter10 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8)9 T9 U9)
    11 HTup11 HTupIter11 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9)10 T10 U10)
    12 HTup12 HTupIter12 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10)11 T11 U11)
    13 HTup13 HTupIter13 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11)12 T12 U12)
    14 HTup14 HTupIter14 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12)13 T13 U13)
    15 HTup15 HTupIter15 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13)14 T14 U14)
    16 HTup16 HTupIter16 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14)15 T15 U15)
    17 HTup17 HTupIter17 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15)16 T16 U16)
    18 HTup18 HTupIter18 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16)17 T17 U17)
    19 HTup19 HTupIter19 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17)18 T18 U18)
    20 HTup20 HTupIter20 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18)19 T19 U19)
    21 HTup21 HTupIter21 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19)20 T20 U20)
    22 HTup22 HTupIter22 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20)21 T21 U21)
    23 HTup23 HTupIter23 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21)22 T22 U22)
    24 HTup24 HTupIter24 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22)23 T23 U23)
    25 HTup25 HTupIter25 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23)24 T24 U24)
    26 HTup26 HTupIter26 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23 24 T24 U24)25 T25 U25)
    27 HTup27 HTupIter27 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23 24 T24 U24 25 T25 U25)26 T26 U26)
    28 HTup28 HTupIter28 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23 24 T24 U24 25 T25 U25 26 T26 U26)27 T27 U27)
    29 HTup29 HTupIter29 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23 24 T24 U24 25 T25 U25 26 T26 U26 27 T27 U27)28 T28 U28)
    30 HTup30 HTupIter30 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23 24 T24 U24 25 T25 U25 26 T26 U26 27 T27 U27 28 T28 U28)29 T29 U29)
    31 HTup31 HTupIter31 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23 24 T24 U24 25 T25 U25 26 T26 U26 27 T27 U27 28 T28 U28 29 T29 U29)30 T30 U30)
    32 HTup32 HTupIter32 => (0 T0 U0 (1 T1 U1 2 T2 U2 3 T3 U3 4 T4 U4 5 T5 U5 6 T6 U6 7 T7 U7 8 T8 U8 9 T9 U9 10 T10 U10 11 T11 U11 12 T12 U12 13 T13 U13 14 T14 U14 15 T15 U15 16 T16 U16 17 T17 U17 18 T18 U18 19 T19 U19 20 T20 U20 21 T21 U21 22 T22 U22 23 T23 U23 24 T24 U24 25 T25 U25 26 T26 U26 27 T27 U27 28 T28 U28 29 T29 U29 30 T30 U30)31 T31 U31)
}

#[cfg( test )]
mod tests {
    use super::*;

    #[test]
    fn len_works() {
        assert_eq!( ()                 .len(), 0 );
        assert_eq!( ("0",)             .len(), 1 );
        assert_eq!( ("0",1)            .len(), 2 );
        assert_eq!( ("0",1,"2")        .len(), 3 );
        assert_eq!( ("0",1,"2",3)      .len(), 4 );
        assert_eq!( ("0",1,"2",3,"4")  .len(), 5 );
        assert_eq!( ("0",1,"2",3,"4",5).len(), 6 );
    }

    #[test]
    fn push_front_works() {
        assert_eq!( ()                 .push_front("0"), ("0",) );
        assert_eq!( (1,)               .push_front("0"), ("0",1) );
        assert_eq!( (1,"2")            .push_front("0"), ("0",1,"2") );
        assert_eq!( (1,"2",3)          .push_front("0"), ("0",1,"2",3) );
        assert_eq!( (1,"2",3,"4")      .push_front("0"), ("0",1,"2",3,"4") );
        assert_eq!( (1,"2",3,"4",5)    .push_front("0"), ("0",1,"2",3,"4",5) );
        assert_eq!( (1,"2",3,"4",5,"6").push_front("0"), ("0",1,"2",3,"4",5,"6") );
    }

    #[test]
    fn push_back_works() {
        assert_eq!( ()                 .push_back("0"), ("0",) );
        assert_eq!( ("0",)             .push_back(1)  , ("0",1) );
        assert_eq!( ("0",1,)           .push_back("2"), ("0",1,"2") );
        assert_eq!( ("0",1,"2")        .push_back(3)  , ("0",1,"2",3) );
        assert_eq!( ("0",1,"2",3)      .push_back("4"), ("0",1,"2",3,"4") );
        assert_eq!( ("0",1,"2",3,"4")  .push_back(5)  , ("0",1,"2",3,"4",5) );
        assert_eq!( ("0",1,"2",3,"4",5).push_back("6"), ("0",1,"2",3,"4",5,"6") );
    }

    #[test]
    fn pop_front_works() {
        assert_eq!( ("0",)             .pop_front(), ("0",()) );
        assert_eq!( ("0",1)            .pop_front(), ("0",(1,)) );
        assert_eq!( ("0",1,"2")        .pop_front(), ("0",(1,"2")) );
        assert_eq!( ("0",1,"2",3)      .pop_front(), ("0",(1,"2",3)) );
        assert_eq!( ("0",1,"2",3,"4")  .pop_front(), ("0",(1,"2",3,"4")) );
        assert_eq!( ("0",1,"2",3,"4",5).pop_front(), ("0",(1,"2",3,"4",5)) );
    }

    #[test]
    fn pop_back_works() {
        assert_eq!( ("0",)             .pop_back(), ("0",()) );
        assert_eq!( ("0",1)            .pop_back(), (1  ,("0",)) );
        assert_eq!( ("0",1,"2")        .pop_back(), ("2",("0",1)) );
        assert_eq!( ("0",1,"2",3)      .pop_back(), (3  ,("0",1,"2")) );
        assert_eq!( ("0",1,"2",3,"4")  .pop_back(), ("4",("0",1,"2",3)) );
        assert_eq!( ("0",1,"2",3,"4",5).pop_back(), (5  ,("0",1,"2",3,"4")) );
    }

    #[test]
    fn bin_tuple_works() {
        struct Test<T:BinTuple>( T, <T as BinTuple>::LeftAssociated, <T as BinTuple>::RightAssociated );
        Test( (),            (),                         ()                         );
        Test( (0,),          ((),0),                     (0,())                     );
        Test( (0,1),         (((),0),1),                 (0,(1,()))                 );
        Test( (0,1,2),       ((((),0),1),2),             (0,(1,(2,())))             );
        Test( (0,1,2,3),     (((((),0),1),2),3),         (0,(1,(2,(3,()))))         );
        Test( (0,1,2,3,4),   ((((((),0),1),2),3),4),     (0,(1,(2,(3,(4,())))))     );
        Test( (0,1,2,3,4,5), (((((((),0),1),2),3),4),5), (0,(1,(2,(3,(4,(5,())))))) );
    }

    #[derive( Debug, PartialEq, Eq )]
    struct I32( i32 );

    impl From<i32> for I32 { fn from( i: i32 ) -> I32 { I32(i) }}

    impl Convert for I32 {
        type Output = i32;
        fn convert( self ) -> i32 { self.0 }
    }

    impl Convert for i32 {
        type Output = i32;
        fn convert( self ) -> i32 { self }
    }

    struct Integer;

    impl ValueOf<Integer> for I32 {}
    impl ValueOf<Integer> for i32 {}

    #[test]
    fn tuple_from_tuple_works() {
        use crate::homo_tuple;
        assert_eq!( <homo_tuple!(I32;0)>::from_tuple( ()                           ), ()                                                 );
        assert_eq!( <homo_tuple!(I32;1)>::from_tuple( (I32(0),)                    ), ( I32(0),)                                         );
        assert_eq!( <homo_tuple!(I32;2)>::from_tuple( (I32(0),1)                   ), ( I32(0), I32(1), )                                );
        assert_eq!( <homo_tuple!(I32;3)>::from_tuple( (I32(0),1,I32(2))            ), ( I32(0), I32(1), I32(2), )                        );
        assert_eq!( <homo_tuple!(I32;4)>::from_tuple( (I32(0),1,I32(2),3)          ), ( I32(0), I32(1), I32(2), I32(3) )                 );
        assert_eq!( <homo_tuple!(I32;5)>::from_tuple( (I32(0),1,I32(2),3,I32(4))   ), ( I32(0), I32(1), I32(2), I32(3), I32(4) )         );
        assert_eq!( <homo_tuple!(I32;6)>::from_tuple( (I32(0),1,I32(2),3,I32(4),5) ), ( I32(0), I32(1), I32(2), I32(3), I32(4), I32(5) ) );
    }

    #[test]
    fn tuple_into_tuple_works() {
        use crate::{homo_tuple,IntoTuple};
        assert_eq!( IntoTuple::<homo_tuple!(I32;0)>::into_tuple( ()                           ), ()                                                 );
        assert_eq!( IntoTuple::<homo_tuple!(I32;1)>::into_tuple( (I32(0),)                    ), ( I32(0),)                                         );
        assert_eq!( IntoTuple::<homo_tuple!(I32;2)>::into_tuple( (I32(0),1)                   ), ( I32(0), I32(1), )                                );
        assert_eq!( IntoTuple::<homo_tuple!(I32;3)>::into_tuple( (I32(0),1,I32(2))            ), ( I32(0), I32(1), I32(2), )                        );
        assert_eq!( IntoTuple::<homo_tuple!(I32;4)>::into_tuple( (I32(0),1,I32(2),3)          ), ( I32(0), I32(1), I32(2), I32(3) )                 );
        assert_eq!( IntoTuple::<homo_tuple!(I32;5)>::into_tuple( (I32(0),1,I32(2),3,I32(4))   ), ( I32(0), I32(1), I32(2), I32(3), I32(4) )         );
        assert_eq!( IntoTuple::<homo_tuple!(I32;6)>::into_tuple( (I32(0),1,I32(2),3,I32(4),5) ), ( I32(0), I32(1), I32(2), I32(3), I32(4), I32(5) ) );
    }

    #[test]
    fn tuple_into_homo_tuple_works() {
        use crate::IntoHomoTuple;
        assert_eq!( IntoHomoTuple::<I32>::into_homo_tuple( ()                           ), ()                                                 );
        assert_eq!( IntoHomoTuple::<I32>::into_homo_tuple( (I32(0),)                    ), ( I32(0),)                                         );
        assert_eq!( IntoHomoTuple::<I32>::into_homo_tuple( (I32(0),1)                   ), ( I32(0), I32(1), )                                );
        assert_eq!( IntoHomoTuple::<I32>::into_homo_tuple( (I32(0),1,I32(2))            ), ( I32(0), I32(1), I32(2), )                        );
        assert_eq!( IntoHomoTuple::<I32>::into_homo_tuple( (I32(0),1,I32(2),3)          ), ( I32(0), I32(1), I32(2), I32(3) )                 );
        assert_eq!( IntoHomoTuple::<I32>::into_homo_tuple( (I32(0),1,I32(2),3,I32(4))   ), ( I32(0), I32(1), I32(2), I32(3), I32(4) )         );
        assert_eq!( IntoHomoTuple::<I32>::into_homo_tuple( (I32(0),1,I32(2),3,I32(4),5) ), ( I32(0), I32(1), I32(2), I32(3), I32(4), I32(5) ) );
    }

    #[test]
    fn array_from_tuple_works() {
        assert_eq!( <[I32;0]>::from_tuple( ()                           ), []                                                 );
        assert_eq!( <[I32;1]>::from_tuple( (I32(0),)                    ), [ I32(0) ]                                         );
        assert_eq!( <[I32;2]>::from_tuple( (I32(0),1)                   ), [ I32(0), I32(1), ]                                );
        assert_eq!( <[I32;3]>::from_tuple( (I32(0),1,I32(2))            ), [ I32(0), I32(1), I32(2), ]                        );
        assert_eq!( <[I32;4]>::from_tuple( (I32(0),1,I32(2),3)          ), [ I32(0), I32(1), I32(2), I32(3) ]                 );
        assert_eq!( <[I32;5]>::from_tuple( (I32(0),1,I32(2),3,I32(4))   ), [ I32(0), I32(1), I32(2), I32(3), I32(4) ]         );
        assert_eq!( <[I32;6]>::from_tuple( (I32(0),1,I32(2),3,I32(4),5) ), [ I32(0), I32(1), I32(2), I32(3), I32(4), I32(5) ] );
    }

    #[test]
    fn tuple_into_array_works() {
        assert_eq!( IntoArray::<I32>::into_array( ()                           ), []                                                 );
        assert_eq!( IntoArray::<I32>::into_array( (I32(0),)                    ), [ I32(0) ]                                         );
        assert_eq!( IntoArray::<I32>::into_array( (I32(0),1)                   ), [ I32(0), I32(1), ]                                );
        assert_eq!( IntoArray::<I32>::into_array( (I32(0),1,I32(2))            ), [ I32(0), I32(1), I32(2), ]                        );
        assert_eq!( IntoArray::<I32>::into_array( (I32(0),1,I32(2),3)          ), [ I32(0), I32(1), I32(2), I32(3) ]                 );
        assert_eq!( IntoArray::<I32>::into_array( (I32(0),1,I32(2),3,I32(4))   ), [ I32(0), I32(1), I32(2), I32(3), I32(4) ]         );
        assert_eq!( IntoArray::<I32>::into_array( (I32(0),1,I32(2),3,I32(4),5) ), [ I32(0), I32(1), I32(2), I32(3), I32(4), I32(5) ] );
    }

    #[test]
    fn tuple_into_boxed_slice_works() {
        assert_eq!( IntoBoxedSlice::<I32>::into_boxed_slice( () )                          , vec![                                                ].into_boxed_slice() );
        assert_eq!( IntoBoxedSlice::<I32>::into_boxed_slice( (I32(0), ))                   , vec![ I32(0)                                         ].into_boxed_slice() );
        assert_eq!( IntoBoxedSlice::<I32>::into_boxed_slice( (I32(0),1 ))                  , vec![ I32(0), I32(1),                                ].into_boxed_slice() );
        assert_eq!( IntoBoxedSlice::<I32>::into_boxed_slice( (I32(0),1,I32(2) ))           , vec![ I32(0), I32(1), I32(2),                        ].into_boxed_slice() );
        assert_eq!( IntoBoxedSlice::<I32>::into_boxed_slice( (I32(0),1,I32(2),3 ))         , vec![ I32(0), I32(1), I32(2), I32(3)                 ].into_boxed_slice() );
        assert_eq!( IntoBoxedSlice::<I32>::into_boxed_slice( (I32(0),1,I32(2),3,I32(4) ))  , vec![ I32(0), I32(1), I32(2), I32(3), I32(4)         ].into_boxed_slice() );
        assert_eq!( IntoBoxedSlice::<I32>::into_boxed_slice( (I32(0),1,I32(2),3,I32(4),5 )), vec![ I32(0), I32(1), I32(2), I32(3), I32(4), I32(5) ].into_boxed_slice() );
    }

    #[test]
    fn tuple_of_works() {
        struct Test<Tup:TupleOf<Integer>>( Tup );
        Test( (I32(0),)                          );
        Test( (I32(0), 1, )                      );
        Test( (I32(0), 1, I32(2), )              );
        Test( (I32(0), 1, I32(2), 3 )            );
        Test( (I32(0), 1, I32(2), 3, I32(4) )    );
        Test( (I32(0), 1, I32(2), 3, I32(4), 5 ) );
    }

    #[test]
    fn convert_tuple_works() {
        assert_eq!( ()                          .convert_tuple(), ()                   );
        assert_eq!( (I32(0),)                   .convert_tuple(), ( 0,)                );
        assert_eq!( (I32(0),1)                  .convert_tuple(), ( 0, 1, )            );
        assert_eq!( (I32(0),1,I32(2))           .convert_tuple(), ( 0, 1, 2, )         );
        assert_eq!( (I32(0),1,I32(2),3)         .convert_tuple(), ( 0, 1, 2, 3 )       );
        assert_eq!( (I32(0),1,I32(2),3,I32(4))  .convert_tuple(), ( 0, 1, 2, 3, 4 )    );
        assert_eq!( (I32(0),1,I32(2),3,I32(4),5).convert_tuple(), ( 0, 1, 2, 3, 4, 5 ) );
    }

    #[test]
    fn homo_into_iter_works() {
        let tuple = (1, 1, 2, 3, 5, 8, 13, 21);
        let iter = tuple.wrap_into_iter();
        assert_eq!( iter.collect::<Vec<_>>(), vec![ 1, 1, 2, 3, 5, 8, 13, 21 ]);
    }

    #[test]
    fn len_exceeds() {
        fn exceeds<More, Less, Tag>() where More: LenExceeds<Less,Tag> {}

        macro_rules! exceeds {
            ($($more:tt $less:tt,)*) => {$(
                exceeds::<[();$more], [();$less], _>();
            )*};
        }

        exceeds!{
            1 0, 2 0, 3 0, 4 0, 5 0, 6 0, 7 0, 8 0, 9 0, 10 0, 11  0, 12  0, 13  0, 14  0, 15  0, 16  0, 17  0, 18  0, 19  0, 20  0, 21  0, 22  0, 23  0, 24  0, 25  0, 26  0, 27  0, 28  0, 29  0, 30  0, 31  0, 32  0,
                 2 1, 3 1, 4 1, 5 1, 6 1, 7 1, 8 1, 9 1, 10 1, 11  1, 12  1, 13  1, 14  1, 15  1, 16  1, 17  1, 18  1, 19  1, 20  1, 21  1, 22  1, 23  1, 24  1, 25  1, 26  1, 27  1, 28  1, 29  1, 30  1, 31  1, 32  1,
                      3 2, 4 2, 5 2, 6 2, 7 2, 8 2, 9 2, 10 2, 11  2, 12  2, 13  2, 14  2, 15  2, 16  2, 17  2, 18  2, 19  2, 20  2, 21  2, 22  2, 23  2, 24  2, 25  2, 26  2, 27  2, 28  2, 29  2, 30  2, 31  2, 32  2,
                           4 3, 5 3, 6 3, 7 3, 8 3, 9 3, 10 3, 11  3, 13  3, 13  3, 14  3, 15  3, 16  3, 17  3, 18  3, 19  3, 20  3, 21  3, 22  3, 23  3, 24  3, 25  3, 26  3, 27  3, 28  3, 29  3, 30  3, 31  3, 32  3,
                                5 4, 6 4, 7 4, 8 4, 9 4, 10 4, 11  4, 13  4, 13  4, 14  4, 15  4, 16  4, 17  4, 18  4, 19  4, 20  4, 21  4, 22  4, 23  4, 24  4, 25  4, 26  4, 27  4, 28  4, 29  4, 30  4, 31  4, 32  4,
                                     6 5, 7 5, 8 5, 9 5, 10 5, 11  5, 13  5, 13  5, 14  5, 15  5, 16  5, 17  5, 18  5, 19  5, 20  5, 21  5, 22  5, 23  5, 24  5, 25  5, 26  5, 27  5, 28  5, 29  5, 30  5, 31  5, 32  5,
                                          7 6, 8 6, 9 6, 10 6, 11  6, 13  6, 13  6, 14  6, 15  6, 16  6, 17  6, 18  6, 19  6, 20  6, 21  6, 22  6, 23  6, 24  6, 25  6, 26  6, 27  6, 28  6, 29  6, 30  6, 31  6, 32  6,
                                               8 7, 9 7, 10 7, 11  7, 13  7, 13  7, 14  7, 15  7, 16  7, 17  7, 18  7, 19  7, 20  7, 21  7, 22  7, 23  7, 24  7, 25  7, 26  7, 27  7, 28  7, 29  7, 30  7, 31  7, 32  7,
                                                    9 8, 10 8, 11  8, 13  8, 13  8, 14  8, 15  8, 16  8, 17  8, 18  8, 19  8, 20  8, 21  8, 22  8, 23  8, 24  8, 25  8, 26  8, 27  8, 28  8, 29  8, 30  8, 31  8, 32  8,
                                                         10 9, 11  9, 13  9, 13  9, 14  9, 15  9, 16  9, 17  9, 18  9, 19  9, 20  9, 21  9, 22  9, 23  9, 24  9, 25  9, 26  9, 27  9, 28  9, 29  9, 30  9, 31  9, 32  9,
                                                               11 10, 13 10, 13 10, 14 10, 15 10, 16 10, 17 10, 18 10, 19 10, 20 10, 21 10, 22 10, 23 10, 24 10, 25 10, 26 10, 27 10, 28 10, 29 10, 30 10, 31 10, 32 10,
                                                                      13 11, 13 11, 14 11, 15 11, 16 11, 17 11, 18 11, 19 11, 20 11, 21 11, 22 11, 23 11, 24 11, 25 11, 26 11, 27 11, 28 11, 29 11, 30 11, 31 11, 32 11,
                                                                             13 12, 14 12, 15 12, 16 12, 17 12, 18 12, 19 12, 20 12, 21 12, 22 12, 23 12, 24 12, 25 12, 26 12, 27 12, 28 12, 29 12, 30 12, 31 12, 32 12,
                                                                                    14 13, 15 13, 16 13, 17 13, 18 13, 19 13, 20 13, 21 13, 22 13, 23 13, 24 13, 25 13, 26 13, 27 13, 28 13, 29 13, 30 13, 31 13, 32 13,
                                                                                           15 14, 16 14, 17 14, 18 14, 19 14, 20 14, 21 14, 22 14, 23 14, 24 14, 25 14, 26 14, 27 14, 28 14, 29 14, 30 14, 31 14, 32 14,
                                                                                                  16 15, 17 15, 18 15, 19 15, 20 15, 21 15, 22 15, 23 15, 24 15, 25 15, 26 15, 27 15, 28 15, 29 15, 30 15, 31 15, 32 15,
                                                                                                         17 16, 18 16, 19 16, 20 16, 21 16, 22 16, 23 16, 24 16, 25 16, 26 16, 27 16, 28 16, 29 16, 30 16, 31 16, 32 16,
                                                                                                                18 17, 19 17, 20 17, 21 17, 22 17, 23 17, 24 17, 25 17, 26 17, 27 17, 28 17, 29 17, 30 17, 31 17, 32 17,
                                                                                                                       19 18, 20 18, 21 18, 22 18, 23 18, 24 18, 25 18, 26 18, 27 18, 28 18, 29 18, 30 18, 31 18, 32 18,
                                                                                                                              20 19, 21 19, 22 19, 23 19, 24 19, 25 19, 26 19, 27 19, 28 19, 29 19, 30 19, 31 19, 32 19,
                                                                                                                                     21 20, 22 20, 23 20, 24 20, 25 20, 26 20, 27 20, 28 20, 29 20, 30 20, 31 20, 32 20,
                                                                                                                                            22 21, 23 21, 24 21, 25 21, 26 21, 27 21, 28 21, 29 21, 30 21, 31 21, 32 21,
                                                                                                                                                   23 22, 24 22, 25 22, 26 22, 27 22, 28 22, 29 22, 30 22, 31 22, 32 22,
                                                                                                                                                          24 23, 25 23, 26 23, 27 23, 28 23, 29 23, 30 23, 31 23, 32 23,
                                                                                                                                                                 25 24, 26 24, 27 24, 28 24, 29 24, 30 24, 31 24, 32 24,
                                                                                                                                                                        26 25, 27 25, 28 25, 29 25, 30 25, 31 25, 32 25,
                                                                                                                                                                               27 26, 28 26, 29 26, 30 26, 31 26, 32 26,
                                                                                                                                                                                      28 27, 29 27, 30 27, 31 27, 32 27,
                                                                                                                                                                                             29 28, 30 28, 31 28, 32 28,
                                                                                                                                                                                                    30 29, 31 29, 32 29,
                                                                                                                                                                                                           31 30, 32 30,
                                                                                                                                                                                                                  32 31,
        }
    }
}
