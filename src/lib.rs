//! Treat Rust tuples as lists.
//!
//! # Features
//!
//! 1. adding/removing element at front/back
//!
//! 2. converting homogeneous tuples to heterogeneous ones
//!
//! # Examples, list operations
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
//! # Examples, homogeneous/heterogeneous conversions
//!
//! ```
//! use tuplex::*;
//!
//!
//! ```

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

pub trait HomoTuple<T>
    where Self: Len
              + IntoArray<T>
              + IntoBoxedSlice<T>
{
    type FieldsWrapped;
    type TupleWrapped: IntoIterator<Item=T>;
    fn wrap_fields( self ) -> Self::FieldsWrapped;
    fn wrap_tuple( self ) -> Self::TupleWrapped;
    fn wrap_into_iter( self ) -> <Self::TupleWrapped as IntoIterator>::IntoIter;
}

use std::marker::PhantomData;

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

pub trait IntoArray<T> {
    type Output: Len;
    fn into_array( self ) -> Self::Output;
}

macro_rules! impl_tuple_into_array {
    ($len:tt, $($index:tt $gen:ident)*) => {
        impl<T$(,$gen)*> IntoArray<T> for ($($gen,)*)
            where $(T: From<$gen>),*
        {
            type Output = [T; $len];

            fn into_array( self ) -> Self::Output {
                [ $( T::from( self.$index )),* ]
            }
        }
    };
}

impl_tuple_into_array!( 0,      );
impl_tuple_into_array!( 1, 0 T0 );

pub trait IntoBoxedSlice<T> {
    fn into_boxed_slice( self ) -> Box<[T]>;
}

macro_rules! impl_tuple_into_boxed_slice {
    ($len:tt, $($index:tt $gen:ident)*) => {
        impl<T$(,$gen)*> IntoBoxedSlice<T> for ($($gen,)*)
            where $(T: From<$gen>),*
        {
            fn into_boxed_slice( self ) -> Box<[T]> {
                Box::new( [ $( T::from( self.$index )),* ])
            }
        }
    };
}

impl_tuple_into_boxed_slice!( 0,      );
impl_tuple_into_boxed_slice!( 1, 0 T0 );

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

pub trait ValueOf<T> {}
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

pub trait Convert {
    type Output;
    fn convert( self ) -> Self::Output;
}

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

macro_rules! impl_tuplex {
    ($($len:tt $htup:ident $htup_iter:ident => ($index0:tt $t0:ident $u0:ident ($($index:tt $t:ident $u:ident)*) $($last_index:tt $tn_1:ident $un_1:ident)*))*) => {$(
        impl_len!(                    $len, $index0 $t0     $($index $t)*    $($last_index $tn_1)*       );
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
}
