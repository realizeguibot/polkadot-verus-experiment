// Memory tracking for decoding — DecodeWithMemTracking and DecodeWithMemLimit.
// Adapted from parity-scale-codec 3.7.5.

use crate::{Decode, Input, Error, Compact, CompactAs};
use crate::alloc::boxed::Box;
use crate::alloc::vec::Vec;
use crate::alloc::string::String;
use crate::alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
use crate::alloc::borrow::Cow;
use crate::alloc::rc::Rc;
#[cfg(target_has_atomic = "ptr")]
use crate::alloc::sync::Arc;
use core::marker::PhantomData;
use core::num::*;
use core::ops::{Range, RangeInclusive};
use core::time::Duration;

/// Marker trait for types that call `Input::on_before_alloc_mem` while decoding.
pub trait DecodeWithMemTracking: Decode {}

// Primitive types
impl DecodeWithMemTracking for u8 {}
impl DecodeWithMemTracking for u16 {}
impl DecodeWithMemTracking for u32 {}
impl DecodeWithMemTracking for u64 {}
impl DecodeWithMemTracking for u128 {}
impl DecodeWithMemTracking for i8 {}
impl DecodeWithMemTracking for i16 {}
impl DecodeWithMemTracking for i32 {}
impl DecodeWithMemTracking for i64 {}
impl DecodeWithMemTracking for i128 {}
impl DecodeWithMemTracking for f32 {}
impl DecodeWithMemTracking for f64 {}
impl DecodeWithMemTracking for bool {}

// NonZero types
impl DecodeWithMemTracking for NonZeroI8 {}
impl DecodeWithMemTracking for NonZeroI16 {}
impl DecodeWithMemTracking for NonZeroI32 {}
impl DecodeWithMemTracking for NonZeroI64 {}
impl DecodeWithMemTracking for NonZeroI128 {}
impl DecodeWithMemTracking for NonZeroU8 {}
impl DecodeWithMemTracking for NonZeroU16 {}
impl DecodeWithMemTracking for NonZeroU32 {}
impl DecodeWithMemTracking for NonZeroU64 {}
impl DecodeWithMemTracking for NonZeroU128 {}

// Arrays
impl<T: DecodeWithMemTracking, const N: usize> DecodeWithMemTracking for [T; N] {}

// Smart pointers
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for Box<T> {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for Rc<T> {}
#[cfg(target_has_atomic = "ptr")]
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for Arc<T> {}

// Option / Result
impl DecodeWithMemTracking for crate::OptionBool {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for Option<T> {}
impl<T: DecodeWithMemTracking, E: DecodeWithMemTracking> DecodeWithMemTracking for Result<T, E> {}

// Collections
impl DecodeWithMemTracking for String {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for Vec<T> {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for VecDeque<T> {}
impl<K: DecodeWithMemTracking, V: DecodeWithMemTracking> DecodeWithMemTracking for BTreeMap<K, V> where BTreeMap<K, V>: Decode {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for BTreeSet<T> where BTreeSet<T>: Decode {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for LinkedList<T> where LinkedList<T>: Decode {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for BinaryHeap<T> where BinaryHeap<T>: Decode {}

// Cow
impl<'a, T: crate::alloc::borrow::ToOwned + ?Sized> DecodeWithMemTracking for Cow<'a, T>
where
	Cow<'a, T>: Decode,
	T::Owned: DecodeWithMemTracking,
{}

// Other std types
impl<T> DecodeWithMemTracking for PhantomData<T> where PhantomData<T>: Decode {}
impl DecodeWithMemTracking for Duration {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for Range<T> {}
impl<T: DecodeWithMemTracking> DecodeWithMemTracking for RangeInclusive<T> {}

// Compact types
impl DecodeWithMemTracking for Compact<()> {}
impl DecodeWithMemTracking for Compact<u8> {}
impl DecodeWithMemTracking for Compact<u16> {}
impl DecodeWithMemTracking for Compact<u32> {}
impl DecodeWithMemTracking for Compact<u64> {}
impl DecodeWithMemTracking for Compact<u128> {}
impl<T> DecodeWithMemTracking for Compact<T>
where
	T: CompactAs,
	Compact<T::As>: DecodeWithMemTracking,
{}

// Tuples (up to 18 elements)
#[impl_trait_for_tuples::impl_for_tuples(18)]
impl DecodeWithMemTracking for Tuple {}

// BitVec (feature-gated)
#[cfg(feature = "bit-vec")]
impl<O: bitvec::order::BitOrder, T: bitvec::store::BitStore + Decode> DecodeWithMemTracking for bitvec::vec::BitVec<T, O> {}
#[cfg(feature = "bit-vec")]
impl<O: bitvec::order::BitOrder, T: bitvec::store::BitStore + Decode> DecodeWithMemTracking for bitvec::boxed::BitBox<T, O> {}

// Bytes (feature-gated)
#[cfg(feature = "bytes")]
impl DecodeWithMemTracking for bytes::Bytes {}

const DECODE_OOM_MSG: &str = "Heap memory limit exceeded while decoding";

/// Input wrapper that enforces a memory limit during decoding.
pub struct MemTrackingInput<'a, I> {
	input: &'a mut I,
	used_mem: usize,
	mem_limit: usize,
}

impl<'a, I: Input> MemTrackingInput<'a, I> {
	/// Create a new instance of `MemTrackingInput`.
	pub fn new(input: &'a mut I, mem_limit: usize) -> Self {
		Self { input, used_mem: 0, mem_limit }
	}

	/// Get the `used_mem` field.
	pub fn used_mem(&self) -> usize {
		self.used_mem
	}
}

impl<I: Input> Input for MemTrackingInput<'_, I> {
	fn remaining_len(&mut self) -> Result<Option<usize>, Error> {
		self.input.remaining_len()
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), Error> {
		self.input.read(into)
	}

	fn read_byte(&mut self) -> Result<u8, Error> {
		self.input.read_byte()
	}

	fn descend_ref(&mut self) -> Result<(), Error> {
		self.input.descend_ref()
	}

	fn ascend_ref(&mut self) {
		self.input.ascend_ref()
	}

	fn on_before_alloc_mem(&mut self, size: usize) -> Result<(), Error> {
		self.input.on_before_alloc_mem(size)?;

		self.used_mem = self.used_mem.saturating_add(size);
		if self.used_mem >= self.mem_limit {
			return Err(DECODE_OOM_MSG.into());
		}

		Ok(())
	}
}

/// Extension trait for decoding with a maximum memory limit.
pub trait DecodeWithMemLimit: DecodeWithMemTracking {
	/// Decode `Self` with the given maximum memory limit.
	fn decode_with_mem_limit<I: Input>(input: &mut I, mem_limit: usize) -> Result<Self, Error>;
}

impl<T> DecodeWithMemLimit for T
where
	T: DecodeWithMemTracking,
{
	fn decode_with_mem_limit<I: Input>(input: &mut I, mem_limit: usize) -> Result<Self, Error> {
		let mut input = MemTrackingInput::new(input, mem_limit);
		T::decode(&mut input)
	}
}
