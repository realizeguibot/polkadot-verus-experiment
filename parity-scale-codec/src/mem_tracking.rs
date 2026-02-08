// Memory tracking for decoding — DecodeWithMemTracking and DecodeWithMemLimit.
// Adapted from parity-scale-codec 3.7.5.

use crate::{Decode, Input, Error};

/// Marker trait for types that call `Input::on_before_alloc_mem` while decoding.
pub trait DecodeWithMemTracking: Decode {}

// Implement for primitive types that are commonly used
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
impl DecodeWithMemTracking for bool {}
impl DecodeWithMemTracking for () {}

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
