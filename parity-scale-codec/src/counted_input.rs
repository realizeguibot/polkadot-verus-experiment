// CountedInput — wraps an Input and counts bytes successfully read.
// Adapted from parity-scale-codec 3.7.5 (simplified to avoid closures for Verus compat).

use crate::{Input, Error};

/// Wrapper around `Input` that counts the number of bytes successfully read.
pub struct CountedInput<'a, I: Input> {
	input: &'a mut I,
	counter: u64,
}

impl<'a, I: Input> CountedInput<'a, I> {
	/// Create a new `CountedInput` with the given input.
	pub fn new(input: &'a mut I) -> Self {
		Self { input, counter: 0 }
	}

	/// Get the number of bytes successfully read.
	pub fn count(&self) -> u64 {
		self.counter
	}
}

impl<I: Input> Input for CountedInput<'_, I> {
	fn remaining_len(&mut self) -> Result<Option<usize>, Error> {
		self.input.remaining_len()
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), Error> {
		let result = self.input.read(into);
		if result.is_ok() {
			self.counter = self.counter.saturating_add(
				into.len().try_into().unwrap_or(u64::MAX)
			);
		}
		result
	}

	fn read_byte(&mut self) -> Result<u8, Error> {
		let result = self.input.read_byte();
		if result.is_ok() {
			self.counter = self.counter.saturating_add(1);
		}
		result
	}

	fn ascend_ref(&mut self) {
		self.input.ascend_ref()
	}

	fn descend_ref(&mut self) -> Result<(), Error> {
		self.input.descend_ref()
	}

	fn on_before_alloc_mem(&mut self, size: usize) -> Result<(), Error> {
		self.input.on_before_alloc_mem(size)
	}
}
