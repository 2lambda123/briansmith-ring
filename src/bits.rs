// Copyright 2016 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

use error;

#[derive(Clone, Copy, Eq, PartialEq)]
pub struct BitLength {
    bits: usize,
}

// Lengths measured in bits, where all arithmetic is guaranteed not to
// overflow.
impl BitLength {
    #[inline]
    pub fn from_usize_bits(bits: usize) -> BitLength {
        BitLength { bits: bits }
    }

    #[inline]
    pub fn from_usize_bytes(bytes: usize)
                            -> Result<BitLength, error::Unspecified> {
        let bits = try!(bytes.checked_mul(8).ok_or(error::Unspecified));
        Ok(BitLength::from_usize_bits(bits))
    }

    #[inline]
    pub fn as_usize_bits(&self) -> usize { self.bits }

    #[inline]
    pub fn as_usize_bytes_rounded_up(&self) -> usize {
        // Equivalent to (self.bits + 7) / 8, except with no potential for
        // overflow and without branches.

        // Branchless round_up = if self.bits & 0b111 != 0 { 1 } else { 0 };
        let round_up = ((self.bits >> 2) | (self.bits >> 1) | self.bits) & 1;

        (self.bits / 8) + round_up
    }

    #[inline]
    pub fn try_sub(self, other: BitLength)
                   -> Result<BitLength, error::Unspecified> {
        let sum =
            try!(self.bits.checked_sub(other.bits).ok_or(error::Unspecified));
        Ok(BitLength { bits: sum })
    }
}

pub const ONE: BitLength = BitLength { bits: 1 };
