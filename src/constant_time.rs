// Copyright 2015-2016 Brian Smith.
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

//! Constant-time operations.

use crate::{c, error, polyfill};
use core::{cmp, ops::RangeFrom};

#[cfg(target_pointer_width = "64")]
pub(crate) type Word = u64;

#[cfg(target_pointer_width = "32")]
pub(crate) type Word = u32;

/// Returns `Ok(())` if `a == b` and `Err(error::Unspecified)` otherwise.
/// The comparison of `a` and `b` is done in constant time with respect to the
/// contents of each, but NOT in constant time with respect to the lengths of
/// `a` and `b`.
pub fn verify_slices_are_equal(a: &[u8], b: &[u8]) -> Result<(), error::Unspecified> {
    if a.len() != b.len() {
        return Err(error::Unspecified);
    }
    let result = unsafe { CRYPTO_memcmp(a.as_ptr(), b.as_ptr(), a.len()) };
    match result {
        0 => Ok(()),
        _ => Err(error::Unspecified),
    }
}

prefixed_extern! {
    fn CRYPTO_memcmp(a: *const u8, b: *const u8, len: c::size_t) -> c::int;
}

pub(crate) fn xor<const N: usize>(mut a: [u8; N], b: [u8; N]) -> [u8; N] {
    // `xor_assign_at_start()`, but avoiding relying on the compiler to
    // optimize the slice iterators.
    a.iter_mut().zip(b.iter()).for_each(|(a, b)| *a ^= *b);
    a
}

/// XORs the first N bytes of `b` into `a`, where N is
/// `core::cmp::min(a.len(), b.len())`.
#[inline(always)]
pub(crate) fn xor_assign_at_start_bytes<'a>(
    a: impl IntoIterator<Item = &'a mut u8>,
    b: impl IntoIterator<Item = &'a u8>,
) {
    a.into_iter().zip(b).for_each(|(a, b)| *a ^= *b);
}

/// XORs the first N words of `b` into `a`, where N is
/// `core::cmp::min(a.len(), b.len())`.
#[inline(always)]
pub(crate) fn xor_assign_at_start<'a>(
    a: impl IntoIterator<Item = &'a mut Word>,
    b: impl IntoIterator<Item = &'a Word>,
) {
    a.into_iter().zip(b).for_each(|(a, b)| *a ^= *b);
}
#[inline(always)]
pub(crate) fn xor_within_chunked_at_start<const INNER: usize>(
    in_out: &mut [u8],
    src: RangeFrom<usize>,
    b: &[[u8; INNER]],
) {
    let (mut input, num_blocks) = {
        let input = match in_out.get(src.clone()) {
            Some(input) => input,
            None => {
                panic!()
            }
        };

        let (input, _): (&[[u8; INNER]], _) = polyfill::slice::as_chunks(input);
        let num_blocks = cmp::min(input.len(), b.len());
        (input.as_ptr(), num_blocks)
    };
    let (output, _): (&mut [[u8; INNER]], _) = polyfill::slice::as_chunks_mut(in_out);
    let output = &mut output[..num_blocks];

    for (b, out) in (b[..num_blocks].iter()).zip(output) {
        let a = unsafe { core::ptr::read(input) };
        out.iter_mut()
            .zip(a.iter().zip(b))
            .for_each(|(out, (a, b))| {
                *out = *a ^ *b;
            });
        input = unsafe { input.add(1) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limb::LimbMask;
    use crate::{bssl, error, rand};

    #[test]
    fn test_constant_time() -> Result<(), error::Unspecified> {
        prefixed_extern! {
            fn bssl_constant_time_test_main() -> bssl::Result;
        }
        Result::from(unsafe { bssl_constant_time_test_main() })
    }

    #[test]
    fn constant_time_conditional_memcpy() -> Result<(), error::Unspecified> {
        let rng = rand::SystemRandom::new();
        for _ in 0..100 {
            let mut out = rand::generate::<[u8; 256]>(&rng)?.expose();
            let input = rand::generate::<[u8; 256]>(&rng)?.expose();

            // Mask to 16 bits to make zero more likely than it would otherwise be.
            let b = (rand::generate::<[u8; 1]>(&rng)?.expose()[0] & 0x0f) == 0;

            let ref_in = input;
            let ref_out = if b { input } else { out };

            prefixed_extern! {
                fn bssl_constant_time_test_conditional_memcpy(dst: &mut [u8; 256], src: &[u8; 256], b: LimbMask);
            }
            unsafe {
                bssl_constant_time_test_conditional_memcpy(
                    &mut out,
                    &input,
                    if b { LimbMask::True } else { LimbMask::False },
                )
            }
            assert_eq!(ref_in, input);
            assert_eq!(ref_out, out);
        }

        Ok(())
    }

    #[test]
    fn constant_time_conditional_memxor() -> Result<(), error::Unspecified> {
        let rng = rand::SystemRandom::new();
        for _ in 0..256 {
            let mut out = rand::generate::<[u8; 256]>(&rng)?.expose();
            let input = rand::generate::<[u8; 256]>(&rng)?.expose();

            // Mask to 16 bits to make zero more likely than it would otherwise be.
            let b = (rand::generate::<[u8; 1]>(&rng)?.expose()[0] & 0x0f) != 0;

            let ref_in = input;
            let ref_out = if b { xor(out, ref_in) } else { out };

            prefixed_extern! {
                fn bssl_constant_time_test_conditional_memxor(dst: &mut [u8; 256], src: &[u8; 256], b: LimbMask);
            }
            unsafe {
                bssl_constant_time_test_conditional_memxor(
                    &mut out,
                    &input,
                    if b { LimbMask::True } else { LimbMask::False },
                );
            }

            assert_eq!(ref_in, input);
            assert_eq!(ref_out, out);
        }

        Ok(())
    }
}
