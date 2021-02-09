// Copyright 2016 Brian Smith.
// Portions Copyright (c) 2016, Google Inc.
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

use super::quic::Sample;
use crate::{aead::Nonce, c, polyfill::ChunksFixed};
use core::ops::RangeFrom;

#[repr(transparent)]
pub struct Key([u32; KEY_LEN / 4]);

impl From<[u8; KEY_LEN]> for Key {
    #[inline]
    fn from(value: [u8; KEY_LEN]) -> Self {
        let value = value.chunks_fixed();
        Self([
            u32::from_le_bytes(value[0]),
            u32::from_le_bytes(value[1]),
            u32::from_le_bytes(value[2]),
            u32::from_le_bytes(value[3]),
            u32::from_le_bytes(value[4]),
            u32::from_le_bytes(value[5]),
            u32::from_le_bytes(value[6]),
            u32::from_le_bytes(value[7]),
        ])
    }
}

impl Key {
    #[inline]
    pub fn encrypt_in_place(&self, counter: Counter, in_out: &mut [u8]) {
        self.encrypt_less_safe(counter, in_out, 0..);
    }

    #[inline]
    pub fn encrypt_iv_xor_in_place(&self, iv: Iv, in_out: &mut [u8; 32]) {
        // It is safe to use `into_counter_for_single_block_less_safe()`
        // because `in_out` is exactly one block long.
        debug_assert!(in_out.len() <= BLOCK_LEN);
        self.encrypt_less_safe(iv.into_counter_for_single_block_less_safe(), in_out, 0..);
    }

    #[inline]
    pub fn new_mask(&self, sample: Sample) -> [u8; 5] {
        let mut out: [u8; 5] = [0; 5];
        let iv = Iv::assume_unique_for_key(sample);

        debug_assert!(out.len() <= BLOCK_LEN);
        self.encrypt_less_safe(iv.into_counter_for_single_block_less_safe(), &mut out, 0..);

        out
    }

    /// Analogous to `slice::copy_within()`.
    pub fn encrypt_within(&self, counter: Counter, in_out: &mut [u8], src: RangeFrom<usize>) {
        // XXX: The x86 and at least one branch of the ARM assembly language
        // code doesn't allow overlapping input and output unless they are
        // exactly overlapping. TODO: Figure out which branch of the ARM code
        // has this limitation and come up with a better solution.
        //
        // https://rt.openssl.org/Ticket/Display.html?id=4362
        if cfg!(any(target_arch = "arm", target_arch = "x86")) && src.start != 0 {
            let len = in_out.len() - src.start;
            in_out.copy_within(src, 0);
            self.encrypt_in_place(counter, &mut in_out[..len]);
        } else {
            self.encrypt_less_safe(counter, in_out, src);
        }
    }

    /// This is "less safe" because it skips the important check that `encrypt_within` does.
    /// Only call this with `src` equal to `0..` or from `encrypt_within`.
    #[inline]
    fn encrypt_less_safe(&self, counter: Counter, in_out: &mut [u8], src: RangeFrom<usize>) {
        let in_out_len = in_out.len().checked_sub(src.start).unwrap();

        // There's no need to worry if `counter` is incremented because it is
        // owned here and we drop immediately after the call.
        extern "C" {
            fn GFp_ChaCha20_ctr32(
                out: *mut u8,
                in_: *const u8,
                in_len: c::size_t,
                key: &Key,
                counter: &Counter,
            );
        }
        unsafe {
            GFp_ChaCha20_ctr32(
                in_out.as_mut_ptr(),
                in_out[src].as_ptr(),
                in_out_len,
                self,
                &counter,
            );
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[inline]
    pub(super) fn words_less_safe(&self) -> &[u32; KEY_LEN / 4] {
        &self.0
    }
}

/// Counter || Nonce, all native endian.
#[repr(transparent)]
pub struct Counter([u32; 4]);

impl Counter {
    pub fn zero(nonce: Nonce) -> Self {
        Self::from_nonce_and_ctr(nonce, 0)
    }

    fn from_nonce_and_ctr(nonce: Nonce, ctr: u32) -> Self {
        let nonce = nonce.as_ref().chunks_fixed();
        Self([
            ctr,
            u32::from_le_bytes(nonce[0]),
            u32::from_le_bytes(nonce[1]),
            u32::from_le_bytes(nonce[2]),
        ])
    }

    pub fn increment(&mut self) -> Iv {
        let iv = Iv(self.0);
        self.0[0] += 1;
        iv
    }
}

/// The IV for a single block encryption.
///
/// Intentionally not `Clone` to ensure each is used only once.
pub struct Iv([u32; 4]);

impl Iv {
    fn assume_unique_for_key(value: [u8; 16]) -> Self {
        let value = value.chunks_fixed();
        Self([
            u32::from_le_bytes(value[0]),
            u32::from_le_bytes(value[1]),
            u32::from_le_bytes(value[2]),
            u32::from_le_bytes(value[3]),
        ])
    }

    fn into_counter_for_single_block_less_safe(self) -> Counter {
        Counter(self.0)
    }
}

pub const KEY_LEN: usize = 32;

const BLOCK_LEN: usize = 64;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{polyfill, test};
    use alloc::vec;
    use core::convert::TryInto;

    // Verifies the encryption is successful when done on overlapping buffers.
    //
    // On some branches of the 32-bit x86 and ARM assembly code the in-place
    // operation fails in some situations where the input/output buffers are
    // not exactly overlapping. Such failures are dependent not only on the
    // degree of overlapping but also the length of the data. `encrypt_within`
    // works around that.
    #[test]
    pub fn chacha20_tests() {
        // Reuse a buffer to avoid slowing down the tests with allocations.
        let mut buf = vec![0u8; 1300];

        test::run(test_file!("chacha_tests.txt"), move |section, test_case| {
            assert_eq!(section, "");

            let key = test_case.consume_bytes("Key");
            let key: &[u8; KEY_LEN] = key.as_slice().try_into()?;
            let key = Key::from(*key);

            let ctr = test_case.consume_usize("Ctr");
            let nonce = test_case.consume_bytes("Nonce");
            let input = test_case.consume_bytes("Input");
            let output = test_case.consume_bytes("Output");

            // Run the test case over all prefixes of the input because the
            // behavior of ChaCha20 implementation changes dependent on the
            // length of the input.
            for len in 0..=input.len() {
                chacha20_test_case_inner(
                    &key,
                    &nonce,
                    ctr as u32,
                    &input[..len],
                    &output[..len],
                    &mut buf,
                );
            }

            Ok(())
        });
    }

    fn chacha20_test_case_inner(
        key: &Key,
        nonce: &[u8],
        ctr: u32,
        input: &[u8],
        expected: &[u8],
        buf: &mut [u8],
    ) {
        const ARBITRARY: u8 = 123;

        for alignment in 0..16 {
            polyfill::slice::fill(&mut buf[..alignment], ARBITRARY);
            let buf = &mut buf[alignment..];
            for offset in 0..=259 {
                let buf = &mut buf[..(offset + input.len())];
                polyfill::slice::fill(&mut buf[..offset], ARBITRARY);
                let src = offset..;
                buf[src.clone()].copy_from_slice(input);

                let ctr = Counter::from_nonce_and_ctr(
                    Nonce::try_assume_unique_for_key(nonce).unwrap(),
                    ctr,
                );
                key.encrypt_within(ctr, buf, src);
                assert_eq!(&buf[..input.len()], expected)
            }
        }
    }
}