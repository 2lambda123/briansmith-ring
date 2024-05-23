// Copyright (c) 2019, Google Inc.
// Portions Copyright 2024 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

use super::{Counter, KeyBytes, AES_KEY, BLOCK_LEN, MAX_ROUNDS};
use crate::{
    constant_time,
    polyfill::{self, usize_from_u32, ArraySplitMap as _},
};
use cfg_if::cfg_if;
use core::{array, ops::RangeFrom};

type Word = constant_time::Word;
const WORD_SIZE: usize = core::mem::size_of::<Word>();
const BATCH_SIZE: usize = WORD_SIZE / 2;
#[allow(clippy::cast_possible_truncation)]
const BATCH_SIZE_U32: u32 = BATCH_SIZE as u32;

const BLOCK_WORDS: usize = 16 / WORD_SIZE;

cfg_if! {
    if #[cfg(target_pointer_width = "64")] {
        const ROW0_MASK: Word = 0x000f000f000f000f;
        const ROW1_MASK: Word = 0x00f000f000f000f0;
        const ROW2_MASK: Word = 0x0f000f000f000f00;
        const ROW3_MASK: Word = 0xf000f000f000f000;
    } else if #[cfg(target_pointer_width = "32")] {
        const ROW0_MASK: Word = 0x03030303;
        const ROW1_MASK: Word = 0x0c0c0c0c;
        const ROW2_MASK: Word = 0x30303030;
        const ROW3_MASK: Word = 0xc0c0c0c0;
    }
}

#[inline(always)]
fn and(a: Word, b: Word) -> Word {
    a & b
}

#[inline(always)]
fn or(a: Word, b: Word) -> Word {
    a | b
}

#[inline(always)]
fn xor(a: Word, b: Word) -> Word {
    a ^ b
}

#[inline(always)]
fn not(a: Word) -> Word {
    !a
}

#[inline(always)]
fn shift_left<const I: u32>(a: Word) -> Word {
    a << (I * BATCH_SIZE_U32)
}

#[inline(always)]
fn shift_right<const I: u32>(a: Word) -> Word {
    a >> (I * BATCH_SIZE_U32)
}

// aes_nohw_delta_swap returns |a| with bits |a & mask| and
// |a & (mask << shift)| swapped. |mask| and |mask << shift| may not overlap.
#[inline(always)]
fn delta_swap<const MASK: Word, const SHIFT: u8>(a: Word) -> Word {
    // See
    // https://reflectionsonsecurity.wordpress.com/2014/05/11/efficient-bit-permutation-using-delta-swaps/
    let b = (a ^ (a >> SHIFT)) & MASK;
    a ^ b ^ (b << SHIFT)
}

// In the 32-bit and 64-bit implementations, a block spans multiple words.
// |aes_nohw_compact_block| must permute bits across different words. First we
// implement |aes_nohw_compact_word| which performs a smaller version of the
// transformation which stays within a single word.
//
// These transformations are generalizations of the output of
// http://programming.sirrida.de/calcperm.php on smaller inputs.
#[inline(always)]
fn compact_word(a: Word) -> Word {
    let a = Word::from_le(a);
    cfg_if! {
        if #[cfg(target_pointer_width = "64")] {
            // Numbering the 64/2 = 16 4-bit chunks, least to most significant, we swap
            // quartets of those chunks:
            //   0 1 2 3 | 4 5 6 7 | 8  9 10 11 | 12 13 14 15 =>
            //   0 2 1 3 | 4 6 5 7 | 8 10  9 11 | 12 14 13 15
            let a = delta_swap::<0x00f000f000f000f0, 4>(a);
            // Swap quartets of 8-bit chunks (still numbering by 4-bit chunks):
            //   0 2 1 3 | 4 6 5 7 | 8 10  9 11 | 12 14 13 15 =>
            //   0 2 4 6 | 1 3 5 7 | 8 10 12 14 |  9 11 13 15
            let a = delta_swap::<0x0000ff000000ff00, 8>(a);
            // Swap quartets of 16-bit chunks (still numbering by 4-bit chunks):
            //   0 2 4 6 | 1  3  5  7 | 8 10 12 14 | 9 11 13 15 =>
            //   0 2 4 6 | 8 10 12 14 | 1  3  5  7 | 9 11 13 15
            delta_swap::<0x00000000ffff0000, 16>(a)
        } else if #[cfg(target_pointer_width = "32")] {
            // Numbering the 32/2 = 16 pairs of bits, least to most significant, we swap:
            //   0 1 2 3 | 4 5 6 7 | 8  9 10 11 | 12 13 14 15 =>
            //   0 4 2 6 | 1 5 3 7 | 8 12 10 14 |  9 13 11 15
            // Note:  0x00cc = 0b0000_0000_1100_1100
            //   0x00cc << 6 = 0b0011_0011_0000_0000
            let a = delta_swap::<0x00cc00cc, 6>(a);
            // Now we swap groups of four bits (still numbering by pairs):
            //   0 4 2  6 | 1 5 3  7 | 8 12 10 14 | 9 13 11 15 =>
            //   0 4 8 12 | 1 5 9 13 | 2  6 10 14 | 3  7 11 15
            // Note: 0x0000_f0f0 << 12 = 0x0f0f_0000
            delta_swap::<0x0000f0f0, 12>(a)
        } else {
            unimplemented!()
        }
    }
}

#[inline(always)]
fn uncompact_word(a: Word) -> Word {
    #[cfg(target_pointer_width = "64")]
    let r = {
        // Reverse the steps of |aes_nohw_uncompact_word|.
        let a = delta_swap::<0x00000000ffff0000, 16>(a);
        let a = delta_swap::<0x0000ff000000ff00, 8>(a);
        delta_swap::<0x00f000f000f000f0, 4>(a)
    };

    #[cfg(target_pointer_width = "32")]
    let r = {
        let a = delta_swap::<0x0000f0f0, 12>(a);
        delta_swap::<0x00cc00cc, 6>(a)
    };

    Word::to_le(r)
}

fn compact_block(input: &[u8; 16]) -> [Word; BLOCK_WORDS] {
    let out: [Word; BLOCK_WORDS] = unsafe { core::mem::transmute(*input) };
    let a0 = compact_word(out[0]);
    let a1 = compact_word(out[1]);

    #[cfg(target_pointer_width = "64")]
    let r = [
        (a0 & 0x00000000ffffffff) | (a1 << 32),
        (a1 & 0xffffffff00000000) | (a0 >> 32),
    ];

    #[cfg(target_pointer_width = "32")]
    let r = {
        let a2 = compact_word(out[2]);
        let a3 = compact_word(out[3]);
        // Note clang, when building for ARM Thumb2, will sometimes miscompile
        // expressions such as (a0 & 0x0000ff00) << 8, particularly when building
        // without optimizations. This bug was introduced in
        // https://reviews.llvm.org/rL340261 and fixed in
        // https://reviews.llvm.org/rL351310. The following is written to avoid this.
        [
            Word::from_le_bytes([lo(a0), lo(a1), lo(a2), lo(a3)]),
            Word::from_le_bytes([lo(a0 >> 8), lo(a1 >> 8), lo(a2 >> 8), lo(a3 >> 8)]),
            Word::from_le_bytes([lo(a0 >> 16), lo(a1 >> 16), lo(a2 >> 16), lo(a3 >> 16)]),
            Word::from_le_bytes([lo(a0 >> 24), lo(a1 >> 24), lo(a2 >> 24), lo(a3 >> 24)]),
        ]
    };

    r
}

fn uncompact_block(out: &mut [u8; BLOCK_LEN], input: &[Word; BLOCK_WORDS]) {
    let a0 = input[0];
    let a1 = input[1];

    #[cfg(target_pointer_width = "64")]
    let [b0, b1] = {
        [
            (a0 & 0x00000000ffffffff) | (a1 << 32),
            (a1 & 0xffffffff00000000) | (a0 >> 32),
        ]
    };

    #[cfg(target_pointer_width = "32")]
    let [b0, b1, b2, b3] = {
        let a2 = input[2];
        let a3 = input[3];

        // Note clang, when building for ARM Thumb2, will sometimes miscompile
        // expressions such as (a0 & 0x0000ff00) << 8, particularly when building
        // without optimizations. This bug was introduced in
        // https://reviews.llvm.org/rL340261 and fixed in
        // https://reviews.llvm.org/rL351310. The following is written to avoid this.
        let b0 = Word::from_le_bytes([lo(a0), lo(a1), lo(a2), lo(a3)]);
        let b1 = Word::from_le_bytes([lo(a0 >> 8), lo(a1 >> 8), lo(a2 >> 8), lo(a3 >> 8)]);
        let b2 = Word::from_le_bytes([lo(a0 >> 16), lo(a1 >> 16), lo(a2 >> 16), lo(a3 >> 16)]);
        let b3 = Word::from_le_bytes([lo(a0 >> 24), lo(a1 >> 24), lo(a2 >> 24), lo(a3 >> 24)]);
        [b0, b1, b2, b3]
    };

    let b0 = uncompact_word(b0);
    let b1 = uncompact_word(b1);

    #[cfg(target_pointer_width = "32")]
    let (b2, b3) = (uncompact_word(b2), uncompact_word(b3));

    let (out, _) = polyfill::slice::as_chunks_mut(out);
    out[0] = Word::to_ne_bytes(b0);
    out[1] = Word::to_ne_bytes(b1);

    #[cfg(target_pointer_width = "32")]
    {
        out[2] = Word::to_ne_bytes(b2);
        out[3] = Word::to_ne_bytes(b3);
    }
}

#[cfg(target_pointer_width = "32")]
#[inline(always)]
fn lo(w: Word) -> u8 {
    w as u8
}

// aes_nohw_swap_bits is a variation on a delta swap. It swaps the bits in
// |*a & (mask << shift)| with the bits in |*b & mask|. |mask| and
// |mask << shift| must not overlap. |mask| is specified as a |uint32_t|, but it
// is repeated to the full width of |aes_word_t|.
fn swap_bits<const A: usize, const B: usize, const MASK_BYTE: u8, const SHIFT: u8>(
    w: &mut [Word; 8],
) {
    // TODO: const MASK: Word = ...
    let mask = Word::from_ne_bytes([MASK_BYTE; core::mem::size_of::<Word>()]);

    // This is a variation on a delta swap.
    let swap = ((w[A] >> SHIFT) ^ w[B]) & mask;
    w[A] ^= swap << SHIFT;
    w[B] ^= swap;
}

// An AES_NOHW_BATCH stores |AES_NOHW_BATCH_SIZE| blocks. Unless otherwise
// specified, it is in bitsliced form.
#[repr(C)]
struct Batch {
    w: [Word; 8],
}

impl Batch {
    // aes_nohw_to_batch initializes |out| with the |num_blocks| blocks from |in|.
    // |num_blocks| must be at most |AES_NOHW_BATCH|.
    fn from_bytes(input: &[[u8; BLOCK_LEN]]) -> Self {
        let mut r = Self {
            w: Default::default(),
        };
        input.iter().enumerate().for_each(|(i, input)| {
            let block = compact_block(input);
            r.set(&block, i);
        });
        r.transpose();
        r
    }

    // aes_nohw_batch_set sets the |i|th block of |batch| to |in|. |batch| is in
    // compact form.
    fn set(&mut self, input: &[Word; BLOCK_WORDS], i: usize) {
        assert!(i < self.w.len());

        // Note the words are interleaved. The order comes from |aes_nohw_transpose|.
        // If |i| is zero and this is the 64-bit implementation, in[0] contains bits
        // 0-3 and in[1] contains bits 4-7. We place in[0] at w[0] and in[1] at
        // w[4] so that bits 0 and 4 are in the correct position. (In general, bits
        // along diagonals of |AES_NOHW_BATCH_SIZE| by |AES_NOHW_BATCH_SIZE| squares
        // will be correctly placed.)
        cfg_if! {
            if #[cfg(target_pointer_width = "64")] {
                self.w[i] = input[0];
                self.w[i + 4] = input[1];
            } else if #[cfg(target_pointer_width = "32")] {
                self.w[i] = input[0];
                self.w[i + 2] = input[1];
                self.w[i + 4] = input[2];
                self.w[i + 6] = input[3];
            } else {
                todo!()
            }
        }
    }

    // aes_nohw_batch_get writes the |i|th block of |batch| to |out|. |batch| is in
    // compact form.
    fn get(&self, i: usize) -> [Word; BLOCK_WORDS] {
        assert!(i < self.w.len());
        array::from_fn(|j| {
            #[cfg(target_pointer_width = "64")]
            const STRIDE: usize = 4;
            #[cfg(target_pointer_width = "32")]
            const STRIDE: usize = 2;

            self.w[i + (j * STRIDE)]
        })
    }
}

// AES round steps.
impl Batch {
    fn sub_bytes(&mut self) {
        // See https://eprint.iacr.org/2009/191.pdf, Appendix C.
        let x0 = self.w[7];
        let x1 = self.w[6];
        let x2 = self.w[5];
        let x3 = self.w[4];
        let x4 = self.w[3];
        let x5 = self.w[2];
        let x6 = self.w[1];
        let x7 = self.w[0];

        // Figure 2, the top linear transformation.
        let y14 = xor(x3, x5);
        let y13 = xor(x0, x6);
        let y9 = xor(x0, x3);
        let y8 = xor(x0, x5);
        let t0 = xor(x1, x2);
        let y1 = xor(t0, x7);
        let y4 = xor(y1, x3);
        let y12 = xor(y13, y14);
        let y2 = xor(y1, x0);
        let y5 = xor(y1, x6);
        let y3 = xor(y5, y8);
        let t1 = xor(x4, y12);
        let y15 = xor(t1, x5);
        let y20 = xor(t1, x1);
        let y6 = xor(y15, x7);
        let y10 = xor(y15, t0);
        let y11 = xor(y20, y9);
        let y7 = xor(x7, y11);
        let y17 = xor(y10, y11);
        let y19 = xor(y10, y8);
        let y16 = xor(t0, y11);
        let y21 = xor(y13, y16);
        let y18 = xor(x0, y16);

        // Figure 3, the middle non-linear section.
        let t2 = and(y12, y15);
        let t3 = and(y3, y6);
        let t4 = xor(t3, t2);
        let t5 = and(y4, x7);
        let t6 = xor(t5, t2);
        let t7 = and(y13, y16);
        let t8 = and(y5, y1);
        let t9 = xor(t8, t7);
        let t10 = and(y2, y7);
        let t11 = xor(t10, t7);
        let t12 = and(y9, y11);
        let t13 = and(y14, y17);
        let t14 = xor(t13, t12);
        let t15 = and(y8, y10);
        let t16 = xor(t15, t12);
        let t17 = xor(t4, t14);
        let t18 = xor(t6, t16);
        let t19 = xor(t9, t14);
        let t20 = xor(t11, t16);
        let t21 = xor(t17, y20);
        let t22 = xor(t18, y19);
        let t23 = xor(t19, y21);
        let t24 = xor(t20, y18);
        let t25 = xor(t21, t22);
        let t26 = and(t21, t23);
        let t27 = xor(t24, t26);
        let t28 = and(t25, t27);
        let t29 = xor(t28, t22);
        let t30 = xor(t23, t24);
        let t31 = xor(t22, t26);
        let t32 = and(t31, t30);
        let t33 = xor(t32, t24);
        let t34 = xor(t23, t33);
        let t35 = xor(t27, t33);
        let t36 = and(t24, t35);
        let t37 = xor(t36, t34);
        let t38 = xor(t27, t36);
        let t39 = and(t29, t38);
        let t40 = xor(t25, t39);
        let t41 = xor(t40, t37);
        let t42 = xor(t29, t33);
        let t43 = xor(t29, t40);
        let t44 = xor(t33, t37);
        let t45 = xor(t42, t41);
        let z0 = and(t44, y15);
        let z1 = and(t37, y6);
        let z2 = and(t33, x7);
        let z3 = and(t43, y16);
        let z4 = and(t40, y1);
        let z5 = and(t29, y7);
        let z6 = and(t42, y11);
        let z7 = and(t45, y17);
        let z8 = and(t41, y10);
        let z9 = and(t44, y12);
        let z10 = and(t37, y3);
        let z11 = and(t33, y4);
        let z12 = and(t43, y13);
        let z13 = and(t40, y5);
        let z14 = and(t29, y2);
        let z15 = and(t42, y9);
        let z16 = and(t45, y14);
        let z17 = and(t41, y8);

        // Figure 4, bottom linear transformation.
        let t46 = xor(z15, z16);
        let t47 = xor(z10, z11);
        let t48 = xor(z5, z13);
        let t49 = xor(z9, z10);
        let t50 = xor(z2, z12);
        let t51 = xor(z2, z5);
        let t52 = xor(z7, z8);
        let t53 = xor(z0, z3);
        let t54 = xor(z6, z7);
        let t55 = xor(z16, z17);
        let t56 = xor(z12, t48);
        let t57 = xor(t50, t53);
        let t58 = xor(z4, t46);
        let t59 = xor(z3, t54);
        let t60 = xor(t46, t57);
        let t61 = xor(z14, t57);
        let t62 = xor(t52, t58);
        let t63 = xor(t49, t58);
        let t64 = xor(z4, t59);
        let t65 = xor(t61, t62);
        let t66 = xor(z1, t63);
        let s0 = xor(t59, t63);
        let s6 = xor(t56, not(t62));
        let s7 = xor(t48, not(t60));
        let t67 = xor(t64, t65);
        let s3 = xor(t53, t66);
        let s4 = xor(t51, t66);
        let s5 = xor(t47, t65);
        let s1 = xor(t64, not(s3));
        let s2 = xor(t55, not(t67));

        self.w[0] = s7;
        self.w[1] = s6;
        self.w[2] = s5;
        self.w[3] = s4;
        self.w[4] = s3;
        self.w[5] = s2;
        self.w[6] = s1;
        self.w[7] = s0;
    }

    fn add_round_key(&mut self, key: &Batch) {
        constant_time::xor_assign_at_start(&mut self.w, &key.w)
    }

    #[inline(always)]
    fn rotate_cols_right<const N_TIMES_4: u32, const BLOCK_LEN_MINUS_N_TIMES_4: u32>(
        v: Word,
    ) -> Word {
        or(
            shift_right::<N_TIMES_4>(v),
            shift_left::<BLOCK_LEN_MINUS_N_TIMES_4>(v),
        )
    }
}

// aes_nohw_rotate_cols_right returns |v| with the columns in each row rotated
// to the right by |n|. This is a macro because |aes_nohw_shift_*| require
// constant shift counts in the SSE2 implementation.
// TODO(MSRV feature(generic_const_exprs)): Replace this.
macro_rules! rotate_cols_right {
    ( Self::rotate_cols_right::<$N:literal>($v:expr) ) => {
        Self::rotate_cols_right::<{ $N * 4 }, { 16 - ($N * 4) }>($v)
    };
}

impl Batch {
    fn shift_rows(&mut self) {
        self.w.iter_mut().for_each(|w| {
            let row0 = and(*w, ROW0_MASK);
            let row1 = and(*w, ROW1_MASK);
            let row2 = and(*w, ROW2_MASK);
            let row3 = and(*w, ROW3_MASK);
            let row1 = rotate_cols_right!(Self::rotate_cols_right::<1>(row1));
            let row2 = rotate_cols_right!(Self::rotate_cols_right::<2>(row2));
            let row3 = rotate_cols_right!(Self::rotate_cols_right::<3>(row3));
            *w = or(or(row0, row1), or(row2, row3));
        });
    }

    fn mix_columns(&mut self) {
        // See https://eprint.iacr.org/2009/129.pdf, section 4.4 and appendix A.
        let a0 = self.w[0];
        let a1 = self.w[1];
        let a2 = self.w[2];
        let a3 = self.w[3];
        let a4 = self.w[4];
        let a5 = self.w[5];
        let a6 = self.w[6];
        let a7 = self.w[7];

        let r0 = rotate_rows_down(a0);
        let a0_r0 = xor(a0, r0);
        let r1 = rotate_rows_down(a1);
        let a1_r1 = xor(a1, r1);
        let r2 = rotate_rows_down(a2);
        let a2_r2 = xor(a2, r2);
        let r3 = rotate_rows_down(a3);
        let a3_r3 = xor(a3, r3);
        let r4 = rotate_rows_down(a4);
        let a4_r4 = xor(a4, r4);
        let r5 = rotate_rows_down(a5);
        let a5_r5 = xor(a5, r5);
        let r6 = rotate_rows_down(a6);
        let a6_r6 = xor(a6, r6);
        let r7 = rotate_rows_down(a7);
        let a7_r7 = xor(a7, r7);

        self.w[0] = xor(xor(a7_r7, r0), rotate_rows_twice(a0_r0));
        self.w[1] = xor(xor(a0_r0, a7_r7), xor(r1, rotate_rows_twice(a1_r1)));
        self.w[2] = xor(xor(a1_r1, r2), rotate_rows_twice(a2_r2));
        self.w[3] = xor(xor(a2_r2, a7_r7), xor(r3, rotate_rows_twice(a3_r3)));
        self.w[4] = xor(xor(a3_r3, a7_r7), xor(r4, rotate_rows_twice(a4_r4)));
        self.w[5] = xor(xor(a4_r4, r5), rotate_rows_twice(a5_r5));
        self.w[6] = xor(xor(a5_r5, r6), rotate_rows_twice(a6_r6));
        self.w[7] = xor(xor(a6_r6, r7), rotate_rows_twice(a7_r7));
    }

    // aes_nohw_from_batch writes the first |num_blocks| blocks in |batch| to |out|.
    // |num_blocks| must be at most |AES_NOHW_BATCH|.
    pub fn into_bytes(self, out: &mut [[u8; BLOCK_LEN]]) {
        assert!(out.len() <= BATCH_SIZE);

        // TODO: Why did the original code copy `self`?
        let mut copy = self;
        copy.transpose();
        out.iter_mut().enumerate().for_each(|(i, out)| {
            let block = copy.get(i);
            uncompact_block(out, &block);
        });
    }

    fn encrypt(mut self, key: &Schedule, rounds: usize, out: &mut [[u8; BLOCK_LEN]]) {
        assert!(out.len() <= BATCH_SIZE);
        self.add_round_key(&key.keys[0]);
        key.keys[1..rounds].iter().for_each(|key| {
            self.sub_bytes();
            self.shift_rows();
            self.mix_columns();
            self.add_round_key(key);
        });
        self.sub_bytes();
        self.shift_rows();
        self.add_round_key(&key.keys[rounds]);
        self.into_bytes(out);
    }

    // aes_nohw_transpose converts |batch| to and from bitsliced form. It divides
    // the 8 × word_size bits into AES_NOHW_BATCH_SIZE × AES_NOHW_BATCH_SIZE squares
    // and transposes each square.
    fn transpose(&mut self) {
        const _: () = assert!(BATCH_SIZE == 2 || BATCH_SIZE == 4);

        // Swap bits with index 0 and 1 mod 2 (0x55 = 0b01010101).
        swap_bits::<0, 1, 0x55, 1>(&mut self.w);
        swap_bits::<2, 3, 0x55, 1>(&mut self.w);
        swap_bits::<4, 5, 0x55, 1>(&mut self.w);
        swap_bits::<6, 7, 0x55, 1>(&mut self.w);

        if BATCH_SIZE >= 4 {
            // Swap bits with index 0-1 and 2-3 mod 4 (0x33 = 0b00110011).
            swap_bits::<0, 2, 0x33, 2>(&mut self.w);
            swap_bits::<1, 3, 0x33, 2>(&mut self.w);
            swap_bits::<4, 6, 0x33, 2>(&mut self.w);
            swap_bits::<5, 7, 0x33, 2>(&mut self.w);
        }
    }
}

#[inline(always)]
fn rotate_rows_down(v: Word) -> Word {
    #[cfg(target_pointer_width = "64")]
    {
        ((v >> 4) & 0x0fff0fff0fff0fff) | ((v << 12) & 0xf000f000f000f000)
    }

    #[cfg(target_pointer_width = "32")]
    {
        ((v >> 2) & 0x3f3f3f3f) | ((v << 6) & 0xc0c0c0c0)
    }
}

// rotate_rows_twice returns |v| with the rows in each column rotated
// by two.
#[inline(always)]
fn rotate_rows_twice(v: Word) -> Word {
    #[cfg(target_pointer_width = "64")]
    {
        ((v >> 8) & 0x00ff00ff00ff00ff) | ((v << 8) & 0xff00ff00ff00ff00)
    }

    #[cfg(target_pointer_width = "32")]
    {
        ((v >> 4) & 0x0f0f0f0f) | ((v << 4) & 0xf0f0f0f0)
    }
}

// Key schedule.

// An AES_NOHW_SCHEDULE is an expanded bitsliced AES key schedule. It is
// suitable for encryption or decryption. It is as large as |AES_NOHW_BATCH|
// |AES_KEY|s so it should not be used as a long-term key representation.
struct Schedule {
    // keys is an array of batches, one for each round key. Each batch stores
    // |AES_NOHW_BATCH_SIZE| copies of the round key in bitsliced form.
    keys: [Batch; MAX_ROUNDS + 1],
}

impl Schedule {
    fn expand_round_keys(key: &AES_KEY) -> Self {
        Self {
            keys: array::from_fn(|i| {
                let tmp: [Word; BLOCK_WORDS] = unsafe { core::mem::transmute(key.rd_key[i]) };

                let mut r = Batch { w: [0; 8] };
                // Copy the round key into each block in the batch.
                for j in 0..BATCH_SIZE {
                    r.set(&tmp, j);
                }
                r.transpose();
                r
            }),
        }
    }
}

static RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

// aes_nohw_rcon_slice returns the |i|th group of |AES_NOHW_BATCH_SIZE| bits in
// |rcon|, stored in a |aes_word_t|.
#[inline(always)]
fn rcon_slice(rcon: u8, i: usize) -> Word {
    let rcon = (rcon >> (i * BATCH_SIZE)) & ((1 << BATCH_SIZE) - 1);
    rcon.into()
}

pub(super) fn set_encrypt_key(key: &mut AES_KEY, bytes: KeyBytes) {
    match bytes {
        KeyBytes::AES_128(bytes) => setup_key_128(key, bytes),
        KeyBytes::AES_256(bytes) => setup_key_256(key, bytes),
    }
}

fn setup_key_128(key: &mut AES_KEY, input: &[u8; 128 / 8]) {
    key.rounds = 10;

    let mut block = compact_block(input);
    key.rd_key[0] = unsafe { core::mem::transmute(block) };

    key.rd_key[1..=10]
        .iter_mut()
        .zip(RCON)
        .for_each(|(rd_key, rcon)| {
            let sub = sub_block(&block);
            *rd_key = derive_round_key(&mut block, sub, rcon);
        });
}

pub(super) fn encrypt_block(key: &AES_KEY, in_out: &mut [u8; BLOCK_LEN]) {
    let sched = Schedule::expand_round_keys(key);
    let batch = Batch::from_bytes(core::slice::from_ref(in_out));
    batch.encrypt(&sched, usize_from_u32(key.rounds), array::from_mut(in_out));
}

fn setup_key_256(key: &mut AES_KEY, input: &[u8; 32]) {
    key.rounds = 14;

    // Each key schedule iteration produces two round keys.
    let (input, _) = polyfill::slice::as_chunks(input);
    let mut block1 = compact_block(&input[0]);
    key.rd_key[0] = unsafe { core::mem::transmute(block1) };
    let mut block2 = compact_block(&input[1]);
    key.rd_key[1] = unsafe { core::mem::transmute(block2) };

    key.rd_key[2..=14]
        .chunks_mut(2)
        .zip(RCON)
        .for_each(|(rd_key_pair, rcon)| {
            let sub = sub_block(&block2);
            rd_key_pair[0] = derive_round_key(&mut block1, sub, rcon);

            if let Some(rd_key_2) = rd_key_pair.get_mut(1) {
                let sub = sub_block(&block1);
                block2.iter_mut().zip(sub).for_each(|(w, sub)| {
                    // Incorporate the transformed word into the first word.
                    *w ^= shift_right::<12>(sub);
                    // Propagate to the remaining words.
                    let v = *w;
                    *w ^= shift_left::<4>(v);
                    *w ^= shift_left::<8>(v);
                    *w ^= shift_left::<12>(v);
                });
                *rd_key_2 = unsafe { core::mem::transmute(block2) };
            }
        });
}

fn derive_round_key(
    block: &mut [Word; BLOCK_WORDS],
    sub: [Word; BLOCK_WORDS],
    rcon: u8,
) -> [u32; 4] {
    block
        .iter_mut()
        .zip(sub)
        .enumerate()
        .for_each(|(j, (w, sub))| {
            // Incorporate |rcon| and the transformed word into the first word.
            *w ^= rcon_slice(rcon, j);
            *w ^= shift_right::<12>(rotate_rows_down(sub));
            // Propagate to the remaining words.
            let v = *w;
            *w ^= shift_left::<4>(v);
            *w ^= shift_left::<8>(v);
            *w ^= shift_left::<12>(v);
        });
    unsafe { core::mem::transmute(*block) }
}

fn sub_block(input: &[Word; BLOCK_WORDS]) -> [Word; BLOCK_WORDS] {
    let mut batch = Batch {
        w: Default::default(),
    };
    batch.set(input, 0);
    batch.transpose();
    batch.sub_bytes();
    batch.transpose();
    batch.get(0)
}

pub(super) fn ctr32_encrypt_within(
    key: &AES_KEY,
    mut in_out: &mut [u8],
    src: RangeFrom<usize>,
    ctr: &mut Counter,
) {
    let (input, leftover): (&[[u8; BLOCK_LEN]], _) =
        polyfill::slice::as_chunks(&in_out[src.clone()]);
    debug_assert_eq!(leftover.len(), 0);
    if input.is_empty() {
        return;
    }
    let blocks_u32 = u32::try_from(input.len()).unwrap();

    let sched = Schedule::expand_round_keys(key);

    let initial_ctr = ctr.as_bytes_less_safe();
    ctr.increment_by_less_safe(blocks_u32);

    let mut ivs = [initial_ctr; BATCH_SIZE];
    let mut enc_ctrs = [[0u8; 16]; BATCH_SIZE];
    let initial_ctr: [[u8; 4]; 4] = initial_ctr.array_split_map(|x| x);
    let mut ctr = u32::from_be_bytes(initial_ctr[3]);

    for _ in (0..).step_by(BATCH_SIZE) {
        (0u32..).zip(ivs.iter_mut()).for_each(|(i, iv)| {
            iv[12..].copy_from_slice(&u32::to_be_bytes(ctr + i));
        });

        let (input, leftover): (&[[u8; BLOCK_LEN]], _) =
            polyfill::slice::as_chunks(&in_out[src.clone()]);
        debug_assert_eq!(leftover.len(), 0);
        let todo = core::cmp::min(ivs.len(), input.len());
        let batch = Batch::from_bytes(&ivs[..todo]);
        batch.encrypt(&sched, usize_from_u32(key.rounds), &mut enc_ctrs[..todo]);
        constant_time::xor_within_chunked_at_start(in_out, src.clone(), &enc_ctrs[..todo]);

        if todo < BATCH_SIZE {
            break;
        }
        in_out = &mut in_out[(BLOCK_LEN * BATCH_SIZE)..];
        ctr += BATCH_SIZE_U32;
    }
}
