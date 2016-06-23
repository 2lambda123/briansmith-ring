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

use core;
use untrusted;

/// Field elements. Field elements are always Montgomery-encoded and always
/// fully reduced mod q; i.e. their range is [0, q).
pub struct Elem {
    limbs: [Limb; MAX_LIMBS],
}

impl Elem {
    #[inline(always)]
    pub unsafe fn limbs_as_ptr<'a>(&self) -> *const Limb {
        self.limbs.as_ptr()
    }
}


// XXX: Not correct for x32 ABIs.
#[cfg(target_pointer_width = "64")] pub type Limb = u64;
#[cfg(target_pointer_width = "32")] pub type Limb = u32;
#[cfg(target_pointer_width = "64")] const LIMB_BITS: usize = 64;
#[cfg(target_pointer_width = "32")] const LIMB_BITS: usize = 32;

#[cfg(all(target_pointer_width = "32", target_endian = "little"))]
macro_rules! limbs {
    ( $limb_b:expr, $limb_a:expr, $limb_9:expr, $limb_8:expr,
      $limb_7:expr, $limb_6:expr, $limb_5:expr, $limb_4:expr,
      $limb_3:expr, $limb_2:expr, $limb_1:expr, $limb_0:expr ) => {
        [$limb_0, $limb_1, $limb_2, $limb_3,
         $limb_4, $limb_5, $limb_6, $limb_7,
         $limb_8, $limb_9, $limb_a, $limb_b]
    }
}

#[cfg(all(target_pointer_width = "64", target_endian = "little"))]
macro_rules! limbs {
    ( $limb_b:expr, $limb_a:expr, $limb_9:expr, $limb_8:expr,
      $limb_7:expr, $limb_6:expr, $limb_5:expr, $limb_4:expr,
      $limb_3:expr, $limb_2:expr, $limb_1:expr, $limb_0:expr ) => {
        [(($limb_1 | 0u64) << 32) | $limb_0,
         (($limb_3 | 0u64) << 32) | $limb_2,
         (($limb_5 | 0u64) << 32) | $limb_4,
         (($limb_7 | 0u64) << 32) | $limb_6,
         (($limb_9 | 0u64) << 32) | $limb_8,
         (($limb_b | 0u64) << 32) | $limb_a]
    }
}

const LIMB_BYTES: usize = (LIMB_BITS + 7) / 8;
const MAX_LIMBS: usize = (384 + (LIMB_BITS - 1)) / LIMB_BITS;


/// Operations and values needed by all curve operations.
pub struct CommonOps {
    num_limbs: usize,
    q: Mont,

    // In all cases, `r`, `a`, and `b` may all alias each other.
    elem_mul_mont: unsafe extern fn(r: *mut Limb, a: *const Limb,
                                    b: *const Limb),
    elem_sqr_mont: unsafe extern fn(r: *mut Limb, a: *const Limb),

    pub ec_group: &'static EC_GROUP,
}

impl CommonOps {
    #[inline]
    pub fn elem_mul(&self, a: &Elem, b: &Elem) -> Elem {
        Elem { limbs: rab(self.elem_mul_mont, &a.limbs, &b.limbs) }
    }

    #[inline]
    pub fn elem_sqr(&self, a: &Elem) -> Elem {
        Elem { limbs: ra(self.elem_sqr_mont, &a.limbs) }
    }
}

struct Mont {
    p: [Limb; MAX_LIMBS],
    rr: [Limb; MAX_LIMBS],
}

#[allow(non_camel_case_types)]
pub enum EC_GROUP { }


/// Operations and values needed by all operations on public keys (ECDH
/// agreement and ECDSA verification).
pub struct PublicKeyOps {
    pub common: &'static CommonOps,

    pub a: Elem, // Must be -3 mod q
    pub b: Elem,

    // `r`, `a`, and `b` may all alias each other.
    elem_add_impl: unsafe extern fn(r: *mut Limb, a: *const Limb,
                                    b: *const Limb),
}

impl PublicKeyOps {
    // The serialized bytes are in big-endian order, zero-padded. The limbs
    // of `Elem` are in the native endianness, least significant limb to
    // most significant limb.
    pub fn elem_parse(&self, input: &mut untrusted::Reader)
                      -> Result<Elem, ()> {
        let num_limbs = self.common.num_limbs;

        let mut elem = Elem { limbs: [0; MAX_LIMBS] };
        for i in 0..num_limbs {
            let mut limb: Limb = 0;
            for _ in 0..LIMB_BYTES {
                limb = (limb << 8) | (try!(input.read_byte()) as Limb);
            }
            elem.limbs[num_limbs - 1 - i] = limb;
        }

        let q = &self.common.q;

        // Verify that the value is in the range [0, q).
        for i in 0..num_limbs {
            match elem.limbs[num_limbs - 1 - i].cmp(&q.p[num_limbs - 1 - i]) {
                core::cmp::Ordering::Less => {
                    // Montgomery encode (elem_to_mont).
                    ab_assign(self.common.elem_mul_mont, &mut elem.limbs,
                              &q.rr);
                    return Ok(elem);
                },
                core::cmp::Ordering::Equal => { }, // keep going
                core::cmp::Ordering::Greater => { break; }
            }
        }
        return Err(());
    }

    #[inline]
    pub fn elem_add(&self, a: &mut Elem, b: &Elem) {
        ab_assign(self.elem_add_impl, &mut a.limbs, &b.limbs)
    }

    pub fn elems_are_equal(&self, a: &Elem, b: &Elem) -> bool {
        for i in 0..self.common.num_limbs {
            if a.limbs[i] != b.limbs[i] {
                return false;
            }
        }
        return true;
    }
}


// let r = f(a, b); return r;
#[inline]
fn rab(f: unsafe extern fn(r: *mut Limb, a: *const Limb, b: *const Limb),
       a: &[Limb; MAX_LIMBS], b: &[Limb; MAX_LIMBS]) -> [Limb; MAX_LIMBS] {
    let mut r = [0; MAX_LIMBS];
    unsafe {
        f(r.as_mut_ptr(), a.as_ptr(), b.as_ptr())
    }
    r
}

// a = f(a, b);
#[inline]
fn ab_assign(f: unsafe extern fn(r: *mut Limb, a: *const Limb, b: *const Limb),
             a: &mut [Limb; MAX_LIMBS], b: &[Limb; MAX_LIMBS]) {
    unsafe {
        f(a.as_mut_ptr(), a.as_ptr(), b.as_ptr())
    }
}

// let r = f(a); return r;
#[inline]
fn ra(f: unsafe extern fn(r: *mut Limb, a: *const Limb),
      a: &[Limb; MAX_LIMBS]) -> [Limb; MAX_LIMBS] {
    let mut r = [0; MAX_LIMBS];
    unsafe {
        f(r.as_mut_ptr(), a.as_ptr())
    }
    r
}

pub mod p256;
pub mod p384;
