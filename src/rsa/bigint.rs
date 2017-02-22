// Copyright 2015-2016 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

//! Multi-precision integers.
//!
//! # Modular Arithmetic.
//!
//! Modular arithmetic is done in finite commutative rings ℤ/mℤ for some
//! modulus *m*. We work in finite commutative rings instead of finite fields
//! because the RSA public modulus *n* is not prime, which means ℤ/nℤ contains
//! nonzero elements that have no multiplicative inverse, so ℤ/nℤ is not a
//! finite field.
//!
//! In some calculations we need to deal with multiple rings at once. For
//! example, RSA private key operations operate in the rings ℤ/nℤ, ℤ/pℤ, and
//! ℤ/qℤ. Types and functions dealing with such rings are all parameterized
//! over a type `M` to ensure that we don't wrongly mix up the math, e.g. by
//! multiplying an element of ℤ/pℤ by an element of ℤ/qℤ modulo q. This follows
//! the "unit" pattern described in [Static checking of units in Servo]; `Elem`,
//! and `Modulus` are analogous to `geom::Length`, and `super::N` and
//! `super::signing::{P, QQ, Q}` are analogous to `Mm` and `Inch`.
//!
//! `Elem` also uses the static unit checking pattern to statically track the
//! Montgomery factors that need to be canceled out in each value using it's
//! `E` parameter.
//!
//! [Static checking of units in Servo]:
//!     https://blog.mozilla.org/research/2014/06/23/static-checking-of-units-in-servo/

// There are two quantities relevant to this code, `r` and `R`, that have
// different values. We avoid using `r` to refer to `R` so we have to disable
// this lint.
#![allow(non_snake_case)]

// XXX TODO: Remove this once RSA verification has been done in Rust.
#![cfg_attr(not(feature = "rsa_signing"), allow(dead_code))]

use {bits, bssl, c, der, error, limb, rand, untrusted};
use core;
use core::marker::PhantomData;

/// This is defined for comparing values instead of using `PartialOrd` because
/// there `PartialOrd` requires `PartialEq`, which we do not otherwise require.
/// Also, this `Result<>`-based interface is more convenient for callers' uses.
pub fn verify_less_than<A: core::convert::AsRef<BIGNUM>,
                        B: core::convert::AsRef<BIGNUM>>(a: &A, b: &B)
        -> Result<(), error::Unspecified> {
    let r = unsafe { GFp_BN_ucmp(a.as_ref(), b.as_ref()) };
    if !(r < 0) {
        return Err(error::Unspecified);
    }
    Ok(())
}

impl AsRef<BIGNUM> for OddPositive {
    fn as_ref<'a>(&'a self) -> &'a BIGNUM { self.0.as_ref() }
}

impl AsRef<BIGNUM> for Positive {
    fn as_ref<'a>(&'a self) -> &'a BIGNUM { self.0.as_ref() }
}

impl AsRef<BIGNUM> for Nonnegative {
    fn as_ref<'a>(&'a self) -> &'a BIGNUM { &self.0 }
}


/// Non-negative, non-zero integers.
///
/// This set is sometimes called `Natural` or `Counting`, but texts, libraries,
/// and standards disagree on whether to include zero in them, so we avoid
/// those names.
pub struct Positive(Nonnegative);

impl Positive {
    // Parses a single ASN.1 DER-encoded `Integer`, which most be positive.
    pub fn from_der(input: &mut untrusted::Reader)
                    -> Result<Positive, error::Unspecified> {
        Self::from_be_bytes(try!(der::positive_integer(input)))
    }

    // Turns a sequence of big-endian bytes into a Positive Integer.
    pub fn from_be_bytes(input: untrusted::Input)
                         -> Result<Positive, error::Unspecified> {
        // Reject leading zeros. Also reject the value zero ([0]) because zero
        // isn't positive.
        if untrusted::Reader::new(input).peek(0) {
            return Err(error::Unspecified);
        }
        Self::from_be_bytes_padded(input)
    }

    pub fn from_be_bytes_padded(input: untrusted::Input)
                                -> Result<Positive, error::Unspecified> {
        // Reject empty inputs.
        if input.is_empty() {
            return Err(error::Unspecified);
        }
        let mut r = try!(Nonnegative::zero());
        try!(bssl::map_result(unsafe {
            GFp_BN_bin2bn(input.as_slice_less_safe().as_ptr(), input.len(),
                          r.as_mut_ref())
        }));
        if r.is_zero() {
            return Err(error::Unspecified);
        }
        Ok(Positive(r))
    }

    pub fn into_elem<M>(self, m: &Modulus<M>)
                        -> Result<Elem<M, Unencoded>, error::Unspecified> {
        self.0.into_elem(m)
    }

    pub fn into_odd_positive(self) -> Result<OddPositive, error::Unspecified> {
        self.0.into_odd_positive()
    }

    #[inline]
    pub fn bit_length(&self) -> bits::BitLength { self.0.bit_length() }
}

/// Odd positive integers.
pub struct OddPositive(Positive);

impl OddPositive {
    pub fn try_clone(&self) -> Result<OddPositive, error::Unspecified> {
        let value = try!((self.0).0.try_clone());
        Ok(OddPositive(Positive(value)))
    }

    pub fn into_elem<M>(self, m: &Modulus<M>)
                        -> Result<Elem<M, Unencoded>, error::Unspecified> {
        self.0.into_elem(m)
    }

    #[inline]
    pub fn into_modulus<M>(self) -> Result<Modulus<M>, error::Unspecified> {
        Modulus::new(self)
    }

    pub fn into_public_exponent(self)
                                -> Result<PublicExponent, error::Unspecified> {
        let bits = self.bit_length();
        if bits < bits::BitLength::from_usize_bits(2) {
            return Err(error::Unspecified);
        }
        if bits > PUBLIC_EXPONENT_MAX_BITS {
            return Err(error::Unspecified);
        }
        let value = unsafe { GFp_BN_get_positive_u64(self.as_ref()) };
        if value == 0 {
            return Err(error::Unspecified);
        }
        Ok(PublicExponent(value))
    }
}

impl core::ops::Deref for OddPositive {
    type Target = Positive;
    fn deref(&self) -> &Self::Target { &self.0 }
}


/// A modulus *s* that is smaller than another modulus *l* so every element of
/// ℤ/sℤ is also an element of ℤ/lℤ.
pub unsafe trait SmallerModulus<L> {}

/// A modulus *s* where s < l < 2*s for the given larger modulus *l*. This is
/// the precondition for reduction by conditional subtraction,
/// `elem_reduce_once()`.
pub unsafe trait SlightlySmallerModulus<L>: SmallerModulus<L> {}

/// A modulus *s* where √l <= s < l for the given larger modulus *l*. This is
/// the precondition for the more general Montgomery reduction from ℤ/lℤ to
/// ℤ/sℤ.
pub unsafe trait NotMuchSmallerModulus<L>: SmallerModulus<L> {}


/// The modulus *m* for a ring ℤ/mℤ, along with the precomputed values needed
/// for efficient Montgomery multiplication modulo *m*. The value must be odd
/// and larger than 2. The larger-than-1 requirement is imposed, at least, by
/// the modular inversion code.
pub struct Modulus<M> {
    value: OddPositive, // Also `value >= 3`.

    // n0 * N == -1 (mod r).
    //
    // TODO(perf): Not all 32-bit platforms actually make use of n0[1]. For the
    // ones that don't, we could use a shorter `R` value and use faster `Limb`
    // calculations instead of double-precision `u64` calculations.
    n0: N0,

    m: PhantomData<M>,
}

// `Modulus` uniquely owns and references its contents.
unsafe impl<M> Send for Modulus<M> {}

// `Modulus` is immutable.
unsafe impl<M> Sync for Modulus<M> {}

#[allow(trivial_numeric_casts)] // XXX
impl<M> Modulus<M> {
    fn new(value: OddPositive) -> Result<Self, error::Unspecified> {
        // A `Modulus` must be larger than 1.
        if value.bit_length() < bits::BitLength::from_usize_bits(2) {
            return Err(error::Unspecified);
        }
        let n0 = unsafe { GFp_bn_mont_n0(value.as_ref()) };
        Ok(Modulus {
            value: value,
            n0: n0_from_u64(n0),
            m: PhantomData,
        })
    }

    // RR = R**2 (mod N). R is the smallest power of 2**LIMB_BITS such that
    // R > mod. Even though the assembly on some 32-bit platforms works with
    // 64-bit values, using `LIMB_BITS` here, rather than
    // `N0_LIMBS_USED * LIMB_BITS`, is correct because R**2 will still be a
    // multiple of the latter as `N0_LIMBS_USED` is either one or two.
    pub fn compute_oneRR(&self) -> Result<Elem<M, RR>, error::Unspecified> {
        use limb::LIMB_BITS;
        let lg_R =
            (self.value.bit_length().as_usize_bits() + (LIMB_BITS - 1))
                / LIMB_BITS * LIMB_BITS;

        let mut RR = try!(Elem::zero());
        try!(bssl::map_result(unsafe {
            GFp_bn_mod_exp_base_2_vartime(RR.value.as_mut_ref(), lg_R,
                                          self.value.as_ref(), &self.n0)
        }));
        Ok(RR)
    }
}

// Not Montgomery encoded; there is no *R* factor that need to be canceled out.
pub enum Unencoded {}

// Montgomery encoded; the value has one *R* factor that needs to be canceled
// out.
pub enum R {}

// Montgomery encoded twice; the value has two *R* factors that need to be
// canceled out.
pub enum RR {}


// Montgomery encoded three times; the value has three *R* factors that need to
// be canceled out.
pub enum RRR {}

// Inversely Montgomery encoded; the value has one 1/*R* factor that needs to
// be canceled out.
pub enum RInverse {}

pub trait MontgomeryEncodingProduct {
    type Output;
}

// The result of Montgomery multiplication of a Montgomery-encoded element by
// an unencoded element is unencoded.
impl MontgomeryEncodingProduct for (Unencoded, R) {
    type Output = Unencoded;
}
impl MontgomeryEncodingProduct for (R, Unencoded) {
    type Output = Unencoded;
}

// The result of Montgomery multiplication of two Montgomery-encoded elements
// is Montgomery-encoded.
impl MontgomeryEncodingProduct for (R, R) {
    type Output = R;
}

impl MontgomeryEncodingProduct for (RR, Unencoded) {
    type Output = R;
}
impl MontgomeryEncodingProduct for (Unencoded, RR) {
    type Output = R;
}

impl MontgomeryEncodingProduct for (RInverse, RR) {
    type Output = Unencoded;
}
impl MontgomeryEncodingProduct for (RR, RInverse) {
    type Output = Unencoded;
}

impl MontgomeryEncodingProduct for (RR, RR) {
    type Output = RRR;
}

impl MontgomeryEncodingProduct for (RRR, RInverse) {
    type Output = R;
}
impl MontgomeryEncodingProduct for (RInverse, RRR) {
    type Output = R;
}


/// Montgomery-encoded elements of a field.
//
// Defaulting `E` to `Unencoded` is a convenience for callers from outside this
// submodule. However, for maximum clarity, we always explicitly use
// `Unencoded` within the `bigint` submodule.
pub struct Elem<M, E = Unencoded> {
    value: Nonnegative,

    /// The modulus m for the ring ℤ/mℤ for which this element is a value.
    m: PhantomData<M>,

    /// The number of Montgomery factors that need to be canceled out from
    /// `value` to get the actual value.
    encoding: PhantomData<E>,
}

impl<M, E> Elem<M, E> {
    // There's no need to convert `value` to the Montgomery domain since
    // 0 * R**2 (mod n) == 0, so the modulus isn't even needed to construct a
    // zero-valued element.
    pub fn zero() -> Result<Self, error::Unspecified> {
        let value = try!(Nonnegative::zero());
        Ok(Elem {
            value: value,
            m: PhantomData,
            encoding: PhantomData,
        })
    }

    pub fn is_zero(&self) -> bool { self.value.is_zero() }

    pub fn take_storage<OtherF>(e: Elem<M, OtherF>) -> Elem<M, E> {
        Elem {
            value: e.value,
            m: PhantomData,
            encoding: PhantomData,
        }
    }

    pub fn try_clone(&self) -> Result<Self, error::Unspecified> {
        let value = try!(self.value.try_clone());
        Ok(Elem {
            value: value,
            m: PhantomData,
            encoding: PhantomData,
        })
    }
}

impl<M> Elem<M, R> {
    pub fn into_unencoded(self, m: &Modulus<M>)
                          -> Result<Elem<M, Unencoded>, error::Unspecified> {
        let mut r = self.value;
        try!(bssl::map_result(unsafe {
            GFp_BN_from_mont(&mut r.0, &r.0, &m.value.as_ref(), &m.n0)
        }));
        Ok(Elem {
            value: r,
            m: PhantomData,
            encoding: PhantomData,
        })
    }
}

impl<M> Elem<M, Unencoded> {
    pub fn one() -> Result<Self, error::Unspecified> {
        let mut r = try!(Elem::zero());
        try!(bssl::map_result(unsafe {
            GFp_BN_one(r.value.as_mut_ref())
        }));
        Ok(r)
    }

    pub fn fill_be_bytes(&self, out: &mut [u8])
                         -> Result<(), error::Unspecified> {
        bssl::map_result(unsafe {
            GFp_BN_bn2bin_padded(out.as_mut_ptr(), out.len(),
                                 self.value.as_ref())
        })
    }

    pub fn is_one(&self) -> bool { self.value.is_one() }

    pub fn into_odd_positive(self) -> Result<OddPositive, error::Unspecified> {
        self.value.into_odd_positive()
    }
}


pub fn elem_mul<M, AF, BF>(a: &Elem<M, AF>, b: Elem<M, BF>, m: &Modulus<M>)
        -> Result<Elem<M, <(AF, BF) as MontgomeryEncodingProduct>::Output>,
                  error::Unspecified>
        where (AF, BF): MontgomeryEncodingProduct {
    let mut r = b.value;
    try!(bssl::map_result(unsafe {
        GFp_BN_mod_mul_mont(&mut r.0, a.value.as_ref(), &r.0, &m.value.as_ref(),
                            &m.n0)
    }));
    Ok(Elem {
        value: r,
        m: PhantomData,
        encoding: PhantomData,
    })
}

// `a` * `b` (mod `m`).
pub fn elem_set_to_product<M, AF, BF>(
        r: &mut Elem<M, <(AF, BF) as MontgomeryEncodingProduct>::Output>,
        a: &Elem<M, AF>, b: &Elem<M, BF>, m: &Modulus<M>)
        -> Result<(), error::Unspecified>
        where (AF, BF): MontgomeryEncodingProduct {
    bssl::map_result(unsafe {
        GFp_BN_mod_mul_mont(r.value.as_mut_ref(), a.value.as_ref(),
                            b.value.as_ref(), &m.value.as_ref(), &m.n0)
    })
}

pub fn elem_reduced_once<Larger, Smaller: SlightlySmallerModulus<Larger>>(
        a: &Elem<Larger, Unencoded>, m: &Modulus<Smaller>)
        -> Result<Elem<Smaller, Unencoded>, error::Unspecified> {
    let mut r = try!(Elem::zero());
    try!(bssl::map_result(unsafe {
        GFp_BN_mod_sub_quick(r.value.as_mut_ref(), a.value.as_ref(),
                             m.value.as_ref(), m.value.as_ref())
    }));
    Ok(r)
}

pub fn elem_reduced<Larger, Smaller: NotMuchSmallerModulus<Larger>>(
        a: &Elem<Larger, Unencoded>, m: &Modulus<Smaller>)
        -> Result<Elem<Smaller, RInverse>, error::Unspecified> {
    let mut tmp = try!(a.try_clone());
    let mut r = try!(Elem::<Smaller, RInverse>::zero());
    try!(bssl::map_result(unsafe {
        GFp_BN_from_montgomery_word(r.value.as_mut_ref(),
                                    tmp.value.as_mut_ref(), &m.value.as_ref(),
                                    &m.n0)
    }));
    Ok(r)
}

pub fn elem_squared<M, E>(a: Elem<M, E>, m: &Modulus<M>)
        -> Result<Elem<M, <(E, E) as MontgomeryEncodingProduct>::Output>,
                  error::Unspecified>
        where (E, E): MontgomeryEncodingProduct {
    let mut value = a.value;
    try!(bssl::map_result(unsafe {
        GFp_BN_mod_mul_mont(value.as_mut_ref(), value.as_ref(), value.as_ref(),
                            &m.value.as_ref(), &m.n0)
    }));
    Ok(Elem {
        value: value,
        m: PhantomData,
        encoding: PhantomData,
    })
}

pub fn elem_widen<Larger, Smaller: SmallerModulus<Larger>>(
        a: Elem<Smaller, Unencoded>) -> Elem<Larger, Unencoded> {
    Elem {
        value: a.value,
        m: PhantomData,
        encoding: PhantomData,
    }
}


// TODO: Document why this works for all Montgomery factors.
pub fn elem_add<M, E>(a: &Elem<M, E>, b: Elem<M, E>, m: &Modulus<M>)
                      -> Result<Elem<M, E>, error::Unspecified> {
    let mut value = b.value;
    try!(bssl::map_result(unsafe {
        GFp_BN_mod_add_quick(&mut value.0, a.value.as_ref(), value.as_ref(),
                             m.value.as_ref())
    }));
    Ok(Elem {
        value: value,
        m: PhantomData,
        encoding: PhantomData,
    })
}

// TODO: Document why this works for all Montgomery factors.
pub fn elem_sub<M, E>(a: Elem<M, E>, b: &Elem<M, E>, m: &Modulus<M>)
                   -> Result<Elem<M, E>, error::Unspecified> {
    let mut value = a.value;
    try!(bssl::map_result(unsafe {
        GFp_BN_mod_sub_quick(&mut value.0, &value.0, b.value.as_ref(),
                             m.value.as_ref())
    }));
    Ok(Elem {
        value: value,
        m: PhantomData,
        encoding: PhantomData,
    })
}


/// An non-secret odd positive value in the range
/// [3, 2**PUBLIC_EXPONENT_MAX_BITS).
#[derive(Clone, Copy)]
pub struct PublicExponent(u64);

// This limit was chosen to bound the performance of the simple
// exponentiation-by-squaring implementation in `elem_exp_vartime`. In
// particular, it helps mitigate theoretical resource exhaustion attacks. 33
// bits was chosen as the limit based on the recommendations in [1] and
// [2]. Windows CryptoAPI (at least older versions) doesn't support values
// larger than 32 bits [3], so it is unlikely that exponents larger than 32
// bits are being used for anything Windows commonly does.
//
// [1] https://www.imperialviolet.org/2012/03/16/rsae.html
// [2] https://www.imperialviolet.org/2012/03/17/rsados.html
// [3] https://msdn.microsoft.com/en-us/library/aa387685(VS.85).aspx
pub const PUBLIC_EXPONENT_MAX_BITS: bits::BitLength = bits::BitLength(33);

/// Calculates base**exponent (mod m).
// TODO: The test coverage needs to be expanded, e.g. test with the largest
// accepted exponent and with the most common values of 65537 and 3.
pub fn elem_exp_vartime<M>(
        base: Elem<M, R>, PublicExponent(exponent): PublicExponent,
        m: &Modulus<M>) -> Result<Elem<M, R>, error::Unspecified> {
    // Use what [Knuth] calls the "S-and-X binary method", i.e. variable-time
    // square-and-multiply that scans the exponent from the most significant
    // bit to the least significant bit (left-to-right). Left-to-right requires
    // less storage compared to right-to-left scanning, at the cost of needing
    // to compute `exponent.leading_zeros()`, which we assume to be cheap.
    //
    // The vast majority of the time the exponent is either 65537
    // (0b10000000000000001) or 3 (0b11), both of which have a Hamming weight
    // of 2. As explained in [Knuth], exponentiation by squaring is the most
    // efficient algorithm the hamming weight is 2 or less. It isn't the most
    // efficient for all other, uncommon, RSA public exponent values weight,
    // but any suboptimality is tightly bounded by the
    // `PUBLIC_EXPONENT_MAX_BITS` cap.
    //
    // This implementation is slightly simplified by taking advantage of the
    // fact that we require the exponent to be an (odd) positive integer.
    //
    // [Knuth]: The Art of Computer Programming, Volume 2: Seminumerical
    //          Algorithms (3rd Edition), Section 4.6.3.
    debug_assert_eq!(exponent & 1, 1);
    assert!(exponent < (1 << PUBLIC_EXPONENT_MAX_BITS.as_usize_bits()));
    let mut acc = try!(base.try_clone());
    let mut bit = 1 << (64 - 1 - exponent.leading_zeros());
    debug_assert!((exponent & bit) != 0);
    while bit > 1 {
        bit >>= 1;
        acc = try!(elem_squared(acc, m));
        if (exponent & bit) != 0 {
            acc = try!(elem_mul(&base, acc, m));
        }
    }
    Ok(acc)
}

pub fn elem_exp_consttime<M>(
        base: Elem<M, R>, exponent: &OddPositive, one: &Elem<M, R>,
        m: &Modulus<M>) -> Result<Elem<M, Unencoded>, error::Unspecified> {
    let mut r = base.value;
    try!(bssl::map_result(unsafe {
        GFp_BN_mod_exp_mont_consttime(&mut r.0, &r.0, exponent.as_ref(),
                                      one.value.as_ref(), &m.value.as_ref(),
                                      &m.n0)
    }));
    Ok(Elem {
        value: r,
        m: PhantomData,
        encoding: PhantomData,
    })
}

pub fn elem_randomize<M, E>(a: &mut Elem<M, E>, m: &Modulus<M>,
                            rng: &rand::SecureRandom)
                            -> Result<(), error::Unspecified> {
    a.value.randomize(m.value.as_ref(), rng)
}

// r = 1/a (mod m), blinded with a random element.
//
// This relies on the invariants of `Modulus` that its value is odd and larger
// than one.
pub fn elem_set_to_inverse_blinded<M>(
            r: &mut Elem<M, Unencoded>, a: &Elem<M, Unencoded>, m: &Modulus<M>,
            rng: &rand::SecureRandom) -> Result<(), InversionError> {
    let mut blinding_factor = try!(Elem::<M, R>::zero());
    try!(blinding_factor.value.randomize(m.value.as_ref(), rng));
    let to_blind = try!(a.try_clone());
    let blinded = try!(elem_mul(&blinding_factor, to_blind, m));
    let blinded_inverse = try!(elem_inverse(blinded, m));
    try!(elem_set_to_product(r, &blinding_factor, &blinded_inverse, m));
    Ok(())
}

// r = 1/a (mod m).
//
// This relies on the invariants of `Modulus` that its value is odd and larger
// than one.
fn elem_inverse<M>(a: Elem<M, Unencoded>, m: &Modulus<M>)
                   -> Result<Elem<M, Unencoded>, InversionError> {
    let mut value = a.value;
    let mut no_inverse = 0;
    try!(bssl::map_result(unsafe {
        GFp_BN_mod_inverse_odd(value.as_mut_ref(), &mut no_inverse,
                               value.as_ref(), m.value.as_ref())
    }).map_err(|_| {
        if no_inverse != 0 {
            InversionError::NoInverse
        } else {
            InversionError::Unspecified
        }
    }));
    Ok(Elem {
        value: value,
        m: PhantomData,
        encoding: PhantomData,
    })
}

pub enum InversionError {
    NoInverse,
    Unspecified
}

impl From<error::Unspecified> for InversionError {
    fn from(_: error::Unspecified) -> Self { InversionError::Unspecified }
}

pub fn elem_verify_equal_consttime<M>(a: &Elem<M, Unencoded>,
                                      b: &Elem<M, Unencoded>)
                                      -> Result<(), error::Unspecified> {
    bssl::map_result(unsafe {
        GFp_BN_equal_consttime(a.value.as_ref(), b.value.as_ref())
    })
}

/// Nonnegative integers: `Positive` ∪ {0}.
struct Nonnegative(BIGNUM);

// `Nonnegative` uniquely owns and references its contents.
unsafe impl Send for Nonnegative {}

impl Nonnegative {
    fn zero() -> Result<Self, error::Unspecified> {
        let r = Nonnegative(BIGNUM::zero());
        debug_assert!(r.is_zero());
        Ok(r)
    }

    fn bit_length(&self) -> bits::BitLength {
        let bits = unsafe { GFp_BN_num_bits(self.as_ref()) };
        bits::BitLength::from_usize_bits(bits)
    }

    fn is_zero(&self) -> bool {
        let is_zero = unsafe { GFp_BN_is_zero(self.as_ref()) };
        is_zero != 0
    }

    fn is_one(&self) -> bool {
        let is_one = unsafe { GFp_BN_is_one(self.as_ref()) };
        is_one != 0
    }

    fn randomize(&mut self, m: &BIGNUM, rng: &rand::SecureRandom)
                 -> Result<(), error::Unspecified> {
        let mut rand = rand::RAND::new(rng);
        bssl::map_result(unsafe {
            GFp_BN_rand_range_ex(self.as_mut_ref(), m, &mut rand)
        })
    }

    // XXX: This makes it too easy to break invariants on things. TODO: Remove
    // this ASAP.
    unsafe fn as_mut_ref(&mut self) -> &mut BIGNUM { &mut self.0 }

    fn into_elem<M>(self, m: &Modulus<M>)
                    -> Result<Elem<M, Unencoded>, error::Unspecified> {
        try!(verify_less_than(&self, &m.value));
        Ok(Elem {
            value: self,
            m: PhantomData,
            encoding: PhantomData,
        })
    }

    fn into_odd_positive(self) -> Result<OddPositive, error::Unspecified> {
        let is_odd = unsafe { GFp_BN_is_odd(self.as_ref()) };
        if is_odd == 0 {
            return Err(error::Unspecified);
        }
        Ok(OddPositive(Positive(self)))
    }

    pub fn try_clone(&self) -> Result<Nonnegative, error::Unspecified> {
        let mut r = try!(Nonnegative::zero());
        try!(bssl::map_result(unsafe {
            GFp_BN_copy(r.as_mut_ref(), self.as_ref())
        }));
        Ok(r)
    }
}

type N0 = [limb::Limb; N0_LIMBS];
const N0_LIMBS: usize = 2;

// const N0_LIMBS_USED: usize = 1;
#[cfg(target_pointer_width = "64")]
#[inline]
fn n0_from_u64(n0: u64) -> N0 {
    [n0, 0]
}

// const N0_LIMBS_USED: usize = 2;
#[cfg(target_pointer_width = "32")]
#[inline]
fn n0_from_u64(n0: u64) -> N0 {
    [n0 as limb::Limb, (n0 >> limb::LIMB_BITS) as limb::Limb]
}

// `BIGNUM` is defined in its own submodule so that its private components are
// not accessible.
mod repr_c {
    use core;
    use {c, limb};
    use libc;

    /* Keep in sync with `bignum_st` in openss/bn.h. */
    #[repr(C)]
    pub struct BIGNUM {
        d: *mut limb::Limb,
        top: c::int,
        dmax: c::int,
        neg: c::int,
        flags: c::int,
    }

    impl Drop for BIGNUM {
        fn drop(&mut self) {
            // Keep this in sync with `GFp_BN_free()`.

            // In particular, this doesn't work for `BN_FLG_STATIC_DATA`.
            assert_eq!(self.flags, 0);
            unsafe {
                let d: *mut limb::Limb = self.d;
                libc::free(d as *mut libc::c_void)
            }
        }
    }

    impl BIGNUM {
        pub fn zero() -> Self {
            BIGNUM {
                d: core::ptr::null_mut(),
                top: 0,
                dmax: 0,
                neg: 0,
                flags: 0,
            }
        }
    }
}

pub use self::repr_c::BIGNUM;

extern {
    fn GFp_BN_one(r: &mut BIGNUM) -> c::int;
    fn GFp_BN_bin2bn(in_: *const u8, len: c::size_t, ret: &mut BIGNUM)
                     -> c::int;
    fn GFp_BN_bn2bin_padded(out_: *mut u8, len: c::size_t, in_: &BIGNUM)
                            -> c::int;
    fn GFp_BN_ucmp(a: &BIGNUM, b: &BIGNUM) -> c::int;
    fn GFp_BN_get_positive_u64(a: &BIGNUM) -> u64;
    fn GFp_BN_equal_consttime(a: &BIGNUM, b: &BIGNUM) -> c::int;
    fn GFp_BN_is_odd(a: &BIGNUM) -> c::int;
    fn GFp_BN_is_zero(a: &BIGNUM) -> c::int;
    fn GFp_BN_is_one(a: &BIGNUM) -> c::int;
    fn GFp_BN_num_bits(bn: *const BIGNUM) -> c::size_t;
    fn GFp_bn_mont_n0(n: &BIGNUM) -> u64;
    fn GFp_bn_mod_exp_base_2_vartime(r: &mut BIGNUM, p: c::size_t,
                                     n: &BIGNUM, n0: &N0) -> c::int;

    // `r` and `a` may alias.
    fn GFp_BN_from_mont(r: *mut BIGNUM, a: *const BIGNUM, n: &BIGNUM, n0: &N0)
                        -> c::int;
    fn GFp_BN_mod_inverse_odd(r: *mut BIGNUM, out_no_inverse: &mut c::int,
                              a: *const BIGNUM, m: &BIGNUM) -> c::int;

    // `r` and/or 'a' and/or 'b' may alias.
    fn GFp_BN_mod_mul_mont(r: *mut BIGNUM, a: *const BIGNUM, b: *const BIGNUM,
                            n: &BIGNUM, n0: &N0) -> c::int;
    fn GFp_BN_mod_add_quick(r: *mut BIGNUM, a: *const BIGNUM, b: *const BIGNUM,
                            m: &BIGNUM) -> c::int;
    fn GFp_BN_mod_sub_quick(r: *mut BIGNUM, a: *const BIGNUM, b: *const BIGNUM,
                            m: &BIGNUM) -> c::int;

    // `r` and `a` may alias.
    fn GFp_BN_mod_exp_mont_consttime(r: *mut BIGNUM, a_mont: *const BIGNUM,
                                     p: &BIGNUM, one_mont: &BIGNUM, n: &BIGNUM,
                                     n0: &N0) -> c::int;

    // The use of references here implies lack of aliasing.
    fn GFp_BN_copy(a: &mut BIGNUM, b: &BIGNUM) -> c::int;
    fn GFp_BN_from_montgomery_word(r: &mut BIGNUM, a: &mut BIGNUM, n: &BIGNUM,
                                   n0: &N0) -> c::int;
}

#[allow(improper_ctypes)]
extern {
    fn GFp_BN_rand_range_ex(r: &mut BIGNUM, max_exclusive: &BIGNUM,
                            rng: &mut rand::RAND) -> c::int;
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::GFp_BN_ucmp;
    use untrusted;
    use test;

    #[test]
    fn test_positive_integer_from_be_bytes_empty() {
        // Empty values are rejected.
        assert!(Positive::from_be_bytes(
                    untrusted::Input::from(&[])).is_err());
    }

    #[test]
    fn test_positive_integer_from_be_bytes_zero() {
        // The zero value is rejected.
        assert!(Positive::from_be_bytes(
                    untrusted::Input::from(&[0])).is_err());
        // A zero with a leading zero is rejected.
        assert!(Positive::from_be_bytes(
                    untrusted::Input::from(&[0, 0])).is_err());
        // A non-zero value with a leading zero is rejected.
        assert!(Positive::from_be_bytes(
                    untrusted::Input::from(&[0, 1])).is_err());
        // A non-zero value with no leading zeros is accepted.
        assert!(Positive::from_be_bytes(
                    untrusted::Input::from(&[1])).is_ok());
        // A non-zero value with that ends in a zero byte is accepted.
        assert!(Positive::from_be_bytes(
                    untrusted::Input::from(&[1, 0])).is_ok());
    }

    #[test]
    fn test_odd_positive_from_even() {
        let x = Positive::from_be_bytes(untrusted::Input::from(&[4])).unwrap();
        assert!(x.into_odd_positive().is_err());
    }


    // Type-level representation of an arbitrary modulus.
    struct M {}

    #[test]
    fn test_elem_exp_consttime() {
        test::from_file("src/rsa/bigint_elem_exp_consttime_tests.txt",
                        |section, test_case| {
            assert_eq!(section, "");

            let m = consume_modulus::<M>(test_case, "M");
            let expected_result = consume_elem(test_case, "ModExp", &m);
            let base = consume_elem(test_case, "A", &m);
            let e = consume_odd_positive(test_case, "E");

            let base = into_encoded(base, &m);
            let one = Positive::from_be_bytes(
                        untrusted::Input::from(&[1])).unwrap();
            let one = one.into_elem(&m).unwrap();
            let one = into_encoded(one, &m);
            let actual_result = elem_exp_consttime(base, &e, &one, &m).unwrap();
            assert_elem_eq(&actual_result, &expected_result);

            Ok(())
        })
    }

    #[test]
    fn test_elem_exp_vartime() {
        test::from_file("src/rsa/bigint_elem_exp_vartime_tests.txt",
                        |section, test_case| {
            assert_eq!(section, "");

            let m = consume_modulus::<M>(test_case, "M");
            let expected_result = consume_elem(test_case, "ModExp", &m);
            let base = consume_elem(test_case, "A", &m);
            let e = consume_public_exponent(test_case, "E");

            let base = into_encoded(base, &m);
            let actual_result = elem_exp_vartime(base, e, &m).unwrap();
            let actual_result = actual_result.into_unencoded(&m).unwrap();
            assert_elem_eq(&actual_result, &expected_result);

            Ok(())
        })
    }

    #[test]
    fn test_elem_mul() {
        test::from_file("src/rsa/bigint_elem_mul_tests.txt",
                        |section, test_case| {
            assert_eq!(section, "");

            let m = consume_modulus::<M>(test_case, "M");
            let expected_result = consume_elem(test_case, "ModMul", &m);
            let a = consume_elem(test_case, "A", &m);
            let b = consume_elem(test_case, "B", &m);

            let b = into_encoded(b, &m);
            let a = into_encoded(a, &m);
            let actual_result = elem_mul(&a, b, &m).unwrap();
            let actual_result = actual_result.into_unencoded(&m).unwrap();
            assert_elem_eq(&actual_result, &expected_result);

            Ok(())
        })
    }

    #[test]
    fn test_elem_squared() {
        test::from_file("src/rsa/bigint_elem_squared_tests.txt",
                        |section, test_case| {
            assert_eq!(section, "");

            let m = consume_modulus::<M>(test_case, "M");
            let expected_result = consume_elem(test_case, "ModSquare", &m);
            let a = consume_elem(test_case, "A", &m);

            let a = into_encoded(a, &m);
            let actual_result = elem_squared(a, &m).unwrap();
            let actual_result = actual_result.into_unencoded(&m).unwrap();
            assert_elem_eq(&actual_result, &expected_result);

            Ok(())
        })
    }

    #[test]
    fn test_elem_reduced() {
        test::from_file("src/rsa/bigint_elem_reduced_tests.txt",
                        |section, test_case| {
            assert_eq!(section, "");

            struct MM {}
            unsafe impl SmallerModulus<MM> for M {}
            unsafe impl NotMuchSmallerModulus<MM> for M {}

            let m = consume_modulus::<M>(test_case, "M");
            let expected_result = consume_elem(test_case, "R", &m);
            let a = consume_elem_unchecked::<MM>(test_case, "A");

            let actual_result = elem_reduced(&a, &m).unwrap();
            let oneRR = m.compute_oneRR().unwrap();
            let actual_result = elem_mul(&oneRR, actual_result, &m).unwrap();
            assert_elem_eq(&actual_result, &expected_result);

            Ok(())
        })
    }

    #[test]
    fn test_elem_reduced_once() {
        test::from_file("src/rsa/bigint_elem_reduced_once_tests.txt",
                        |section, test_case| {
            assert_eq!(section, "");

            struct N {}
            struct QQ {}
            unsafe impl SmallerModulus<N> for QQ {}
            unsafe impl SlightlySmallerModulus<N> for QQ {}

            let qq = consume_modulus::<QQ>(test_case, "QQ");
            let expected_result = consume_elem::<QQ>(test_case, "R", &qq);
            let n = consume_modulus::<N>(test_case, "N");
            let a = consume_elem::<N>(test_case, "A", &n);

            let actual_result = elem_reduced_once(&a, &qq).unwrap();
            assert_elem_eq(&actual_result, &expected_result);

            Ok(())
        })
    }

    fn consume_elem<M>(test_case: &mut test::TestCase, name: &str, m: &Modulus<M>)
                       -> Elem<M, Unencoded> {
        let value = consume_nonnegative(test_case, name);
        value.into_elem::<M>(m).unwrap()
    }

    fn consume_elem_unchecked<M>(test_case: &mut test::TestCase, name: &str)
            -> Elem<M, Unencoded> {
        let value = consume_nonnegative(test_case, name);
        Elem {
            value: value,
            m: PhantomData,
            encoding: PhantomData,
        }
    }

    fn consume_modulus<M>(test_case: &mut test::TestCase, name: &str)
                          -> Modulus<M> {
        let value = consume_odd_positive(test_case, name);
        value.into_modulus().unwrap()
    }

    fn consume_public_exponent(test_case: &mut test::TestCase, name: &str)
                               -> PublicExponent {
        let value = consume_odd_positive(test_case, name);
        value.into_public_exponent().unwrap()
    }

    fn consume_odd_positive(test_case: &mut test::TestCase, name: &str)
                            -> OddPositive {
        let bytes = test_case.consume_bytes(name);
        let value =
            Positive::from_be_bytes(untrusted::Input::from(&bytes)).unwrap();
        value.into_odd_positive().unwrap()
    }

    fn consume_nonnegative(test_case: &mut test::TestCase, name: &str)
                           -> Nonnegative {
        let bytes = test_case.consume_bytes(name);
        let mut r = Nonnegative::zero().unwrap();
        bssl::map_result(unsafe {
            GFp_BN_bin2bn(bytes.as_ptr(), bytes.len(), r.as_mut_ref())
        }).unwrap();
        r
    }

    fn assert_elem_eq<M, E>(a: &Elem<M, E>, b: &Elem<M, E>) {
        let r = unsafe { GFp_BN_ucmp(a.value.as_ref(), b.value.as_ref()) };
        assert_eq!(r, 0)
    }

    fn into_encoded<M>(a: Elem<M, Unencoded>, m: &Modulus<M>) -> Elem<M, R> {
        let oneRR = m.compute_oneRR().unwrap();
        elem_mul(&oneRR, a, m).unwrap()
    }
}
