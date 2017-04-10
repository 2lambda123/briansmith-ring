// Copyright 2015-2017 Brian Smith.
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

use {error, init, rand};
use untrusted;

/// A key agreement algorithm.
// XXX: This doesn't seem like the best place for this.
pub struct AgreementAlgorithmImpl {
    pub curve: &'static Curve,
    pub ecdh: fn(out: &mut [u8], private_key: &PrivateKey,
                 peer_public_key: untrusted::Input)
                 -> Result<(), error::Unspecified>,
}

pub struct Curve {
    pub public_key_len: usize,
    pub elem_and_scalar_len: usize,

    pub id: CurveID,

    generate_private_key: fn(rng: &rand::SecureRandom)
                             -> Result<PrivateKey, error::Unspecified>,

    public_from_private: fn(public_out: &mut [u8], private_key: &PrivateKey)
                            -> Result<(), error::Unspecified>,
}

#[derive(Clone, Copy, PartialEq)]
pub enum CurveID {
    Curve25519,
    P256,
    P384,
}

pub struct PrivateKey {
    bytes: [u8; SCALAR_MAX_BYTES],
}

impl<'a> PrivateKey {
    pub fn generate(curve: &Curve, rng: &rand::SecureRandom)
                    -> Result<PrivateKey, error::Unspecified> {
        init::init_once();
        (curve.generate_private_key)(rng)
    }

    /// Panics if `test_vector` is not the correct length.
    #[cfg(test)]
    pub fn from_test_vector(curve: &Curve, test_vector: &[u8]) -> PrivateKey {
        init::init_once();
        let mut bytes = [0; SCALAR_MAX_BYTES];
        bytes[..curve.elem_and_scalar_len].copy_from_slice(test_vector);
        PrivateKey { bytes: bytes }
    }

    #[cfg(test)]
    pub fn bytes(&'a self) -> &'a [u8] { &self.bytes[..] }

    #[inline(always)]
    pub fn compute_public_key(&self, curve: &Curve, out: &mut [u8])
                              -> Result<(), error::Unspecified> {
        check!(out.len() == curve.public_key_len);
        (curve.public_from_private)(out, self)
    }
}


const ELEM_MAX_BITS: usize = 384;
pub const ELEM_MAX_BYTES: usize = (ELEM_MAX_BITS + 7) / 8;

const SCALAR_MAX_BYTES: usize = ELEM_MAX_BYTES;

/// The maximum length, in bytes, of an encoded public key.
pub const PUBLIC_KEY_MAX_LEN: usize = 1 + (2 * ELEM_MAX_BYTES);


pub mod eddsa;

#[path = "suite_b/suite_b.rs"]
pub mod suite_b;

pub mod x25519;
