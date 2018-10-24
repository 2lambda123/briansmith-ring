// Copyright 2018 Brian Smith.
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

//! Unauthenticated stream cipher.
//!
//! # Warning
//! This API does not provide any authentification! You should use the
//! [aead](aead/index.html) module instead.
//!
//! C analog: `EVP_CIPHER`
//!
//! Go analog: [`crypto.cipher.Stream`]
//!
//! [`crypto.cipher.Stream`]: https://golang.org/pkg/crypto/cipher/#Stream

use crate::{aead, error, init, polyfill};

pub use self::chacha20::CHACHA20;

/// A key for decrypting data encrypted using an unauthenticated stream cipher.
///
/// C analog: `EVP_CIPHER_CTX`
///
/// Go analog: [`crypto.cipher.Stream`]
pub struct DecryptingKey {
    key: Key,
}

impl DecryptingKey {
    /// Create a new decrypting key.
    ///
    /// `key_bytes` must be exactly `algorithm.key_len` bytes long.
    ///
    /// C analogs: `EVP_CIPHER_CTX_init`.
    ///
    /// Go analog:
    ///   [`crypto.aes.NewCipher`](https://golang.org/pkg/crypto/aes/#NewCipher)
    #[inline]
    pub fn new(algorithm: &'static Algorithm, key_bytes: &[u8])
               -> Result<DecryptingKey, error::Unspecified> {
        Ok(DecryptingKey {
            key: Key::new(algorithm, key_bytes)?,
        })
    }

    /// The key's unauthenticated stream cipher algorithm.
    ///
    /// C analog: `EVP_CIPHER_CTX.cipher`
    #[inline(always)]
    pub fn algorithm(&self) -> &'static Algorithm { self.key.algorithm() }
}

/// Decrypts the input data in place.
pub fn decrypt_in_place<'a>(key: &DecryptingKey, nonce: &[u8],
                            in_out: &'a mut [u8])
                            -> Result<&'a mut [u8], error::Unspecified> {
    do_encryption_in_place(&key.key, nonce, in_out)?;
    Ok(&mut in_out[..])
}

/// A key for encrypting data using an unauthenticated stream cipher.
///
/// C analog: `EVP_CIPHER_CTX`
///
/// Go analog: [`crypto.cipher.Stream`]
pub struct EncryptingKey {
    key: Key,
}

impl EncryptingKey {
    /// Create a new encrypting key.
    ///
    /// `key_bytes` must be exactly `algorithm.key_len` bytes long.
    ///
    /// C analogs: `EVP_CIPHER_CTX_init`.
    ///
    /// Go analog:
    ///   [`crypto.aes.NewCipher`](https://golang.org/pkg/crypto/aes/#NewCipher)
    #[inline]
    pub fn new(algorithm: &'static Algorithm, key_bytes: &[u8])
               -> Result<EncryptingKey, error::Unspecified> {
        Ok(EncryptingKey {
            key: Key::new(algorithm, key_bytes)?,
        })
    }

    /// The key's unauthenticated stream cipher algorithm.
    ///
    /// C analog: `EVP_CIPHER_CTX.cipher`
    #[inline(always)]
    pub fn algorithm(&self) -> &'static Algorithm { self.key.algorithm() }
}

/// Encrypts the input data in place.
pub fn encrypt_in_place(key: &EncryptingKey, nonce: &[u8], in_out: &mut [u8])
                        -> Result<usize, error::Unspecified> {
    do_encryption_in_place(&key.key, nonce, in_out)?;
    Ok(in_out.len())
}

fn do_encryption_in_place(key: &Key, nonce: &[u8], in_out: &mut [u8])
                        -> Result<(), error::Unspecified> {
    let nonce = slice_as_array_ref!(nonce, NONCE_LEN)?;
    check_per_nonce_max_bytes(key.algorithm.max_input_len, in_out.len())?;
    (key.algorithm.xor_in_place)(&key.ctx_buf, nonce, in_out)
}

/// `DecryptingKey` and `EncryptingKey` are type-safety wrappers around `Key`,
/// which does all the actual work via the C stream cipher interface.
///
/// C analog: `EVP_CIPHER_CTX`
struct Key {
    ctx_buf: [u64; KEY_CTX_BUF_ELEMS],
    algorithm: &'static Algorithm,
}

/// TODO: once unauthenticated_encryption supports AES, we should move the
/// definition of KEY_CTX_BUF_ELEMS here.
const KEY_CTX_BUF_ELEMS: usize = aead::KEY_CTX_BUF_ELEMS;

impl Key {
    fn new(algorithm: &'static Algorithm, key_bytes: &[u8]) -> Result<Self, error::Unspecified> {
        if key_bytes.len() != algorithm.key_len() {
            return Err(error::Unspecified);
        }

        let mut r = Key {
            algorithm,
            ctx_buf: [0; KEY_CTX_BUF_ELEMS],
        };

        init::init_once();
        {
            let ctx_buf_bytes = polyfill::slice::u64_as_u8_mut(&mut r.ctx_buf);
            (r.algorithm.init)(ctx_buf_bytes, key_bytes)?;
        }

        Ok(r)
    }

    /// The key's unauthenticated stream cipher algorithm.
    #[inline(always)]
    fn algorithm(&self) -> &'static Algorithm { self.algorithm }
}

/// An unauthenticated stream cipher Algorithm.
///
/// C analog: `EVP_CIPHER`
///
/// Go analog:
///     [`crypto.cipher.Stream`](https://golang.org/pkg/crypto/cipher/#Stream)
pub struct Algorithm {
    init: fn(ctx_buf: &mut [u8], key: &[u8]) -> Result<(), error::Unspecified>,

    xor_in_place: fn(ctx: &[u64; KEY_CTX_BUF_ELEMS], nonce: &[u8; NONCE_LEN],
                      in_out: &mut [u8]) -> Result<(), error::Unspecified>,

    key_len: usize,
    id: AlgorithmID,

    /// Use `max_input_len!()` to initialize this.
    // TODO: Make this `usize`.
    max_input_len: u64,
}

/// TODO: Make this a `const fn` when those become stable.
#[macro_export]
macro_rules! max_input_len {
    ($block_len:expr, $overhead_blocks_per_nonce:expr) => {
        // Each of our AEADs use a 32-bit block counter so the maximum is the
        // largest input that will not overflow the counter.
        (((1u64 << 32) - $overhead_blocks_per_nonce) * $block_len)
    }
}

impl Algorithm {
    /// The length of the key.
    ///
    /// C analog: `EVP_CIPHER_key_length`
    #[inline(always)]
    pub fn key_len(&self) -> usize { self.key_len }

    /// The length of the nonces.
    ///
    /// C analog: `EVP_CIPHER_nonce_length`
    ///
    /// Go analog:
    /// [`crypto.cipher.Stream.NonceSize`](https://golang.org/pkg/crypto/cipher/#Stream)
    #[inline(always)]
    pub fn nonce_len(&self) -> usize { NONCE_LEN }
}

derive_debug_via_self!(Algorithm, self.id);

#[derive(Debug, Eq, PartialEq)]
enum AlgorithmID {
    CHACHA20,
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool { self.id == other.id }
}

impl Eq for Algorithm {}

// All the stream ciphers we support use 128-bit nonces.
const NONCE_LEN: usize = 128 / 8;

pub(crate) fn check_per_nonce_max_bytes(max_input_len: u64, in_out_len: usize)
                             -> Result<(), error::Unspecified> {
    if polyfill::u64_from_usize(in_out_len) > max_input_len {
        return Err(error::Unspecified);
    }
    Ok(())
}

pub(crate) mod chacha20;
