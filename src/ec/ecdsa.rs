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

#![allow(unsafe_code)]

//! ECDSA Signatures.

use {bssl, c, digest, ec, signature, signature_impl};
use input::Input;

#[cfg(not(feature = "no_heap"))]
struct ECDSA {
    digest_alg: &'static digest::Algorithm,
    ec_group_fn: unsafe extern fn() -> *const ec::EC_GROUP,
}

#[cfg(not(feature = "no_heap"))]
impl signature_impl::VerificationAlgorithmImpl for ECDSA {
    fn verify(&self, public_key: Input, msg: Input, signature: Input)
              -> Result<(), ()> {
        let digest = digest::digest(self.digest_alg, msg.as_slice_less_safe());
        let signature = signature.as_slice_less_safe();
        let public_key = public_key.as_slice_less_safe();
        bssl::map_result(unsafe {
            ECDSA_verify_signed_digest((self.ec_group_fn)(),
                                       digest.algorithm().nid,
                                       digest.as_ref().as_ptr(),
                                       digest.as_ref().len(), signature.as_ptr(),
                                       signature.len(), public_key.as_ptr(),
                                       public_key.len())
        })
    }
}

// TODO: After ecdsa_test.cc is removed, this function should be removed and
// the caller should be changed to call `SHA512_4` directly. Also, the
// alternative implementation of this in crypto/test should be removed at
// that time.
#[allow(non_snake_case)]
#[doc(hidden)]
#[no_mangle]
pub extern fn BN_generate_dsa_nonce_digest(
        out: *mut u8, out_len: c::size_t,
        part1: *const u8, part1_len: c::size_t,
        part2: *const u8, part2_len: c::size_t,
        part3: *const u8, part3_len: c::size_t,
        part4: *const u8, part4_len: c::size_t)
        -> c::int {
    digest::SHA512_4(out, out_len, part1, part1_len, part2, part2_len, part3,
                     part3_len, part4, part4_len);
    1
}

macro_rules! ecdsa {
    ( $VERIFY_ALGORITHM:ident, $curve_name:expr, $ec_group_fn:expr,
      $digest_alg_name:expr, $digest_alg:expr ) => {
        #[cfg(not(feature = "no_heap"))]
        #[doc="Verification of ECDSA signatures using the "]
        #[doc=$curve_name]
        #[doc=" curve and the "]
        #[doc=$digest_alg_name]
        #[doc=" digest algorithm."]
        ///
        /// Public keys are encoding in uncompressed form using the
        /// Octet-String-to-Elliptic-Curve-Point algorithm in [SEC 1: Elliptic
        /// Curve Cryptography, Version 2.0](http://www.secg.org/sec1-v2.pdf).
        /// Public keys are validated during key agreement as described in
        /// [NIST Special Publication 800-56A, revision
        /// 2](http://csrc.nist.gov/groups/ST/toolkit/documents/SP800-56Arev1_3-8-07.pdf)
        /// Section 5.6.2.5 and the [Suite B Implementer's Guide to NIST SP
        /// 800-56A](https://www.nsa.gov/ia/_files/suiteb_implementer_g-113808.pdf)
        /// Appendix B.3. Note that, as explained in the NSA guide, "partial"
        /// validation is equivalent to "full" validation for prime-order
        /// curves like this one.
        ///
        /// TODO: Each of the encoded coordinates are verified to be the
        /// correct length, but values of the allowed length that haven't been
        /// reduced modulo *q* are currently reduced mod *q* during
        /// verification. Soon, coordinates larger than *q* - 1 will be
        /// rejected.
        ///
        /// The signature will be parsed as a DER-encoded `Ecdsa-Sig-Value` as
        /// described in [RFC 3279 Section
        /// 2.2.3](https://tools.ietf.org/html/rfc3279#section-2.2.3). Both *r*
        /// and *s* are verified to be in the range [1, *n* - 1].
        ///
        /// Not available in `no_heap` mode.
        pub static $VERIFY_ALGORITHM: signature::VerificationAlgorithm =
                signature::VerificationAlgorithm {
            implementation: &ECDSA {
                digest_alg: $digest_alg,
                ec_group_fn: $ec_group_fn,
            }
        };
    }
}

ecdsa!(ECDSA_P256_SHA1_VERIFY, "P-256 (secp256r1)", ec::EC_GROUP_P256, "SHA-1",
       &digest::SHA1);
ecdsa!(ECDSA_P256_SHA256_VERIFY, "P-256 (secp256r1)", ec::EC_GROUP_P256,
       "SHA-256", &digest::SHA256);
ecdsa!(ECDSA_P256_SHA384_VERIFY, "P-256 (secp256r1)", ec::EC_GROUP_P256,
       "SHA-384", &digest::SHA384);
ecdsa!(ECDSA_P256_SHA512_VERIFY, "P-256 (secp256r1)", ec::EC_GROUP_P256,
       "SHA-512", &digest::SHA512);

ecdsa!(ECDSA_P384_SHA1_VERIFY, "P-384 (secp384r1)", ec::EC_GROUP_P384, "SHA-1",
       &digest::SHA1);
ecdsa!(ECDSA_P384_SHA256_VERIFY, "P-384 (secp384r1)", ec::EC_GROUP_P384,
       "SHA-256", &digest::SHA256);
ecdsa!(ECDSA_P384_SHA384_VERIFY, "P-384 (secp384r1)", ec::EC_GROUP_P384,
       "SHA-384", &digest::SHA384);
ecdsa!(ECDSA_P384_SHA512_VERIFY, "P-384 (secp384r1)", ec::EC_GROUP_P384,
       "SHA-512", &digest::SHA512);


extern {
    #[cfg(not(feature = "no_heap"))]
    fn ECDSA_verify_signed_digest(group: *const ec::EC_GROUP, hash_nid: c::int,
                                  digest: *const u8, digest_len: c::size_t,
                                  sig_der: *const u8, sig_der_len: c::size_t,
                                  key_octets: *const u8,
                                  key_octets_len: c::size_t) -> c::int;
}
