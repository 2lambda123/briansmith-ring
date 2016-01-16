/* ====================================================================
 * Copyright (c) 1999-2007 The OpenSSL Project.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. All advertising materials mentioning features or use of this
 *    software must display the following acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit. (http://www.OpenSSL.org/)"
 *
 * 4. The names "OpenSSL Toolkit" and "OpenSSL Project" must not be used to
 *    endorse or promote products derived from this software without
 *    prior written permission. For written permission, please contact
 *    licensing@OpenSSL.org.
 *
 * 5. Products derived from this software may not be called "OpenSSL"
 *    nor may "OpenSSL" appear in their names without prior written
 *    permission of the OpenSSL Project.
 *
 * 6. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit (http://www.OpenSSL.org/)"
 *
 * THIS SOFTWARE IS PROVIDED BY THE OpenSSL PROJECT ``AS IS'' AND ANY
 * EXPRESSED OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE OpenSSL PROJECT OR
 * ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 * ==================================================================== */

#ifndef OPENSSL_HEADER_MD32_COMMON_H
#define OPENSSL_HEADER_MD32_COMMON_H

#include <openssl/base.h>


#if defined(__cplusplus)
extern "C" {
#endif


#if !defined(PEDANTIC) && defined(__GNUC__) && __GNUC__ >= 2 && \
    !defined(OPENSSL_NO_ASM)
#if defined(OPENSSL_X86) || defined(OPENSSL_X86_64)
/* The first macro gives a ~30-40% performance improvement in SHA-256 compiled
 * with gcc on P4. This can only be done on x86, where unaligned data fetches
 * are possible. */
#define HOST_c2l(c, l)                       \
  (void)({                                   \
    uint32_t r = *((const uint32_t *)(c));   \
    __asm__("bswapl %0" : "=r"(r) : "0"(r)); \
    (c) += 4;                                \
    (l) = r;                                 \
  })
#elif defined(__aarch64__) && defined(__BYTE_ORDER__)
#if defined(__ORDER_LITTLE_ENDIAN__) && \
    __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
#define HOST_c2l(c, l)                                                 \
  (void)({                                                             \
    uint32_t r;                                                        \
    __asm__("rev %w0, %w1" : "=r"(r) : "r"(*((const uint32_t *)(c)))); \
    (c) += 4;                                                          \
    (l) = r;                                                           \
  })
#elif defined(__ORDER_BIG_ENDIAN__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define HOST_c2l(c, l) (void)((l) = *((const uint32_t *)(c)), (c) += 4)
#endif /* __aarch64__ && __BYTE_ORDER__ */
#endif /* ARCH */
#endif /* !PEDANTIC && GNUC && !NO_ASM */

#ifndef HOST_c2l
#define HOST_c2l(c, l)                        \
  (void)(l = (((uint32_t)(*((c)++))) << 24),  \
         l |= (((uint32_t)(*((c)++))) << 16), \
         l |= (((uint32_t)(*((c)++))) << 8), l |= (((uint32_t)(*((c)++)))))
#endif


#if defined(__cplusplus)
} /* extern C */
#endif

#endif /* OPENSSL_HEADER_MD32_COMMON_H */
