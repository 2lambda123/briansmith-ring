/* Originally written by Bodo Moeller for the OpenSSL project.
 * ====================================================================
 * Copyright (c) 1998-2005 The OpenSSL Project.  All rights reserved.
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
 *    for use in the OpenSSL Toolkit. (http://www.openssl.org/)"
 *
 * 4. The names "OpenSSL Toolkit" and "OpenSSL Project" must not be used to
 *    endorse or promote products derived from this software without
 *    prior written permission. For written permission, please contact
 *    openssl-core@openssl.org.
 *
 * 5. Products derived from this software may not be called "OpenSSL"
 *    nor may "OpenSSL" appear in their names without prior written
 *    permission of the OpenSSL Project.
 *
 * 6. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by the OpenSSL Project
 *    for use in the OpenSSL Toolkit (http://www.openssl.org/)"
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
 * ====================================================================
 *
 * This product includes cryptographic software written by Eric Young
 * (eay@cryptsoft.com).  This product includes software written by Tim
 * Hudson (tjh@cryptsoft.com).
 *
 */
/* ====================================================================
 * Copyright 2002 Sun Microsystems, Inc. ALL RIGHTS RESERVED.
 *
 * Portions of the attached software ("Contribution") are developed by
 * SUN MICROSYSTEMS, INC., and are contributed to the OpenSSL project.
 *
 * The Contribution is licensed pursuant to the OpenSSL open source
 * license provided above.
 *
 * The elliptic curve binary polynomial software is originally written by
 * Sheueling Chang Shantz and Douglas Stebila of Sun Microsystems
 * Laboratories. */

#ifndef OPENSSL_HEADER_EC_H
#define OPENSSL_HEADER_EC_H

#include <openssl/base.h>

#if defined(__cplusplus)
extern "C" {
#endif


/* Low-level operations on elliptic curves. */


typedef struct ec_group_st EC_GROUP;
typedef struct ec_point_st EC_POINT;


/* Elliptic curve groups. */

extern const EC_GROUP EC_GROUP_P256;
extern const EC_GROUP EC_GROUP_P384;

/* EC_GROUP_get0_generator returns a pointer to the internal |EC_POINT| object
 * in |group| that specifies the generator for the group. */
OPENSSL_EXPORT const EC_POINT *EC_GROUP_get0_generator(const EC_GROUP *group);

/* EC_GROUP_get0_order returns a pointer to the internal |BIGNUM| object in
 * |group| that specifies the order of the group. */
OPENSSL_EXPORT const BIGNUM *EC_GROUP_get0_order(const EC_GROUP *group);

/* EC_GROUP_get_degree returns the number of bits needed to represent an
 * element of the field underlying |group|. */
OPENSSL_EXPORT unsigned EC_GROUP_get_degree(const EC_GROUP *group);


/* Points on elliptic curves. */

/* EC_POINT_new returns a fresh |EC_POINT| object in the given group, or NULL
 * on error. */
OPENSSL_EXPORT EC_POINT *EC_POINT_new(const EC_GROUP *group);

/* EC_POINT_free frees |point| and the data that it points to. */
OPENSSL_EXPORT void EC_POINT_free(EC_POINT *point);

/* EC_POINT_set_to_infinity sets |point| to be the "point at infinity" for the
 * given group. */
OPENSSL_EXPORT int EC_POINT_set_to_infinity(const EC_GROUP *group,
                                            EC_POINT *point);

/* EC_POINT_is_at_infinity returns one iff |point| is the point at infinity and
 * zero otherwise. */
OPENSSL_EXPORT int EC_POINT_is_at_infinity(const EC_GROUP *group,
                                           const EC_POINT *point);


#if defined(__cplusplus)
}  /* extern C */
#endif

#define EC_R_BUFFER_TOO_SMALL 100
#define EC_R_COORDINATES_OUT_OF_RANGE 101
#define EC_R_D2I_ECPKPARAMETERS_FAILURE 102
#define EC_R_EC_GROUP_NEW_BY_NAME_FAILURE 103
#define EC_R_GROUP2PKPARAMETERS_FAILURE 104
#define EC_R_I2D_ECPKPARAMETERS_FAILURE 105
#define EC_R_INCOMPATIBLE_OBJECTS 106
#define EC_R_INVALID_COMPRESSED_POINT 107
#define EC_R_INVALID_COMPRESSION_BIT 108
#define EC_R_INVALID_ENCODING 109
#define EC_R_INVALID_FIELD 110
#define EC_R_INVALID_FORM 111
#define EC_R_INVALID_GROUP_ORDER 112
#define EC_R_INVALID_PRIVATE_KEY 113
#define EC_R_MISSING_PARAMETERS 114
#define EC_R_MISSING_PRIVATE_KEY 115
#define EC_R_NON_NAMED_CURVE 116
#define EC_R_NOT_INITIALIZED 117
#define EC_R_PKPARAMETERS2GROUP_FAILURE 118
#define EC_R_POINT_AT_INFINITY 119
#define EC_R_POINT_IS_NOT_ON_CURVE 120
#define EC_R_SLOT_FULL 121
#define EC_R_UNDEFINED_GENERATOR 122
#define EC_R_UNKNOWN_GROUP 123
#define EC_R_UNKNOWN_ORDER 124
#define EC_R_WRONG_ORDER 125
#define EC_R_BIGNUM_OUT_OF_RANGE 126
#define EC_R_WRONG_CURVE_PARAMETERS 127

#endif  /* OPENSSL_HEADER_EC_H */
