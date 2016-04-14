/*
 * Utilities for constant-time cryptography.
 *
 * Author: Emilia Kasper (emilia@openssl.org)
 * Based on previous work by Bodo Moeller, Emilia Kasper, Adam Langley
 * (Google).
 * ====================================================================
 * Copyright (c) 2014 The OpenSSL Project.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *    "This product includes cryptographic software written by
 *     Eric Young (eay@cryptsoft.com)"
 *    The word 'cryptographic' can be left out if the rouines from the library
 *    being used are not cryptographic related :-).
 * 4. If you include any Windows specific code (or a derivative thereof) from
 *    the apps directory (application code) you must include an acknowledgement:
 *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
 *
 * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * The licence and distribution terms for any publically available version or
 * derivative of this code cannot be changed.  i.e. this code cannot simply be
 * copied and put under another distribution licence
 * [including the GNU Public Licence.]
 */

#include "internal.h"

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>


static const unsigned int CONSTTIME_TRUE = (unsigned)(~0);
static const unsigned int CONSTTIME_FALSE = 0;

static int test_is_zero(unsigned int a) {
  unsigned int c = constant_time_is_zero(a);
  if (a == 0 && c != CONSTTIME_TRUE) {
    fprintf(stderr,
            "Test failed for constant_time_is_zero(%du): expected %du (TRUE), "
            "got %du\n",
            a, CONSTTIME_TRUE, c);
    return 1;
  } else if (a != 0 && c != CONSTTIME_FALSE) {
    fprintf(stderr,
            "Test failed for constant_time_is_zero(%du): expected %du (FALSE), "
            "got %du\n",
            a, CONSTTIME_FALSE, c);
    return 1;
  }
  return 0;
}

static int test_eq_int(int a, int b) {
  unsigned int equal = constant_time_eq_int(a, b);
  if (a == b && equal != CONSTTIME_TRUE) {
    fprintf(stderr,
            "Test failed for constant_time_eq_int(%d, %d): expected %du(TRUE), "
            "got %du\n",
            a, b, CONSTTIME_TRUE, equal);
    return 1;
  } else if (a != b && equal != CONSTTIME_FALSE) {
    fprintf(stderr,
            "Test failed for constant_time_eq_int(%d, %d): expected "
            "%du(FALSE), got %du\n",
            a, b, CONSTTIME_FALSE, equal);
    return 1;
  }
  return 0;
}

static unsigned int test_values[] = {0, 1, 1024, 12345, 32000, UINT_MAX / 2 - 1,
                                     UINT_MAX / 2, UINT_MAX / 2 + 1,
                                     UINT_MAX - 1, UINT_MAX};

static int signed_test_values[] = {
    0,     1,      -1,      1024,    -1024,       12345,      -12345,
    32000, -32000, INT_MAX, INT_MIN, INT_MAX - 1, INT_MIN + 1};

int main(void) {
  unsigned int a, i, j;
  int c, d;
  int num_failed = 0, num_all = 0;

  for (i = 0; i < sizeof(test_values) / sizeof(int); ++i) {
    a = test_values[i];
    num_failed += test_is_zero(a);
    num_all += 2;
  }

  for (i = 0; i < sizeof(signed_test_values) / sizeof(int); ++i) {
    c = signed_test_values[i];
    for (j = 0; j < sizeof(signed_test_values) / sizeof(int); ++j) {
      d = signed_test_values[j];
      num_failed += test_eq_int(c, d);
      num_all += 3;
    }
  }

  if (!num_failed) {
    return EXIT_SUCCESS;
  } else {
    fprintf(stdout, "%d of %d tests failed!\n", num_failed, num_all);
    return EXIT_FAILURE;
  }
}
