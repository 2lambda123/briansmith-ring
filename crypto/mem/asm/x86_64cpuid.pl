#! /usr/bin/env perl
# Copyright 2015-2016 The OpenSSL Project Authors. All Rights Reserved.
#
# Licensed under the OpenSSL license (the "License").  You may not use
# this file except in compliance with the License.

# /* ====================================================================
#  * Copyright (c) 1998-2017 The OpenSSL Project.  All rights reserved.
#  *
#  * Redistribution and use in source and binary forms, with or without
#  * modification, are permitted provided that the following conditions
#  * are met:
#  *
#  * 1. Redistributions of source code must retain the above copyright
#  *    notice, this list of conditions and the following disclaimer. 
#  *
#  * 2. Redistributions in binary form must reproduce the above copyright
#  *    notice, this list of conditions and the following disclaimer in
#  *    the documentation and/or other materials provided with the
#  *    distribution.
#  *
#  * 3. All advertising materials mentioning features or use of this
#  *    software must display the following acknowledgment:
#  *    "This product includes software developed by the OpenSSL Project
#  *    for use in the OpenSSL Toolkit. (http://www.openssl.org/)"
#  *
#  * 4. The names "OpenSSL Toolkit" and "OpenSSL Project" must not be used to
#  *    endorse or promote products derived from this software without
#  *    prior written permission. For written permission, please contact
#  *    openssl-core@openssl.org.
#  *
#  * 5. Products derived from this software may not be called "OpenSSL"
#  *    nor may "OpenSSL" appear in their names without prior written
#  *    permission of the OpenSSL Project.
#  *
#  * 6. Redistributions of any form whatsoever must retain the following
#  *    acknowledgment:
#  *    "This product includes software developed by the OpenSSL Project
#  *    for use in the OpenSSL Toolkit (http://www.openssl.org/)"
#  *
#  * THIS SOFTWARE IS PROVIDED BY THE OpenSSL PROJECT ``AS IS'' AND ANY
#  * EXPRESSED OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
#  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
#  * PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE OpenSSL PROJECT OR
#  * ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
#  * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
#  * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
#  * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
#  * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
#  * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
#  * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
#  * OF THE POSSIBILITY OF SUCH DAMAGE.
#  * ====================================================================
#  *
#  * This product includes cryptographic software written by Eric Young
#  * (eay@cryptsoft.com).  This product includes software written by Tim
#  * Hudson (tjh@cryptsoft.com).
#  *
#  */
# 
#  Original SSLeay License
#  -----------------------
# 
# /* Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com)
#  * All rights reserved.
#  *
#  * This package is an SSL implementation written
#  * by Eric Young (eay@cryptsoft.com).
#  * The implementation was written so as to conform with Netscapes SSL.
#  * 
#  * This library is free for commercial and non-commercial use as long as
#  * the following conditions are aheared to.  The following conditions
#  * apply to all code found in this distribution, be it the RC4, RSA,
#  * lhash, DES, etc., code; not just the SSL code.  The SSL documentation
#  * included with this distribution is covered by the same copyright terms
#  * except that the holder is Tim Hudson (tjh@cryptsoft.com).
#  * 
#  * Copyright remains Eric Young's, and as such any Copyright notices in
#  * the code are not to be removed.
#  * If this package is used in a product, Eric Young should be given attribution
#  * as the author of the parts of the library used.
#  * This can be in the form of a textual message at program startup or
#  * in documentation (online or textual) provided with the package.
#  * 
#  * Redistribution and use in source and binary forms, with or without
#  * modification, are permitted provided that the following conditions
#  * are met:
#  * 1. Redistributions of source code must retain the copyright
#  *    notice, this list of conditions and the following disclaimer.
#  * 2. Redistributions in binary form must reproduce the above copyright
#  *    notice, this list of conditions and the following disclaimer in the
#  *    documentation and/or other materials provided with the distribution.
#  * 3. All advertising materials mentioning features or use of this software
#  *    must display the following acknowledgement:
#  *    "This product includes cryptographic software written by
#  *     Eric Young (eay@cryptsoft.com)"
#  *    The word 'cryptographic' can be left out if the rouines from the library
#  *    being used are not cryptographic related :-).
#  * 4. If you include any Windows specific code (or a derivative thereof) from 
#  *    the apps directory (application code) you must include an acknowledgement:
#  *    "This product includes software written by Tim Hudson (tjh@cryptsoft.com)"
#  * 
#  * THIS SOFTWARE IS PROVIDED BY ERIC YOUNG ``AS IS'' AND
#  * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
#  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
#  * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
#  * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
#  * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
#  * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
#  * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
#  * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
#  * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
#  * SUCH DAMAGE.
#  * 
#  * The licence and distribution terms for any publically available version or
#  * derivative of this code cannot be changed.  i.e. this code cannot simply be
#  * copied and put under another distribution licence
#  * [including the GNU Public Licence.]
#  */

$flavour = shift;
$output  = shift;
if ($flavour =~ /\./) { $output = $flavour; undef $flavour; }

$win64=0; $win64=1 if ($flavour =~ /[nm]asm|mingw64/ || $output =~ /\.asm$/);

$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
( $xlate="${dir}x86_64-xlate.pl" and -f $xlate ) or
( $xlate="${dir}perlasm/x86_64-xlate.pl" and -f $xlate) or
die "can't locate x86_64-xlate.pl";

open OUT,"| \"$^X\" \"$xlate\" $flavour \"$output\"";
*STDOUT=*OUT;

($arg1,$arg2,$arg3,$arg4)=$win64?("%rcx","%rdx","%r8", "%r9") :	# Win64 order
				 ("%rdi","%rsi","%rdx","%rcx");	# Unix order

print<<___;
.extern		OPENSSL_cpuid_setup
.hidden		OPENSSL_cpuid_setup
.section	.init
	call	OPENSSL_cpuid_setup

.hidden	OPENSSL_ia32cap_P
.comm	OPENSSL_ia32cap_P,16,4

.text

.globl	OPENSSL_atomic_add
.type	OPENSSL_atomic_add,\@abi-omnipotent
.align	16
OPENSSL_atomic_add:
	movl	($arg1),%eax
.Lspin:	leaq	($arg2,%rax),%r8
	.byte	0xf0		# lock
	cmpxchgl	%r8d,($arg1)
	jne	.Lspin
	movl	%r8d,%eax
	.byte	0x48,0x98	# cltq/cdqe
	ret
.size	OPENSSL_atomic_add,.-OPENSSL_atomic_add

.globl	OPENSSL_rdtsc
.type	OPENSSL_rdtsc,\@abi-omnipotent
.align	16
OPENSSL_rdtsc:
	rdtsc
	shl	\$32,%rdx
	or	%rdx,%rax
	ret
.size	OPENSSL_rdtsc,.-OPENSSL_rdtsc

.globl	OPENSSL_ia32_cpuid
.type	OPENSSL_ia32_cpuid,\@function,1
.align	16
OPENSSL_ia32_cpuid:
.cfi_startproc
	mov	%rbx,%r8		# save %rbx
.cfi_register	%rbx,%r8

	xor	%eax,%eax
	mov	%eax,8(%rdi)		# clear extended feature flags
	cpuid
	mov	%eax,%r11d		# max value for standard query level

	xor	%eax,%eax
	cmp	\$0x756e6547,%ebx	# "Genu"
	setne	%al
	mov	%eax,%r9d
	cmp	\$0x49656e69,%edx	# "ineI"
	setne	%al
	or	%eax,%r9d
	cmp	\$0x6c65746e,%ecx	# "ntel"
	setne	%al
	or	%eax,%r9d		# 0 indicates Intel CPU
	jz	.Lintel

	cmp	\$0x68747541,%ebx	# "Auth"
	setne	%al
	mov	%eax,%r10d
	cmp	\$0x69746E65,%edx	# "enti"
	setne	%al
	or	%eax,%r10d
	cmp	\$0x444D4163,%ecx	# "cAMD"
	setne	%al
	or	%eax,%r10d		# 0 indicates AMD CPU
	jnz	.Lintel

	# AMD specific
	mov	\$0x80000000,%eax
	cpuid
	cmp	\$0x80000001,%eax
	jb	.Lintel
	mov	%eax,%r10d
	mov	\$0x80000001,%eax
	cpuid
	or	%ecx,%r9d
	and	\$0x00000801,%r9d	# isolate AMD XOP bit, 1<<11

	cmp	\$0x80000008,%r10d
	jb	.Lintel

	mov	\$0x80000008,%eax
	cpuid
	movzb	%cl,%r10		# number of cores - 1
	inc	%r10			# number of cores

	mov	\$1,%eax
	cpuid
	bt	\$28,%edx		# test hyper-threading bit
	jnc	.Lgeneric
	shr	\$16,%ebx		# number of logical processors
	cmp	%r10b,%bl
	ja	.Lgeneric
	and	\$0xefffffff,%edx	# ~(1<<28)
	jmp	.Lgeneric

.Lintel:
	cmp	\$4,%r11d
	mov	\$-1,%r10d
	jb	.Lnocacheinfo

	mov	\$4,%eax
	mov	\$0,%ecx		# query L1D
	cpuid
	mov	%eax,%r10d
	shr	\$14,%r10d
	and	\$0xfff,%r10d		# number of cores -1 per L1D

.Lnocacheinfo:
	mov	\$1,%eax
	cpuid
	and	\$0xbfefffff,%edx	# force reserved bits to 0
	cmp	\$0,%r9d
	jne	.Lnotintel
	or	\$0x40000000,%edx	# set reserved bit#30 on Intel CPUs
	and	\$15,%ah
	cmp	\$15,%ah		# examine Family ID
	jne	.Lnotintel
	or	\$0x00100000,%edx	# set reserved bit#20 to engage RC4_CHAR
.Lnotintel:
	bt	\$28,%edx		# test hyper-threading bit
	jnc	.Lgeneric
	and	\$0xefffffff,%edx	# ~(1<<28)
	cmp	\$0,%r10d
	je	.Lgeneric

	or	\$0x10000000,%edx	# 1<<28
	shr	\$16,%ebx
	cmp	\$1,%bl			# see if cache is shared
	ja	.Lgeneric
	and	\$0xefffffff,%edx	# ~(1<<28)
.Lgeneric:
	and	\$0x00000800,%r9d	# isolate AMD XOP flag
	and	\$0xfffff7ff,%ecx
	or	%ecx,%r9d		# merge AMD XOP flag

	mov	%edx,%r10d		# %r9d:%r10d is copy of %ecx:%edx

	cmp	\$7,%r11d
	jb	.Lno_extended_info
	mov	\$7,%eax
	xor	%ecx,%ecx
	cpuid
	mov	%ebx,8(%rdi)		# save extended feature flags
.Lno_extended_info:

	bt	\$27,%r9d		# check OSXSAVE bit
	jnc	.Lclear_avx
	xor	%ecx,%ecx		# XCR0
	.byte	0x0f,0x01,0xd0		# xgetbv
	and	\$0xe6,%eax		# isolate XMM, YMM and ZMM state support
	cmp	\$0xe6,%eax
	je	.Ldone
	andl	\$0xfffeffff,8(%rdi)	# clear AVX512F, ~(1<<16)
					# note that we don't touch other AVX512
					# extensions, because they can be used
					# with YMM (without opmasking though)
	and	\$6,%eax		# isolate XMM and YMM state support
	cmp	\$6,%eax
	je	.Ldone
.Lclear_avx:
	mov	\$0xefffe7ff,%eax	# ~(1<<28|1<<12|1<<11)
	and	%eax,%r9d		# clear AVX, FMA and AMD XOP bits
	mov	\$0x3fdeffdf,%eax	# ~(1<<31|1<<30|1<<21|1<<16|1<<5)
	and	%eax,8(%rdi)		# cleax AVX2 and AVX512* bits
.Ldone:
	shl	\$32,%r9
	mov	%r10d,%eax
	mov	%r8,%rbx		# restore %rbx
.cfi_restore	%rbx
	or	%r9,%rax
	ret
.cfi_endproc
.size	OPENSSL_ia32_cpuid,.-OPENSSL_ia32_cpuid

.globl  OPENSSL_cleanse
.type   OPENSSL_cleanse,\@abi-omnipotent
.align  16
OPENSSL_cleanse:
	xor	%rax,%rax
	cmp	\$15,$arg2
	jae	.Lot
	cmp	\$0,$arg2
	je	.Lret
.Little:
	mov	%al,($arg1)
	sub	\$1,$arg2
	lea	1($arg1),$arg1
	jnz	.Little
.Lret:
	ret
.align	16
.Lot:
	test	\$7,$arg1
	jz	.Laligned
	mov	%al,($arg1)
	lea	-1($arg2),$arg2
	lea	1($arg1),$arg1
	jmp	.Lot
.Laligned:
	mov	%rax,($arg1)
	lea	-8($arg2),$arg2
	test	\$-8,$arg2
	lea	8($arg1),$arg1
	jnz	.Laligned
	cmp	\$0,$arg2
	jne	.Little
	ret
.size	OPENSSL_cleanse,.-OPENSSL_cleanse

.globl  CRYPTO_memcmp
.type   CRYPTO_memcmp,\@abi-omnipotent
.align  16
CRYPTO_memcmp:
	xor	%rax,%rax
	xor	%r10,%r10
	cmp	\$0,$arg3
	je	.Lno_data
.Loop_cmp:
	mov	($arg1),%r10b
	lea	1($arg1),$arg1
	xor	($arg2),%r10b
	lea	1($arg2),$arg2
	or	%r10b,%al
	dec	$arg3
	jnz	.Loop_cmp
	neg	%rax
	shr	\$63,%rax
.Lno_data:
	ret
.size	CRYPTO_memcmp,.-CRYPTO_memcmp
___

print<<___ if (!$win64);
.globl	OPENSSL_wipe_cpu
.type	OPENSSL_wipe_cpu,\@abi-omnipotent
.align	16
OPENSSL_wipe_cpu:
	pxor	%xmm0,%xmm0
	pxor	%xmm1,%xmm1
	pxor	%xmm2,%xmm2
	pxor	%xmm3,%xmm3
	pxor	%xmm4,%xmm4
	pxor	%xmm5,%xmm5
	pxor	%xmm6,%xmm6
	pxor	%xmm7,%xmm7
	pxor	%xmm8,%xmm8
	pxor	%xmm9,%xmm9
	pxor	%xmm10,%xmm10
	pxor	%xmm11,%xmm11
	pxor	%xmm12,%xmm12
	pxor	%xmm13,%xmm13
	pxor	%xmm14,%xmm14
	pxor	%xmm15,%xmm15
	xorq	%rcx,%rcx
	xorq	%rdx,%rdx
	xorq	%rsi,%rsi
	xorq	%rdi,%rdi
	xorq	%r8,%r8
	xorq	%r9,%r9
	xorq	%r10,%r10
	xorq	%r11,%r11
	leaq	8(%rsp),%rax
	ret
.size	OPENSSL_wipe_cpu,.-OPENSSL_wipe_cpu
___
print<<___ if ($win64);
.globl	OPENSSL_wipe_cpu
.type	OPENSSL_wipe_cpu,\@abi-omnipotent
.align	16
OPENSSL_wipe_cpu:
	pxor	%xmm0,%xmm0
	pxor	%xmm1,%xmm1
	pxor	%xmm2,%xmm2
	pxor	%xmm3,%xmm3
	pxor	%xmm4,%xmm4
	pxor	%xmm5,%xmm5
	xorq	%rcx,%rcx
	xorq	%rdx,%rdx
	xorq	%r8,%r8
	xorq	%r9,%r9
	xorq	%r10,%r10
	xorq	%r11,%r11
	leaq	8(%rsp),%rax
	ret
.size	OPENSSL_wipe_cpu,.-OPENSSL_wipe_cpu
___
{
my $out="%r10";
my $cnt="%rcx";
my $max="%r11";
my $lasttick="%r8d";
my $lastdiff="%r9d";
my $redzone=win64?8:-8;

print<<___;
.globl	OPENSSL_instrument_bus
.type	OPENSSL_instrument_bus,\@abi-omnipotent
.align	16
OPENSSL_instrument_bus:
	mov	$arg1,$out	# tribute to Win64
	mov	$arg2,$cnt
	mov	$arg2,$max

	rdtsc			# collect 1st tick
	mov	%eax,$lasttick	# lasttick = tick
	mov	\$0,$lastdiff	# lastdiff = 0
	clflush	($out)
	.byte	0xf0		# lock
	add	$lastdiff,($out)
	jmp	.Loop
.align	16
.Loop:	rdtsc
	mov	%eax,%edx
	sub	$lasttick,%eax
	mov	%edx,$lasttick
	mov	%eax,$lastdiff
	clflush	($out)
	.byte	0xf0		# lock
	add	%eax,($out)
	lea	4($out),$out
	sub	\$1,$cnt
	jnz	.Loop

	mov	$max,%rax
	ret
.size	OPENSSL_instrument_bus,.-OPENSSL_instrument_bus

.globl	OPENSSL_instrument_bus2
.type	OPENSSL_instrument_bus2,\@abi-omnipotent
.align	16
OPENSSL_instrument_bus2:
	mov	$arg1,$out	# tribute to Win64
	mov	$arg2,$cnt
	mov	$arg3,$max
	mov	$cnt,$redzone(%rsp)

	rdtsc			# collect 1st tick
	mov	%eax,$lasttick	# lasttick = tick
	mov	\$0,$lastdiff	# lastdiff = 0

	clflush	($out)
	.byte	0xf0		# lock
	add	$lastdiff,($out)

	rdtsc			# collect 1st diff
	mov	%eax,%edx
	sub	$lasttick,%eax	# diff
	mov	%edx,$lasttick	# lasttick = tick
	mov	%eax,$lastdiff	# lastdiff = diff
.Loop2:
	clflush	($out)
	.byte	0xf0		# lock
	add	%eax,($out)	# accumulate diff

	sub	\$1,$max
	jz	.Ldone2

	rdtsc
	mov	%eax,%edx
	sub	$lasttick,%eax	# diff
	mov	%edx,$lasttick	# lasttick = tick
	cmp	$lastdiff,%eax
	mov	%eax,$lastdiff	# lastdiff = diff
	mov	\$0,%edx
	setne	%dl
	sub	%rdx,$cnt	# conditional --$cnt
	lea	($out,%rdx,4),$out	# conditional ++$out
	jnz	.Loop2

.Ldone2:
	mov	$redzone(%rsp),%rax
	sub	$cnt,%rax
	ret
.size	OPENSSL_instrument_bus2,.-OPENSSL_instrument_bus2
___
}

sub gen_random {
my $rdop = shift;
print<<___;
.globl	OPENSSL_ia32_${rdop}
.type	OPENSSL_ia32_${rdop},\@abi-omnipotent
.align	16
OPENSSL_ia32_${rdop}:
	mov	\$8,%ecx
.Loop_${rdop}:
	${rdop}	%rax
	jc	.Lbreak_${rdop}
	loop	.Loop_${rdop}
.Lbreak_${rdop}:
	cmp	\$0,%rax
	cmove	%rcx,%rax
	ret
.size	OPENSSL_ia32_${rdop},.-OPENSSL_ia32_${rdop}

.globl	OPENSSL_ia32_${rdop}_bytes
.type	OPENSSL_ia32_${rdop}_bytes,\@abi-omnipotent
.align	16
OPENSSL_ia32_${rdop}_bytes:
	xor	%rax, %rax	# return value
	cmp	\$0,$arg2
	je	.Ldone_${rdop}_bytes

	mov	\$8,%r11
.Loop_${rdop}_bytes:
	${rdop}	%r10
	jc	.Lbreak_${rdop}_bytes
	dec	%r11
	jnz	.Loop_${rdop}_bytes
	jmp	.Ldone_${rdop}_bytes

.align	16
.Lbreak_${rdop}_bytes:
	cmp	\$8,$arg2
	jb	.Ltail_${rdop}_bytes
	mov	%r10,($arg1)
	lea	8($arg1),$arg1
	add	\$8,%rax
	sub	\$8,$arg2
	jz	.Ldone_${rdop}_bytes
	mov	\$8,%r11
	jmp	.Loop_${rdop}_bytes

.align	16
.Ltail_${rdop}_bytes:
	mov	%r10b,($arg1)
	lea	1($arg1),$arg1
	inc	%rax
	shr	\$8,%r8
	dec	$arg2
	jnz	.Ltail_${rdop}_bytes

.Ldone_${rdop}_bytes:
	ret
.size	OPENSSL_ia32_${rdop}_bytes,.-OPENSSL_ia32_${rdop}_bytes
___
}
gen_random("rdrand");
gen_random("rdseed");

close STDOUT;	# flush
