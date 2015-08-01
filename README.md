THE SOFTWARE IS PROVIDED "AS IS" AND BRIAN SMITH AND THE AUTHORS DISCLAIM
ALL WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES
OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL BRIAN SMITH OR THE AUTHORS
BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY
DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN
AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.



What is *ring*?
===============

*ring* is a simplified version of BoringSSL that has the following features
removed:

* TLS (libssl)
* X.509 (crypto/pem, crypto/x509, crypto/x509v3)
* ASN.1 (crypto/asn1 and crypto/obj)

*ring* makes OpenSSL's high-quality, high-performance crypto primitives
conveniently available to new crypto libraries written in safer (than C)
languages like OCaml and Rust. Particular attention is being paid to making it
easy to build and integrate *ring* into applications and higher-level
frameworks, and to ensuring that *ring* works optimally on microcontrollers
to support Internet of Things (IoT) applications. It may also be useful for
people implementing cryptographic protocols in C and C++.

The name *ring* comes from the fact that *ring* started as a subset of
BoringSSL, and *"ring"* is a substring of "Bo*ring*SSL". Almost all the code in
*ring* comes from BoringSSL, and BoringSSL is derived from OpenSSL. In general
an application that uses the subset of BoringSSL APIs that *ring* supports
should work identically if it is recompiled and relinked with BoringSSL
instead. *ring* tracks upstream changes to BoringSSL. Several patches that
were developed for *ring* have already been integrated upstream in BoringSSL.



Warning: The ```wip``` Branch Gets Rebased Frequently
=====================================================

The default branch on GitHub for this project is the ```wip``` branch. This
branch is getting rebased regularly as I clean up the initial set of patches
for *ring*. Once that cleanup is done, I will create a ```master``` branch that
I intend to never rebase, and then I will delete the ```wip``` branch.



Building
========

See [BUILDING.md](BUILDING.md) for instructions on how to build *ring* and
incorporate it into your project.



Contributing
============

Patches Welcome! Suggestions:

* Better IDE support for Windows (e.g. running the tests within the IDE) and
  Mac OS X (e.g. Xcode project files).
* Language bindings for safer programming languages like Haskell, OCaml, and
  Rust.
* Support for more platforms in the continuous integration, such as Android,
  Mac OS X, and ARM microcontrollers. (The current CI only covers Linux.)
* Static analysis and fuzzing in the continuous integration.
* More code elimination, especially dead code.



License
=======

See [LICENSE](LICENSE). The *ring* project happily accepts pull requests
without any copyright license agreement. The portions of pull requests that
modify existing files should be licensed under the same terms as the files
being modified. New files in pull requests should be licensed under the
ISC-style license. If your patch is useful for BoringSSL then it would be very
nice of you to also submit it to them after agreeing to their copyright license
agreement.



Continuous Integration
======================

*ring* uses Travis CI to test builds in a variety of configurations on Linux:

[![Build Status](https://travis-ci.org/briansmith/ring.svg?branch=wip)](https://travis-ci.org/briansmith/ring)



Bug Reporting
=============

Please file bugs in the
[issue tracker](https://github.com/briansmith/ring/issues). If you think you've
found a security vulnerability that affects BoringSSL and/or OpenSSL then those
projects would probably appreciate it if you report the bug privately to them.
The *ring* project is happy to take *any* kind of bug report as a pull request
that fixes it and/or adds a test for the issue, or as an issue filed in the
public issue tracker. **Do NOT report any security vulnerability privately to
the *ring* developers.**
