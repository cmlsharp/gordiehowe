// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: domain H of v7 mdoc (mdoc_hash.h) on Longfellow's mdoc
// test vectors, with 1, 2 and 4 requested attributes: honest proofs verify,
// and a wrong attribute value, a wrong window offset, a wrong block count,
// an expired date, a tampered MSO byte (outside and inside a window) and a
// repeated attribute are rejected.
//
// mdoc_hash_bench (mdoc_hash_bench.cc) measures domain H alone.

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

#include "gordiehowe/examples/mdoc/mdoc_hash_fixture.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe::examples::mdoc::testing {
namespace {

// Whether the proof of witness data D against STATEMENT verifies (the
// prover does not require D to satisfy the system).
bool accepts(const Compiled &x, const Assignment &statement,
             const examples::mdoc::MdocHashData &d) {
  auto prep = x.c->prepare(statement);
  Sys::ProveOptions opt;
  opt.require_satisfied = false;
  SecureRandomEngine rng;
  return prep.verify(prep.prove(x.sys->witness(d), rng, opt));
}

void expect_honest(const Case &c) {
  const Witness w = witness_of(c);
  Compiled &x = compiled(c.attrs.size());
  auto prep = x.c->prepare(x.sys->statement(c, w));
  SecureRandomEngine rng;
  const auto proof = prep.prove(x.sys->witness(w.data), rng);
  EXPECT_TRUE(prep.verify(proof))
      << "doc " << c.doc << ", " << c.attrs.size() << " attributes";
}

TEST(MdocHash, HonestDoc0OneAttribute) { expect_honest(bench_case(0, 1)); }
TEST(MdocHash, HonestDoc3OneAttribute) { expect_honest(bench_case(3, 1)); }
TEST(MdocHash, HonestDoc3TwoAttributes) { expect_honest(bench_case(3, 2)); }
TEST(MdocHash, HonestDoc3FourAttributes) { expect_honest(bench_case(3, 4)); }

// Each change to an honest doc-3 instance with two attributes is rejected.
TEST(MdocHash, Rejections) {
  const Case c = bench_case(3, 2);
  const Witness w = witness_of(c);
  Compiled &x = compiled(2);
  const Assignment st = x.sys->statement(c, w);
  EXPECT_TRUE(accepts(x, st, w.data)) << "honest, through the hook";

  // A wrong attribute value: family_name "Mustermanm".
  {
    Case c2 = c;
    c2.attrs[1].cbor_value[c2.attrs[1].cbor_value_len - 1] = 'm';
    EXPECT_FALSE(accepts(x, x.sys->statement(c2, w), w.data))
        << "attribute value";
  }
  // A wrong offset: validFrom one byte later.
  {
    auto d = w.data;
    d.offsets[0] += 1;
    EXPECT_FALSE(accepts(x, st, d)) << "offset";
  }
  // A wrong attribute-digest offset.
  {
    auto d = w.data;
    d.offsets[examples::mdoc::kFixedWindows + 1] += 2;
    EXPECT_FALSE(accepts(x, st, d)) << "digest offset";
  }
  // A wrong block count: the length one block longer.
  {
    auto d = w.data;
    d.length += 64;
    EXPECT_FALSE(accepts(x, st, d)) << "block count";
  }
  // An expired document: now after validUntil.
  {
    const uint8_t late[] = "2099-01-01T00:00:00Z";
    EXPECT_FALSE(accepts(x, x.sys->statement(c, w, late), w.data))
        << "expired";
  }
  // Not yet valid: now before validFrom.
  {
    const uint8_t early[] = "2000-01-01T00:00:00Z";
    EXPECT_FALSE(accepts(x, x.sys->statement(c, w, early), w.data))
        << "not yet valid";
  }
  // A tampered MSO byte outside every window: the digest changes, and the
  // signed digest no longer matches.
  {
    const size_t at =
        examples::mdoc::kPrefixBytes + examples::mdoc::kWindowFirst + 40;
    auto d = w.data;
    d.buffer[at] ^= 0x01;
    EXPECT_FALSE(accepts(x, st, d)) << "MSO byte";
  }
  // A tampered MSO byte inside the deviceKeyInfo key, against the digest
  // of the tampered MSO: only the window rejects it.
  {
    auto d = w.data;
    const size_t at = examples::mdoc::kPrefixBytes +
                      examples::mdoc::kWindowFirst + d.offsets[2] + 3;
    d.buffer[at] ^= 0x20;
    Witness w2 = w;
    SHA256 h;
    h.Update(d.buffer.data(), d.length);
    h.DigestData(w2.e.data());
    EXPECT_FALSE(accepts(x, x.sys->statement(c, w2), d)) << "window byte";
  }
  // A tampered item byte (its digest no longer in the MSO).
  {
    auto d = w.data;
    d.items[0].bytes[20] ^= 0x01;
    EXPECT_FALSE(accepts(x, st, d)) << "item byte";
  }
}

// One attribute requested twice: the two digest windows coincide, and
// disjoint windows reject it.
TEST(MdocHash, RepeatedAttributeRejected) {
  Case c = bench_case(3, 1);
  c.attrs.push_back(c.attrs[0]);
  const Witness w = witness_of(c);
  Compiled &x = compiled(2);
  EXPECT_FALSE(accepts(x, x.sys->statement(c, w), w.data));
}

}  // namespace
}  // namespace proofs::gordiehowe::examples::mdoc::testing
