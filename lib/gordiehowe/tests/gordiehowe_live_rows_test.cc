// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the masked skip's prover over its live rows (field_skip.h,
// batch.h, bit_skip.h, sumcheck/boolean_skip.h) against the prover over all
// 2^logs rows (the full_rows test switch): the proofs are equal field
// element for field element, with the masking pads, sequentially and with
// the kernels' chunks on a fork-join pool (threads.h), and the terminal
// check row holds on the pads. Every first-round kernel: field operands
// (Q of degree 1, 2, 3 and 5, each sum path of MaskedFieldSkip), the
// bit-sliced chi kernel and the bit-sliced kernel of a runtime relation;
// in characteristic 2 and in odd characteristic; at live row counts that
// are odd and not a power of two, a power of two (no padding) and one.

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "algebra/fp_goldilocks4.h"
#include "gf2k/gf2_128.h"
#include "gordiehowe/compiler/batch.h"
#include "gordiehowe/compiler/bit_skip.h"
#include "gordiehowe/compiler/field_skip.h"
#include "gordiehowe/threads.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/boolean_skip.h"
#include "util/crypto.h"
#include "util/parallel.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

using compiler::FieldRelation;
using compiler::MaskedFieldSkip;
using compiler::SkipOperands;

// Restores the full_rows test switch on scope exit.
class FullRows {
 public:
  explicit FullRows(bool on) : prev_(compiler::test_switches().full_rows) {
    compiler::test_switches().full_rows = on;
  }
  ~FullRows() { compiler::test_switches().full_rows = prev_; }

 private:
  bool prev_;
};

// Proves OPS on SK with PADS from a fixed transcript: over all rows or the
// live rows, sequentially or on a pool of three workers.
template <class F>
typename MaskedFieldSkip<F>::Proof prove(const MaskedFieldSkip<F> &sk,
                                         const SkipOperands<F> &ops,
                                         const std::vector<typename F::Elt> &pads,
                                         bool full, bool pool) {
  static const uint8_t kLabel[] = "live-rows";
  BasicProofSeed<SHA256> seed;
  std::memset(seed.bytes, 0, sizeof(seed.bytes));
  BasicTranscript<SHA256> ts(kLabel, sizeof(kLabel) - 1, seed);
  const FullRows fr(full);
  if (!pool) return sk.prove(ops, ts, pads.data());
  internal::TaskPool tp(3);
  const parallel::Scope scope(&tp);
  return sk.prove(ops, ts, pads.data());
}

// The four proofs of OPS (full or live rows, sequential or pooled) are the
// same; the terminal check row holds on the pads. LIVE is the live rows
// the batch should have.
template <class F>
void expect_live_rows_match(const F &f, const MaskedFieldSkip<F> &sk,
                            const SkipOperands<F> &ops, size_t live,
                            const std::string &what) {
  EXPECT_EQ(sk.live_rows(), live) << what;
  std::vector<typename F::Elt> pads(sk.layout.count);
  SecureRandomEngine rng;
  sk.fill_pads(pads.data(), rng);
  const auto want = prove(sk, ops, pads, true, false);
  for (const bool full : {true, false})
    for (const bool pool : {false, true}) {
      const auto got = prove(sk, ops, pads, full, pool);
      const std::string at = what + (full ? ", full rows" : ", live rows") +
                             (pool ? ", pooled" : ", sequential");
      EXPECT_EQ(got.skip, want.skip) << at;
      EXPECT_EQ(got.rounds, want.rounds) << at;
      EXPECT_EQ(got.terminal, want.terminal) << at;
    }
  // The verifier's terminal check row on the live-row proof.
  static const uint8_t kLabel[] = "live-rows";
  BasicProofSeed<SHA256> seed;
  std::memset(seed.bytes, 0, sizeof(seed.bytes));
  BasicTranscript<SHA256> tv(kLabel, sizeof(kLabel) - 1, seed);
  const auto ctx = sk.rows_of(prove(sk, ops, pads, false, true), tv, 0);
  ASSERT_EQ(ctx.b.size(), 1u) << what;
  typename F::Elt lhs = f.zero();
  for (const auto &t : ctx.a) f.add(lhs, f.mulf(t.k, pads[t.w]));
  EXPECT_EQ(lhs, ctx.b[0]) << what;
}

// Field operands of Q at degree D, satisfied by every instance: Q =
// x0^D - x1 (D = 1, 5), x0 x1 + x2 (D = 2), x0 x1 x2 - x3 (D = 3).
template <class F>
void field_case(const F &f, unsigned degree, unsigned width, size_t live) {
  using E = typename F::Elt;
  FieldRelation<F> rel;
  rel.name = "degree-" + std::to_string(degree);
  if (degree == 2) {
    rel.operands = 3;
    rel.monomials = {{f.one(), {0, 1}}, {f.one(), {2}}};
  } else if (degree == 3) {
    rel.operands = 4;
    rel.monomials = {{f.one(), {0, 1, 2}}, {f.mone(), {3}}};
  } else {
    rel.operands = 2;
    rel.monomials = {{f.one(), std::vector<unsigned>(degree, 0)},
                     {f.mone(), {1}}};
  }
  // The last live row partly filled when the width allows it.
  const size_t instances = live * width - (width > 1 && live > 0 ? 1 : 0);
  std::mt19937_64 g(degree * 1000 + width * 10 + live);
  std::vector<std::vector<E>> ops(instances);
  for (auto &o : ops) {
    for (unsigned j = 0; j + 1 < rel.operands; ++j)
      o.push_back(f.of_scalar(g() & 0xffff));
    E last = f.zero();
    if (degree == 2) last = f.negf(f.mulf(o[0], o[1]));
    if (degree == 3) last = f.mulf(f.mulf(o[0], o[1]), o[2]);
    if (degree != 2 && degree != 3) {
      last = f.one();
      for (unsigned d = 0; d < degree; ++d) f.mul(last, o[0]);
    }
    o.push_back(last);
  }
  const MaskedFieldSkip<F> sk(f, rel, instances, width);
  const compiler::FieldSkipOperands<F> first(ops);
  expect_live_rows_match(f, sk, first, live,
                         "field, degree " + std::to_string(degree) +
                             ", width " + std::to_string(width) + ", live " +
                             std::to_string(live));
}

TEST(GordieHoweLiveRows, FieldOperandsBinary) {
  const GF2_128<> f;
  for (unsigned degree : {1u, 2u, 3u, 5u})
    for (unsigned width : {1u, 4u, 16u})
      for (size_t live : {21u, 13u, 32u, 1u}) {
        // The skip points must fit the 8-bit skip subfield.
        if (degree * (width - 1) + 1 > 256) continue;
        field_case(f, degree, width, live);
      }
}

TEST(GordieHoweLiveRows, FieldOperandsOdd) {
  const Fp64G4 f;
  for (unsigned degree : {1u, 2u, 3u, 5u})
    for (unsigned width : {1u, 3u, 4u})
      for (size_t live : {21u, 13u, 32u, 1u}) field_case(f, degree, width, live);
}

// The bit-sliced chi kernel (BasicBooleanSkip<F, SkipChi>): LANES lanes of
// c = a & b, 64 / width rows each.
TEST(GordieHoweLiveRows, BitChi) {
  using F = GF2_128<>;
  const F f;
  FieldRelation<F> rel{"chi", 3, {{f.one(), {0, 1}}, {f.one(), {2}}}};
  for (unsigned width : {1u, 16u, 64u})
    for (size_t lanes : {21u, 5u, 8u, 1u}) {
      std::mt19937_64 g(width * 100 + lanes);
      std::vector<SkipWord> in(lanes);
      for (auto &x : in) {
        x.a = g();
        x.b = g();
        x.c = x.a & x.b;
      }
      const BasicBooleanSkip<F, SkipChi> skip(f, width);
      const MaskedFieldSkip<F> sk(f, rel, lanes * 64, width);
      const compiler::BitSkipOperands<F, SkipChi> first(skip, skip.rows(in));
      expect_live_rows_match(f, sk, first, lanes * (64 / width),
                             "chi, width " + std::to_string(width) +
                                 ", lanes " + std::to_string(lanes));
    }
}

// The bit-sliced kernel of a runtime relation (RuntimeBooleanSkip):
// a b c + d over four operands, d = a & b & c.
TEST(GordieHoweLiveRows, BitRuntime) {
  using F = GF2_128<>;
  const F f;
  FieldRelation<F> rel{"abc+d", 4, {{f.one(), {0, 1, 2}}, {f.one(), {3}}}};
  for (unsigned width : {1u, 16u, 64u})
    for (size_t lanes : {21u, 5u, 8u, 1u}) {
      std::mt19937_64 g(width * 100 + lanes);
      std::vector<uint64_t> in(lanes * 4);
      for (size_t l = 0; l < lanes; ++l) {
        in[4 * l] = g();
        in[4 * l + 1] = g();
        in[4 * l + 2] = g();
        in[4 * l + 3] = in[4 * l] & in[4 * l + 1] & in[4 * l + 2];
      }
      const compiler::RuntimeBooleanSkip<F> skip(
          f, 4, {{0, 1, 2}, {3}}, width);
      const MaskedFieldSkip<F> sk(f, rel, lanes * 64, width);
      size_t n = 0;
      auto rows = skip.rows(in, n);
      const compiler::RuntimeBitSkipOperands<F> first(skip, std::move(rows),
                                                      n);
      expect_live_rows_match(f, sk, first, lanes * (64 / width),
                             "runtime, width " + std::to_string(width) +
                                 ", lanes " + std::to_string(lanes));
    }
}

}  // namespace
}  // namespace proofs::gordiehowe
