// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: ML-DSA's SampleInBall (FIPS 204 Algorithm 29) in a binary
// domain H, as two gadgets:
//
//   sample_in_ball_select   the rejection sampling: the t-th selected byte
//                           j_t is at most 256 - tau + t, by lib/select.h's
//                           select_first with a rising-threshold scan
//   sample_in_ball_shuffle  the Fisher-Yates swaps as one offline memory
//                           check (lib/permutation.h); the cells hold 0, 1
//                           and theta (of order 3 in GF(2^16)) for the
//                           coefficients 0, +1 and -1
//
// sample_in_ball runs both and returns the (support, sign) bits. The host
// trace is in sample_in_ball_witness.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_SAMPLE_IN_BALL_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_SAMPLE_IN_BALL_H_

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <string>
#include <tuple>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/examples/mldsa/sample_in_ball_witness.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::examples {

// theta of order 3 in GF(2^16): g^21845 for g of order 2^16 - 1. The
// cells hold 0, 1 and theta for the coefficients 0, +1 and -1.
template <class F>
typename F::Elt sample_in_ball_theta(const F &f) {
  auto g = lib::select::subfield_generator(f);
  typename F::Elt r = f.one();
  for (uint64_t e = 21845; e; e >>= 1) {
    if (e & 1) r = f.mulf(r, g);
    g = f.mulf(g, g);
  }
  return r;
}

// SampleInBallScan(tau): the threshold scan of SelectFirstTau. THRESHOLD
// holds each sample's low L committed bits; the decoded thresholds THR
// ([S, 8]) add the high bits, the OR of low bits [h, L).
template <class F>
struct SampleInBallScan {
  using Elt = typename F::Elt;
  const Domain<F> *D = nullptr;
  // [S, L]
  Ref<F, Bit, Committed> threshold;
  // [S, 8]
  Expr<F, Bit> thr;
  size_t S = 0, n = 0, tau = 0, L = 0, h = 0;

  SampleInBallScan() = default;
  SampleInBallScan(const Domain<F> &d, Ref<F, Bit, Committed> t, size_t tau_,
                   size_t L_, size_t h_)
      : D(&d), threshold(t), S(t.dims()[0]), n(tau_), tau(tau_), L(L_),
        h(h_) {
    thr = threshold;
    if (L < 8) {
      const Expr<F, Bit> low = threshold;
      const auto high = low.slice(h, L, 1).any(1).reshape({S, 1});
      thr = low.concat(high.reindex(std::vector<size_t>(8 - L, 0), 1), 1);
    }
  }

  lib::select::SelectionPlan selection_plan() const {
    return {PlanRecords::Selection::kRisingThreshold, tau};
  }
  Expr<F, Bit> accept(const Expr<F, Bit> &stream) const {
    return stream.from_bits() <= thr.from_bits();
  }
  Expr<F, Bit> done() const { return ~thr.slice(n, S).at(1, 7); }
  void assert_steps(const Scope &s, const std::string &name,
                    const Expr<F, Bit> &selected) const {
    std::vector<uint64_t> start;
    for (size_t b = 0; b < 8; ++b) start.push_back(((256 - tau) >> b) & 1);
    assert_equal(thr.at(0), D->constant(Bit{}, start),
                 s.name(name + ".start"));
    // Threshold i + 1 is threshold i plus the selection, which arrives
    // late (add_bit).
    const auto t = thr.slice(0, S - 1);
    assert_equal(thr.slice(1, S), lib::arith::add_bit<F>(t, selected),
                 s.name(name + ".step"));
  }
  Expr<F> labels() const { return lib::select::word_values(*D, thr); }
  Expr<F> output_labels() const {
    std::vector<uint64_t> v;
    for (size_t j = 0; j < tau; ++j) v.push_back(256 - tau + j);
    return lib::select::word_constants(*D, v);
  }
};

template <class F>
struct SampleInBallSelection {
  // [tau, 8]: the selected bytes
  Ref<F, Bit, Committed> j;
  // [S, L]: the thresholds' low bits
  Ref<F, Bit, Committed> threshold;
  Ref<F, Field, Public> delta;
};

// The rejection sampling: j_t, the t-th byte of STREAM ([S, 8] bits) not
// above 256 - tau + t, in order. The gadget owns the selected bytes and
// the thresholds (one oblivious scan per proof, ct.h).
template <class F, class P>
SampleInBallSelection<F> sample_in_ball_select(const Scope &s,
                                               Domain<F> &H,
                                               const std::string &name,
                                               Ref<F, Bit, P> stream_in,
                                               size_t tau) {
  using Elt = typename F::Elt;
  const F &f = H.field();
  if (tau == 0 || tau > 128)
    fail("sample_in_ball_select: tau = " + std::to_string(tau) +
         " is not in [1, 128] (the threshold's high bit is set until "
         "completion)");
  if (stream_in.n % 8 != 0)
    fail("sample_in_ball_select: the stream is not whole bytes");
  const size_t S = stream_in.n / 8;
  if (S < tau)
    fail("sample_in_ball_select: " + std::to_string(S) +
         " candidates for tau = " + std::to_string(tau));
  const auto stream = stream_in.reshape({S, 8});
  const size_t L = std::min<size_t>(size_t(std::bit_width(tau)), 8);
  size_t h = 0;
  if (L < 8)
    while ((size_t{2} << h) <= (size_t{1} << L) - tau) ++h;
  const F *pf = &f;
  SampleInBallSelection<F> out;
  std::tie(out.j, out.threshold) = s.advice_record(
      depends_on(stream),
      [pf, S, tau, L](const Tensor<Elt> &st, std::vector<Elt> &j,
                      std::vector<Elt> &thr) {
        const F &f = *pf;
        std::vector<uint32_t> v(S);
        for (size_t i = 0; i < S; ++i)
          v[i] = lib::select::host::sample_value(f, st.row(i));
        // Sample i is accepted when v[i] <= (256 - tau + before) mod 256.
        auto threshold = [tau](uint64_t before) {
          return (256 - tau + before) & 255;
        };
        const auto o = sample_in_ball_host::select(v, tau);
        j = lib::select::host::selected_bits(f, o, 8);
        for (size_t i = 0; i < S; ++i)
          for (size_t b = 0; b < L; ++b)
            thr[i * L + b] = ct::bit_elt(f, threshold(o.before[i]) >> b);
      },
      H.slot(Bit{}, s.scoped(name + ".j"), Shape{tau, 8}),
      H.slot(Bit{}, s.scoped(name + ".threshold"), Shape{S, L}));
  const SampleInBallScan<F> scan(H, out.threshold, tau, L, h);
  out.delta = lib::select::select_first(s, H, name, stream, out.j, scan);
  return out;
}

template <class F>
struct SampleInBallShuffle {
  Ref<F, Subfield<>, Committed> read_value, c_enc, final_origin;
  Ref<F, Bit, Committed> read_origin;
  // The records' unit and read-origin components as subfield cells, tied to
  // their bit forms by affine rows.
  Ref<F, Subfield<>, Committed> unit, origin;
  Ref<F, Field, Public> delta;
  // [N] each
  Ref<F, Bit, CircuitOnly> support, sign;
};

// The Fisher-Yates swaps of J (Bit [tau, 8], the selected bytes) with the
// signs SIGNS (Bit [tau]) over N cells, as one memory check.
template <class F, class P1, class P2>
SampleInBallShuffle<F> sample_in_ball_shuffle(const Scope &s,
                                              Domain<F> &H,
                                              const std::string &name,
                                              Ref<F, Bit, P1> j,
                                              Ref<F, Bit, P2> signs,
                                              size_t N = 256) {
  using Elt = typename F::Elt;
  const F &f = H.field();
  const size_t tau = signs.n;
  if (j.n != 8 * tau)
    fail("sample_in_ball_shuffle: j has " + std::to_string(j.n) +
         " bits, not 8 per sign");
  if (tau == 0 || tau >= N || N > 256)
    fail("sample_in_ball_shuffle: tau = " + std::to_string(tau) +
         " and N = " + std::to_string(N));
  // origin labels 0..tau
  const size_t lb = size_t(std::bit_width(tau));
  const Elt theta = sample_in_ball_theta(f);
  const Elt theta1 = f.addf(theta, f.one());
  const auto jw = j.reshape({tau, 8});
  const F *pf = &f;
  // The memory trace:
  // sample_in_ball_host::swaps, its cells 0, 1, 2 as 0, 1, theta.
  SampleInBallShuffle<F> out;
  std::tie(out.read_value, out.read_origin, out.c_enc, out.final_origin,
           out.unit, out.origin) =
      s.advice_record(
          depends_on(jw, signs),
          [pf, tau, N, lb, theta](const Tensor<Elt> &jv, const Tensor<Elt> &sg,
                                  std::vector<Elt> &rv, std::vector<Elt> &ro,
                                  std::vector<Elt> &fin,
                                  std::vector<Elt> &fo, std::vector<Elt> &un,
                                  std::vector<Elt> &ow) {
            const F &f = *pf;
            std::vector<uint64_t> js(tau), sv(tau);
            for (size_t t = 0; t < tau; ++t) {
              js[t] = lib::select::host::sample_value(f, jv.row(t));
              sv[t] = ct::bit_of(f, sg[t]);
            }
            const auto tr = sample_in_ball_host::swaps(js, sv, N);
            auto cell = [&](uint64_t c) {
              return ct::select(ct::mask(ct::eq(c, 2)), theta,
                                ct::select(ct::mask(c), f.one(), f.zero()));
            };
            for (size_t t = 0; t < tau; ++t) {
              rv[t] = cell(tr.read_value[t]);
              un[t] = cell(1 + sv[t]);
              ow[t] = lib::select::host::word_value(f, tr.read_origin[t], 16);
              for (size_t b = 0; b < lb; ++b)
                ro[t * lb + b] = ct::bit_elt(f, tr.read_origin[t] >> b);
            }
            for (size_t k = 0; k < N; ++k) {
              fin[k] = cell(tr.cells[k]);
              fo[k] = lib::select::host::word_value(f, tr.origins[k], 16);
            }
          },
          H.slot(Subfield{}, s.scoped(name + ".read_value"), Shape(tau)),
          H.slot(Bit{}, s.scoped(name + ".read_origin"), Shape{tau, lb}),
          H.slot(Subfield{}, s.scoped(name + ".c_enc"), Shape(N)),
          H.slot(Subfield{}, s.scoped(name + ".final_origin"), Shape(N)),
          H.slot(Subfield{}, s.scoped(name + ".unit"), Shape(tau)),
          H.slot(Subfield{}, s.scoped(name + ".origin"), Shape(tau)));

  std::vector<uint64_t> live, steps, at, cells;
  for (size_t k = 0; k < N - tau; ++k) live.push_back(k);
  for (size_t t = 0; t < tau; ++t) {
    steps.push_back(t + 1);
    at.push_back(N - tau + t);
  }
  for (size_t k = 0; k < N; ++k) cells.push_back(k);
  const Expr<F> aj = lib::select::word_values(H, jw);
  // The unit and the read origin enter the records as cells: read through
  // their bit expressions inside the product circuit, they cost it a layer.
  assert_zero(out.unit - (theta1 * Expr<F, Bit>(signs) + 1),
              s.name(name + ".unit"));
  assert_zero(out.origin - lib::select::word_values(H, out.read_origin),
              s.name(name + ".origin"));
  lib::permutation::Records<F, 3> initial(H), reads(H), writes(H), last(H);
  initial.push_constants({live, std::vector<uint64_t>(live.size(), 0),
                          std::vector<uint64_t>(live.size(), 0)});
  reads.push(aj, out.read_value, out.origin);
  writes.push(aj, out.unit, lib::select::word_constants(H, steps));
  writes.push(lib::select::word_constants(H, at), out.read_value, out.origin);
  last.push(lib::select::word_constants(H, cells), out.c_enc,
            out.final_origin);
  out.delta =
      lib::permutation::assert_memory(s, H, name, initial, reads, writes, last)
          .delta;
  {
    PlanRecords::SampleInBall rec;
    rec.domain = H.name;
    rec.challenge = out.delta.name();
    rec.tau = tau;
    s.note("sample-in-ball", name, rec);
  }
  // Read origins precede their step: o_t < t + 1.
  assert_true(out.read_origin.from_bits() < steps, s.name(name + ".fresh"));
  // The decoded challenge.
  const auto c = Expr<F, Subfield<>>(out.c_enc);
  const auto sign = c * c + c;
  const auto support = c + theta1 * sign;
  out.sign = s[H].bit_from_unchecked(name + ".sign", sign);
  out.support = s[H].bit_from_unchecked(name + ".support", support);
  return out;
}

// SampleInBall: the selection, then the shuffle, from the stream bytes and
// the sign bits.
template <class F>
struct SampleInBall {
  SampleInBallSelection<F> select;
  SampleInBallShuffle<F> shuffle;
};
template <class F, class P1, class P2>
SampleInBall<F> sample_in_ball(const Scope &s,
                               Domain<F> &H, const std::string &name,
                               Ref<F, Bit, P1> stream, Ref<F, Bit, P2> signs,
                               size_t N = 256) {
  SampleInBall<F> out;
  out.select =
      sample_in_ball_select(s, H, name + ".select", stream, signs.n);
  out.shuffle =
      sample_in_ball_shuffle(s, H, name + ".mem", out.select.j, signs, N);
  return out;
}

}  // namespace proofs::gordiehowe::examples

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_SAMPLE_IN_BALL_H_
