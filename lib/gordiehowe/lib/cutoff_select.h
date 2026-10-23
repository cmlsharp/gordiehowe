// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: selection of the first n samples below a fixed cutoff, on
// the library's select_first (select.h). Falcon's HashToPoint selects
// 16-bit samples below 5q and ML-DSA's RejNTTPoly (mldsa/expand_a.h)
// 23-bit samples below q.
//
// select_first_n(s, H, stream, Cutoff{c}, Count{n}) proves that select.raw
// holds the first n samples of STREAM below c, in order. It commits the
// selected samples (select.raw), a label per candidate counting the
// selections before it (select.count) and saturation flags once n samples
// are selected (select.full); select_first checks them under one challenge
// (select.delta). The batch form runs one selection per stream under one
// challenge, naming each stream's values select.<m>.*. The generators run
// the oblivious scan of cutoff_select_witness.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_CUTOFF_SELECT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_CUTOFF_SELECT_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/lib/cutoff_select_witness.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::select {

struct Cutoff {
  uint32_t v;
};

template <class F>
struct CutoffSelection {
  // [Count, w]: the selected samples
  Ref<F, Bit, Committed> raw;
  // S: the labels (Counter)
  Ref<F, Subfield<>, Committed> count;
  // S - Count: saturation flags
  Ref<F, Bit, Committed> full;
  Ref<F, Field, Public> delta;
  // log2 of the probability that uniform samples leave fewer than Count
  // accepted (the honest prover's budget failure).
  double log2_budget_failure = 0;
};

// CutoffScan(n): the label counter COUNT with the committed flags FULL,
// accepting w-bit samples below the cutoff.
template <class F>
struct CutoffScan {
  using Elt = typename F::Elt;
  const Domain<F> *D = nullptr;
  Ref<F, Subfield<>, Committed> count;
  Ref<F, Bit, Committed> full;
  lib::select::Counter<F> counter;
  size_t S = 0, n = 0, w = 16;
  uint32_t cutoff = 0;

  explicit CutoffScan(const Domain<F> &d) : D(&d), counter(d.field()) {}

  lib::select::SelectionPlan selection_plan() const {
    return {PlanRecords::Selection::kFixedCutoff, cutoff};
  }
  Expr<F, Bit> accept(const Expr<F, Bit> &stream) const {
    if (uint64_t(cutoff) >= (uint64_t(1) << w))
      return D->constant(Bit{}, std::vector<uint64_t>(S, 1));
    return stream.from_bits() < uint64_t(cutoff);
  }
  Expr<F, Bit> done() const { return full; }
  void assert_steps(const Scope &s, const std::string &name,
                    const Expr<F, Bit> &selected) const {
    const Expr<F> c = count;
    assert_zero(c.slice(0, 1) - counter.at(0), s.name(name + ".start"));
    assert_equal(c.slice(1, S), counter.next(c.slice(0, S - 1), selected),
                 s.name(name + ".step"));
    if (n < S)
      assert_zero(Expr<F>(full) * (c.slice(n, S) - counter.at(n)),
                  s.name(name + ".done"));
  }
  Expr<F> labels() const { return count; }
  Expr<F> output_labels() const { return D->constant(counter.labels(n)); }
};

namespace cutoff_select_internal {

// The checks of one stream (a Bit value of H, [S, w] or S w bits read as
// w = 16) and of the cutoff and count; returns it as [S, w].
template <class F, class P>
Ref<F, Bit, P> checked_stream(const lib::select::Counter<F> &counter,
                              Ref<F, Bit, P> stream_in, uint32_t c,
                              size_t n) {
  const auto dims = stream_in.dims();
  const size_t w = dims.size() == 2 ? dims[1] : 16;
  if (w == 0 || w > 32 || stream_in.n % w != 0)
    fail("select_first_n: the stream has " + std::to_string(stream_in.n) +
         " bits, not a multiple of the sample width " + std::to_string(w));
  const size_t S = stream_in.n / w;
  if (uint64_t(c) > (uint64_t(1) << w))
    fail("select_first_n: the cutoff exceeds 2^" + std::to_string(w));
  if (n > S || n == 0)
    fail("select_first_n: Count " + std::to_string(n) +
         " is not in [1, S = " + std::to_string(S) + "]");
  // The labels are distinct: S below the counter's period.
  if (Bound(S) >= counter.period())
    fail("select_first_n: S is at least the label counter's period");
  // Sample i is row i.
  return stream_in.reshape({S, w});
}

// One selection's priv values in scope S (PRE.raw, PRE.count, PRE.full)
// over STREAM [S, w], and its scan.
template <class F, class P>
std::pair<CutoffSelection<F>, CutoffScan<F>> advice(
    const Scope &s, Domain<F> &H, const std::string &pre,
    const Ref<F, Bit, P> &stream, uint32_t c, size_t n) {
  using Elt = typename F::Elt;
  const F &f = H.field();
  const size_t S = stream.dims()[0], w = stream.dims()[1];
  const F *pf = &f;
  CutoffScan<F> scan(H);
  CutoffSelection<F> sel;
  sel.raw = s[H].priv(Bit{}, pre + ".raw", Shape{n, w}, depends_on(stream),
                      [pf, S, n, c, w](const Tensor<Elt> &st) {
                        return lib::select::host::selected_bits(
                            *pf, cutoff_host::scan_stream(*pf, st, S, n, c),
                            w);
                      });
  const lib::select::Counter<F> counter = scan.counter;
  sel.count = s[H].priv(Subfield{}, pre + ".count", S, depends_on(stream),
      [pf, S, n, c, counter](const Tensor<Elt> &st) {
        return cutoff_host::counts(
            counter, cutoff_host::scan_stream(*pf, st, S, n, c, false));
      });
  sel.full = s[H].priv(Bit{}, pre + ".full", S - n, depends_on(stream),
      [pf, S, n, c](const Tensor<Elt> &st) {
        return cutoff_host::full_bits(
            *pf, cutoff_host::scan_stream(*pf, st, S, n, c, false));
      });
  // Completeness: the budget fails with probability
  // Pr[Bin(S, c / 2^w) < n] on uniform samples.
  sel.log2_budget_failure = lib::select::host::log2_binomial_tail(
      S, double(c) / double(uint64_t(1) << w), n);
  scan.count = sel.count;
  scan.full = sel.full;
  scan.S = S;
  scan.n = n;
  scan.w = w;
  scan.cutoff = c;
  return {sel, scan};
}

}  // namespace cutoff_select_internal

// STREAM is a Bit value (a typed handle of another type is a C++ compile
// error).
template <class F, class X>
CutoffSelection<F> select_first_n(const Scope &,
                                  Domain<F> &, X, Cutoff, lib::select::Count) {
  static_assert(kTypeError<X>, "select_first_n: the stream is a Bit value");
  return {};
}
// Its names carry the scope's prefix (S is the system or a scope of it).
template <class F, class P>
CutoffSelection<F> select_first_n(const Scope &s,
                                  Domain<F> &H,
                                  Ref<F, Bit, P> stream_in, Cutoff cutoff,
                                  lib::select::Count count) {
  namespace csi = cutoff_select_internal;
  const lib::select::Counter<F> counter(H.field());
  const auto stream =
      csi::checked_stream(counter, stream_in, cutoff.v, count.v);
  auto [sel, scan] = csi::advice(s, H, "select", stream, cutoff.v, count.v);
  sel.delta = lib::select::select_first(s, H, "select", stream, sel.raw, scan);
  return sel;
}

// One selection per stream under one challenge (select_first_batch); the
// streams share a sample width.
template <class F, class P>
std::vector<CutoffSelection<F>> select_first_n(
    const Scope &s, Domain<F> &H, const std::vector<Ref<F, Bit, P>> &streams,
    Cutoff cutoff, lib::select::Count count) {
  namespace csi = cutoff_select_internal;
  const lib::select::Counter<F> counter(H.field());
  std::vector<CutoffSelection<F>> sels;
  std::vector<lib::select::SelectInstance<F, CutoffScan<F>>> inst;
  for (size_t m = 0; m < streams.size(); ++m) {
    const auto stream =
        csi::checked_stream(counter, streams[m], cutoff.v, count.v);
    auto [sel, scan] = csi::advice(s, H, "select." + std::to_string(m),
                                   stream, cutoff.v, count.v);
    sels.push_back(sel);
    inst.push_back({stream, sel.raw, scan});
  }
  const auto delta = lib::select::select_first_batch(s, H, "select", inst);
  for (auto &x : sels) x.delta = delta;
  return sels;
}

}  // namespace proofs::gordiehowe::lib::select

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_CUTOFF_SELECT_H_
