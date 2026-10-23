// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: ordered selection by a filtered multiset equality, an
// application randomized check written over the core.
//
// select_first(s, H, name, stream, out, scan) proves that OUT ([n, w] Bit)
// holds the first n samples of STREAM ([S, w] Bit) that SCAN accepts, in
// stream order. The prover supplies the scan's state before every sample
// (a label counter, committed by the scheme's gadget, which owns its priv
// values); the scan's predicates check its transitions pointwise, so their
// depth does not grow with S. A scan is a scheme gadget (CutoffScan in
// cutoff_select.h, ML-DSA's SampleInBallScan in
// examples/mldsa/sample_in_ball.h) with this interface, every member returning
// expressions of H or declaring predicates:
//
//   accept(stream) -> Bit [S]        the acceptance predicate
//   done() -> Bit [S - n]            all slots are filled before candidate
//                                    n + i (n < S only)
//   assert_steps(s, name, selected)  the counter's start, and state i ->
//                                    i + 1 advancing exactly on selection
//                                    (SELECTED: Bit [S - 1])
//   labels() -> [S]                  the slot the next selection fills
//   output_labels() -> [n]           output slot j's fixed label
//
// The function declares NAME.delta and, per instance, the predicates
//
//   selected = accept (i < n), accept AND NOT done (i >= n)
//   scan.assert_steps(selected[0, S - 1))
//   assert_filtered_multiset_equal over records (label, sample words):
//     left (labels(i), stream[i]) active selected[i], right
//     (output_labels(j), out[j])
//
// The records pack as permutation.h packs them: in characteristic 2 a word
// of up to 16 bits embeds as sum_j 2^j b_j in GF(2^16) (of_scalar's basis),
// and the fixed kappa packs label + kappa w_0 + kappa^2 w_1, injective when
// the labels lie in GF(2^16) and 1, kappa, kappa^2 are independent over it;
// in odd characteristic a word is the integer sum_j 2^j b_j, packed by kappa
// or by a challenge NAME.gamma (record_packing).
//
// The labels are a counter of the selections made before a candidate
// (Counter): in characteristic 2 g^k, g of order 2^16 - 1 in GF(2^16), with
// l_{i+1} = l_i sel_i.mux(g, 1); in odd characteristic the integer k, with
// l_{i+1} = l_i + sel_i. They are distinct for k below the counter's period
// (2^16 - 1, or p).
//
// select_first_batch(s, H, name, instances) runs several instances (each a
// stream, an output and a scan) under one delta, one filtered multiset
// equality per instance (ML-DSA's ExpandA, 16 RejNTTPoly selections;
// examples/mldsa/expand_a.h).
//
// The encoding of samples and labels, for the scans and other gadgets
// over GF(2^16) records (windows.h, examples/mldsa/sample_in_ball.h):
//
//   subfield_generator(f)        g of order 2^16 - 1 in GF(2^16)
//   word_values(D, x)            Bit words [m, w], w <= 16, as values
//                                sum_j of_scalar(2^j) x_j
//   word_constants(D, v)         the integers V as constants, of_scalar
//
// The honest prover's selection (namespace host), for the scans'
// generators: host::select_first, the oblivious scan (ct.h) whose
// acceptance a scan supplies; host::sample_value and host::selected_bits,
// the samples' integers and the selected samples' bits; and
// host::log2_binomial_tail, the budget's failure probability.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_SELECT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_SELECT_H_

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::select {

struct Count {
  size_t v;
};

// What a scan reports to the plan export (PlanRecords::Selection): its
// kind (a fixed cutoff or a rising threshold) and the cutoff or tau. A
// scan declares it as `SelectionPlan selection_plan() const`; a scan
// without one is recorded with kind kNone.
struct SelectionPlan {
  PlanRecords::Selection::Kind kind = PlanRecords::Selection::kNone;
  uint64_t bound = 0;
};
template <class ScanT, class = void>
struct has_selection_plan : std::false_type {};
template <class ScanT>
struct has_selection_plan<
    ScanT, std::void_t<decltype(std::declval<const ScanT &>().selection_plan())>>
    : std::true_type {};

// An element of GF(2^16) of multiplicative order 2^16 - 1.
template <class F>
typename F::Elt subfield_generator(const F &f) {
  auto pow = [&f](typename F::Elt a, uint64_t e) {
    typename F::Elt r = f.one();
    while (e) {
      if (e & 1) r = f.mulf(r, a);
      a = f.mulf(a, a);
      e >>= 1;
    }
    return r;
  };
  for (uint64_t u = 2; u < 65536; ++u) {
    const auto g = f.of_scalar(u);
    bool ok = true;
    for (uint64_t q : {3u, 5u, 17u, 257u}) ok = ok && pow(g, 65535 / q) != f.one();
    if (ok) return g;
  }
  fail("select: no element of order 2^16 - 1 in the subfield");
}

// The Bit words X ([..., w], w <= 16) as values of D, [m] for m words:
// sum_j of_scalar(2^j) x_j, a sum of products by constants, affine in X.
// In characteristic 2 a word embeds in GF(2^16) by of_scalar's basis; in
// odd characteristic it is the integer sum_j 2^j x_j.
template <class F>
Expr<F> word_values(const Domain<F> &D, const Expr<F, Bit> &x) {
  const size_t w = x.dims().back();
  const size_t m = x.size() / w;
  std::vector<typename F::Elt> basis;
  for (size_t j = 0; j < w; ++j)
    basis.push_back(D.field().of_scalar(uint64_t(1) << j));
  return (Expr<F>(x.reshape({m, w})) * D.constant(basis)).sum(1);
}
// The integers V as constants of D, embedded as word_values embeds words.
template <class F>
Expr<F> word_constants(const Domain<F> &D, const std::vector<uint64_t> &v) {
  std::vector<typename F::Elt> e;
  for (uint64_t x : v) e.push_back(D.field().of_scalar(x));
  return D.constant(e);
}

// The honest prover's side of a selection, oblivious (ct.h).
namespace host {

// The integer value of a sample's bits (0/1 field elements), least
// significant first.
template <class F>
uint32_t sample_value(const F &f, const Tensor<typename F::Elt> &bits) {
  uint32_t v = 0;
  for (size_t j = 0; j < bits.size(); ++j)
    v |= uint32_t(ct::bit_of(f, bits[j])) << j;
  return v;
}

// The element of the bit word X (W bits) that word_values gives it: sum_b
// of_scalar(2^b) x_b, with no branch on X.
template <class F>
typename F::Elt word_value(const F &f, uint64_t x, size_t w) {
  typename F::Elt r = f.zero();
  for (size_t b = 0; b < w; ++b)
    f.add(r, ct::select(ct::mask(x >> b), f.of_scalar(uint64_t(1) << b),
                        f.zero()));
  return r;
}

// The selection of the first N accepted samples among V:
//   before[i]  samples selected before candidate i: min(accepted before
//              i, N)
//   selected[i]  candidate i is accepted and before[i] < N
//   full[i]    before[n + i] = N (saturation of candidates N..S-1)
//   raw[k]     the k-th selected sample (k < N)
//   budget     at least N samples are accepted
//   steps      the inner steps of the scan, N (S - N + 1): a function of S
//              and N alone
struct Scan {
  std::vector<uint64_t> before, selected, full;
  std::vector<uint32_t> raw;
  uint64_t budget = 0;
  uint64_t steps = 0;
};
// The first N samples of V that ACCEPT accepts, obliviously: every
// comparison is a mask, and the trip counts and addresses depend on S and
// N alone. ACCEPT(i, before) is sample i's acceptance bit when BEFORE
// samples are selected (masks only). Output k is the candidate i with
// selected[i] and before[i] = k, which lies in i in [k, k + S - N] when
// the budget holds: a masked pass over that window, N (S - N + 1) steps.
// WITH_RAW false (a public choice) leaves raw empty and steps 0, for the
// callers that read only before, selected, full and budget.
template <class Accept>
Scan select_first(const std::vector<uint32_t> &v, size_t n, Accept accept,
                  bool with_raw = true) {
  const size_t S = v.size();
  Scan o;
  o.before.resize(S);
  o.selected.resize(S);
  uint64_t accepted = 0;
  for (size_t i = 0; i < S; ++i) {
    const uint64_t below = ct::lt(accepted, n);
    o.before[i] = ct::select(ct::mask(below), accepted, n);
    const uint64_t acc = accept(i, o.before[i]) & 1;
    o.selected[i] = acc & below;
    accepted += acc;
  }
  o.budget = ct::lt(accepted, n) ^ 1;
  for (size_t i = n; i < S; ++i) o.full.push_back(ct::eq(o.before[i], n));
  if (!with_raw) return o;
  o.raw.assign(n, 0);
  for (size_t k = 0; k < n; ++k) {
    uint64_t x = 0;
    for (size_t i = k; i <= k + (S - n); ++i) {
      x |= v[i] & ct::mask(o.selected[i] & ct::eq(o.before[i], k));
      ++o.steps;
    }
    o.raw[k] = uint32_t(x);
  }
  return o;
}

// The selected samples' bits, W per sample.
template <class F>
std::vector<typename F::Elt> selected_bits(const F &f, const Scan &o,
                                           size_t w = 16) {
  std::vector<typename F::Elt> out;
  out.reserve(w * o.raw.size());
  for (uint32_t x : o.raw)
    for (size_t j = 0; j < w; ++j) out.push_back(ct::bit_elt(f, x >> j));
  return out;
}

// log2 Pr[Bin(S, q) < n], summed in log space.
inline double log2_binomial_tail(size_t S, double q, size_t n) {
  if (q >= 1.0) return -std::numeric_limits<double>::infinity();
  if (q <= 0.0) return 0.0;
  double m = -std::numeric_limits<double>::infinity();
  std::vector<double> terms;
  for (size_t k = 0; k < n && k <= S; ++k) {
    const double t = std::lgamma(double(S) + 1) - std::lgamma(double(k) + 1) -
                     std::lgamma(double(S - k) + 1) + double(k) * std::log(q) +
                     double(S - k) * std::log1p(-q);
    terms.push_back(t);
    m = std::max(m, t);
  }
  double s = 0;
  for (double t : terms) s += std::exp(t - m);
  return (m + std::log(s)) / std::log(2.0);
}

}  // namespace host

// The label counter of an ordered selection (above): k selections encoded
// as g^k in characteristic 2 and as the integer k in odd characteristic.
template <class F>
struct Counter {
  using Elt = typename F::Elt;
  const F *f = nullptr;
  Elt g{};
  explicit Counter(const F &field) : f(&field) {
    if constexpr (F::kCharacteristicTwo)
      g = subfield_generator(field);
  }
  // The number of distinct labels: the order of g, or p.
  Bound period() const {
    if constexpr (F::kCharacteristicTwo) {
      return 65535;
    } else {
      return field_characteristic(*f);
    }
  }
  // The label of K selections.
  Elt at(uint64_t k) const {
    if constexpr (F::kCharacteristicTwo) {
      Elt r = f->one(), a = g;
      for (size_t t = 0; t < 64; ++t) {
        r = ct::select(ct::mask(k >> t), f->mulf(r, a), r);
        a = f->mulf(a, a);
      }
      return r;
    } else {
      return f->of_scalar(k);
    }
  }
  // The labels of 0 .. N - 1 selections.
  std::vector<Elt> labels(size_t n) const {
    std::vector<Elt> out;
    out.reserve(n);
    Elt x = at(0);
    for (size_t k = 0; k < n; ++k) {
      out.push_back(x);
      if constexpr (F::kCharacteristicTwo) {
        x = f->mulf(x, g);
      } else {
        f->add(x, f->one());
      }
    }
    return out;
  }
  // The label after LABEL when SEL (a Bit) selects: LABEL sel.mux(g, 1), or
  // LABEL + sel.
  Expr<F> next(const Expr<F> &label, const Expr<F, Bit> &sel) const {
    if constexpr (F::kCharacteristicTwo) {
      return label * sel.mux(g, f->one());
    } else {
      return label + sel;
    }
  }
};

// One instance of a batched selection: STREAM [S, w] and OUT [n, w], Bit
// values of H, and the scan that accepts.
template <class F, class ScanT>
struct SelectInstance {
  Expr<F, Bit> stream, out;
  ScanT scan;
};

namespace select_internal {

// The words of the samples X ([m, w] Bit) as values: words of 16 bits,
// each sum_j 2^j b_j (of_scalar's embedding in characteristic 2).
template <class F>
std::vector<Expr<F>> sample_words(const Domain<F> &D, const Expr<F, Bit> &x,
                                  size_t w) {
  const F &f = D.field();
  std::vector<Expr<F>> out;
  for (size_t e0 = 0; e0 < w; e0 += 16) {
    const size_t e1 = std::min(w, e0 + 16);
    std::vector<typename F::Elt> basis;
    for (size_t j = 0; j < e1 - e0; ++j)
      basis.push_back(f.of_scalar(uint64_t(1) << j));
    out.push_back(
        (Expr<F>(x.slice(e0, e1, 1)) * D.constant(basis)).sum(1));
  }
  return out;
}

}  // namespace select_internal

// SelectFirst (above) of several instances under one challenge delta: each
// instance's candidates and claims meet in their own filtered multiset
// equality NAME.route (NAME.route.<m> for several). Returns delta.
template <class F, class ScanT>
Ref<F, Field, Public> select_first_batch(
    const Scope &s, Domain<F> &H, const std::string &name,
    const std::vector<SelectInstance<F, ScanT>> &inst) {
  const std::string what = "select_first '" + s.scoped(name) + "'";
  if (inst.empty()) fail(what + ": no instance");
  std::vector<size_t> Ss, ns;
  size_t w = 0;
  for (const auto &x : inst) {
    const auto sd = x.stream.dims(), od = x.out.dims();
    if (sd.size() != 2 || od.size() != 2 || sd[1] != od[1])
      fail(what + ": the stream and the output are [S, w] and [n, w] bits");
    if (w != 0 && sd[1] != w)
      fail(what + ": the instances' sample widths differ");
    w = sd[1];
    if (od[0] > sd[0] || od[0] == 0)
      fail(what + ": " + std::to_string(od[0]) +
           " outputs are not in [1, S = " + std::to_string(sd[0]) + "]");
    Ss.push_back(sd[0]);
    ns.push_back(od[0]);
  }
  if (w == 0 || w > 32)
    fail(what + ": the sample width " + std::to_string(w) +
         " is not in [1, 32]");
  const size_t words = (w + 15) / 16;
  // The records (label, words...) of every instance, and their packing.
  std::vector<std::vector<Expr<F>>> lefts, rights;
  std::vector<Expr<F>> comps;
  for (const auto &x : inst) {
    std::vector<Expr<F>> l = {x.scan.labels()};
    std::vector<Expr<F>> r = {x.scan.output_labels()};
    for (const auto &e : select_internal::sample_words(H, x.stream, w))
      l.push_back(e);
    for (const auto &e : select_internal::sample_words(H, x.out, w))
      r.push_back(e);
    comps.insert(comps.end(), l.begin(), l.end());
    comps.insert(comps.end(), r.begin(), r.end());
    lefts.push_back(std::move(l));
    rights.push_back(std::move(r));
  }
  const auto packing =
      permutation::record_packing(s, H, name, 1 + words, comps);
  if constexpr (F::kCharacteristicTwo)
    if (!packing.fixed)
      fail(what + ": the labels or samples leave GF(2^16), or 1, kappa, "
           "..., kappa^" + std::to_string(words) +
           " are dependent over it");
  // Tests the streams, the outputs and the states (inferred from the
  // predicates).
  auto delta = s[H].challenge(name + ".delta");
  for (size_t m = 0; m < inst.size(); ++m) {
    PlanRecords::Selection rec;
    const std::string nm =
        inst.size() > 1 ? name + "[" + std::to_string(m) + "]" : name;
    rec.domain = H.name;
    rec.challenge = delta.name();
    rec.candidates = Ss[m];
    rec.outputs = ns[m];
    rec.width = w;
    if constexpr (has_selection_plan<ScanT>::value) {
      const SelectionPlan sp = inst[m].scan.selection_plan();
      rec.kind = sp.kind;
      rec.bound = sp.bound;
    }
    s.note("selection", nm, rec);
    // The instance's grand products have degree at most S in delta, and
    // (A - 1) S in gamma when the records pack by it.
    s.note("charge", "select", ChallengeCharge{delta, Bound(Ss[m])});
    if (packing.gamma.has_value())
      s.note("charge", "select",
             ChallengeCharge{*packing.gamma, Bound(Ss[m]) * Bound(words)});
  }
  for (size_t m = 0; m < inst.size(); ++m) {
    const auto &x = inst[m];
    const size_t S = Ss[m], n = ns[m];
    const std::string nm =
        inst.size() > 1 ? name + "." + std::to_string(m) : name;
    const Expr<F, Bit> acc = x.scan.accept(x.stream);
    // Completion is impossible before candidate n.
    const Expr<F, Bit> selected =
        n < S ? acc.slice(0, n).concat(acc.slice(n, S) & ~x.scan.done())
              : acc;
    if (S > 1) x.scan.assert_steps(s, nm, selected.slice(0, S - 1));
    permutation::assert_products_equal(
        delta, packing(lefts[m]), std::optional<Expr<F, Bit>>(selected),
        packing(rights[m]), s.name(nm + ".route"));
  }
  return delta;
}

// SelectFirst (above) of one instance. Returns the challenge delta.
template <class F, class ScanT>
Ref<F, Field, Public> select_first(const Scope &s, Domain<F> &H,
                                   const std::string &name,
                                   const Expr<F, Bit> &stream,
                                   const Expr<F, Bit> &out,
                                   const ScanT &scan) {
  return select_first_batch(
      s, H, name, std::vector<SelectInstance<F, ScanT>>{{stream, out, scan}});
}

}  // namespace proofs::gordiehowe::lib::select

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_SELECT_H_
