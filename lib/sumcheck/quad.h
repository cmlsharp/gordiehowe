// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: accessors and assign_all for the compressed form, a unit-coefficient shortcut option in bind_g and the bound evaluation, and bind_g and bind_gh_all in chunks from cached decoder checkpoints

#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_QUAD_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_QUAD_H_

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <mutex>
#include <vector>

#include "arrays/affine.h"
#include "arrays/eqs.h"
#include "sumcheck/equad.h"
#include "sumcheck/hquad.h"
#include "util/panic.h"
#include "util/parallel.h"

// ------------------------------------------------------------
// Representation of the QUAD array used in sumcheck.
//
// The main concern is to save memory.  To this end,
// we have three representations of the quad.
//
// The fully expanded representation EQuad (in equad.h)
// comprises the indices and the coefficient value.  EQuad
// is the only representation that can be canonicalized.
//
// The "ordinary" representation Quad (this file) contains (g, h)
// indices but it stores the coefficient as an index into an array of
// constants, where the index is 32 bits and the constant is a large
// field element.
//
// In addition, HQuad represents a QUAD after the g index has
// been bound.  Since g = 0 it does not need to be stored.
// A special method Quad::bind_g produces a compact HQuad in
// one step.
//
// The compiler works on EQuad and converts to Quad when done.
// Circuit evaluation works on Quad and materializes EQuad
// lazily.  Sumcheck starts with Quad, binds g into an HQuad,
// and finishes binding h on HQuad.
namespace proofs {
template <class Field>
class Quad {
  using Elt = typename Field::Elt;
  using Accum = typename Field::Accum;
  using kvec_t = std::vector<Elt>;
  using ecorner = typename EQuad<Field>::ecorner;
  using hcorner = typename HQuad<Field>::hcorner;
  using vcorner = typename HQuad<Field>::vcorner;

 public:
  using quad_corner_t = typename EQuad<Field>::quad_corner_t;
  using index_t = typename EQuad<Field>::index_t;

  struct delta_corner {
    quad_corner_t dg;
    quad_corner_t dh[2];
    uint32_t vi;

    bool operator==(const delta_corner& o) const {
      return dg == o.dg && dh[0] == o.dh[0] && dh[1] == o.dh[1] && vi == o.vi;
    }
  };

  using delta_table_t = std::vector<delta_corner>;

  explicit Quad(index_t n, std::shared_ptr<kvec_t> kvec,
                std::shared_ptr<delta_table_t> delta_table)
      : n_(n),
        vc_(n),
        delta_table_(std::move(delta_table)),
        kvec_(std::move(kvec)) {
    check(n > 0, "Quad n > 0");
  }

  // no copies
  Quad(const Quad& y) = delete;
  Quad(Quad&& y) = delete;
  Quad& operator=(const Quad& y) = delete;
  Quad& operator=(Quad&& y) = delete;

  index_t size() const { return n_; }

  void assign(index_t i, uint32_t di) {
    vc_[i] = di;
    reset_index();
  }

  // The compressed form, as built: each term's index into the delta table,
  // the delta table and the constants (GordieHowe's compile cache stores
  // and restores it as is).
  const std::vector<uint32_t>& delta_indices() const { return vc_; }
  const delta_table_t& deltas() const { return *delta_table_; }
  const kvec_t& constants() const { return *kvec_; }
  void assign_all(std::vector<uint32_t> vc) {
    check(vc.size() == n_, "Quad assign_all size");
    vc_ = std::move(vc);
    reset_index();
  }

  class const_iterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = ecorner;
    using difference_type = std::ptrdiff_t;
    using pointer = void;  // operator* returns by value
    using reference = ecorner;

    const_iterator(const Quad* q, index_t i)
        : q_(q), i_(i), prev_g_(0), prev_h0_(0), prev_h1_(0) {}

    ecorner operator*() const {
      const auto& d = (*q_->delta_table_)[q_->vc_[i_]];
      return ecorner{prev_g_ + d.dg,
                     {prev_h0_ + d.dh[0], prev_h1_ + d.dh[1]},
                     (*q_->kvec_)[d.vi]};
    }
    const_iterator& operator++() {
      const auto& d = (*q_->delta_table_)[q_->vc_[i_]];
      prev_g_ += d.dg;
      prev_h0_ += d.dh[0];
      prev_h1_ += d.dh[1];
      ++i_;
      return *this;
    }
    const_iterator operator++(int) {
      const_iterator tmp = *this;
      ++(*this);
      return tmp;
    }
    bool operator==(const const_iterator& other) const {
      return i_ == other.i_;
    }
    bool operator!=(const const_iterator& other) const {
      return i_ != other.i_;
    }

   private:
    const Quad* q_;
    index_t i_;
    quad_corner_t prev_g_;
    quad_corner_t prev_h0_;
    quad_corner_t prev_h1_;
  };

  // The terms ordered by gate (a stable counting sort of the decoded
  // terms), cut into chunks of about kIndexChunk terms at changes of gate,
  // for an evaluation in parallel by output (the prover's eval_quad). Built
  // once, on first use, from the circuit alone.
  struct GateTerm {
    uint32_t g, h0, h1, vi;
  };
  struct ByGate {
    std::vector<GateTerm> terms;
    // Chunk K is terms [first[K], first[K + 1]).
    std::vector<size_t> first;
  };
  const ByGate& by_gate() const {
    const ByGate* bg = by_gate_ptr_.load(std::memory_order_acquire);
    if (bg != nullptr) return *bg;
    std::lock_guard<std::mutex> lock(index_mu_);
    if (by_gate_ == nullptr) {
      auto out = std::make_unique<ByGate>();
      std::vector<GateTerm> t(n_);
      uint32_t g = 0, h0 = 0, h1 = 0, ng = 0;
      for (index_t i = 0; i < n_; ++i) {
        const delta_corner& d = (*delta_table_)[vc_[i]];
        g += uint32_t(d.dg);
        h0 += uint32_t(d.dh[0]);
        h1 += uint32_t(d.dh[1]);
        t[i] = GateTerm{g, h0, h1, d.vi};
        ng = std::max(ng, g + 1);
      }
      std::vector<size_t> at(size_t(ng) + 1, 0);
      for (const auto& x : t) ++at[size_t(x.g) + 1];
      for (size_t k = 0; k < ng; ++k) at[k + 1] += at[k];
      out->terms.resize(n_);
      for (const auto& x : t) out->terms[at[x.g]++] = x;
      out->first.push_back(0);
      for (size_t i = 1; i < n_; ++i)
        if (i - out->first.back() >= kIndexChunk &&
            out->terms[i].g != out->terms[i - 1].g)
          out->first.push_back(i);
      out->first.push_back(n_);
      by_gate_ = std::move(out);
    }
    by_gate_ptr_.store(by_gate_.get(), std::memory_order_release);
    return *by_gate_;
  }

  const_iterator begin() const { return const_iterator(this, 0); }
  const_iterator end() const { return const_iterator(this, n_); }

  // Equivalent to expand()->bind_g(...).

  // Allocate an hquad of minimal size and
  // g-bind it in place: in the chunks of the index (below), each from its
  // checkpoint into its own outputs, in parallel under a runner
  // (util/parallel.h). Terms with equal hands, which bind_g sums into one
  // output, never straddle two chunks, and field sums are exact, so the
  // result is the serial pass's.
  std::unique_ptr<HQuad<Field>> bind_g(size_t logv, const Elt* G0,
                                       const Elt* G1, const Elt& alpha,
                                       const Elt& beta, const Field& F,
                                       bool unit_coefficient_shortcuts = false) const {
    check(n_ > 0, "n_ > 0");
    const Index& ix = index();
    auto s = std::make_unique<HQuad<Field>>(ix.outputs);

    // The table up to the largest gate the terms name: its entries are
    // the full table's (the recursion only prunes the subtrees past it).
    const size_t nv = std::min(size_t(1) << logv, size_t(ix.gates));
    const auto dot = eq2(logv, corner_t(nv), G0, G1, alpha, F);

    const size_t nch = ix.chunks.size() - 1;
    const delta_corner* dt = delta_table_->data();
    const Elt* kv = kvec_->data();
    parallel::for_chunks(
        nch, parallel::grain_for(nch, parallel::kChunks),
        [&](size_t cb, size_t ce) {
          const Checkpoint& c0 = ix.chunks[cb];
          quad_corner_t g = c0.g, h0 = c0.h0, h1 = c0.h1;
          index_t wr = c0.out;
          const index_t end = ix.chunks[ce].begin;
          for (index_t i = c0.begin; i < end; ++i) {
            const delta_corner& d = dt[vc_[i]];
            g += d.dg;
            const bool same = i > c0.begin && d.dh[0] == quad_corner_t(0) &&
                              d.dh[1] == quad_corner_t(0);
            h0 += d.dh[0];
            h1 += d.dh[1];
            const Elt v = prep_v(kv[d.vi], dot[corner_t(g)], beta, F,
                                 unit_coefficient_shortcuts);
            if (same) {
              F.add(s->vc_[wr - 1].v, v);
            } else {
              s->hc_[wr] = hcorner{{h0, h1}};
              s->vc_[wr] = vcorner{v};
              ++wr;
            }
          }
        });

    return s;
  }

  // Optimized combined bind_g + bind_h, nondestructive, avoiding expansion.
  // The terms are summed in the chunks of the index (below), each from its
  // checkpoint into its own partial sum, in parallel under a runner
  // (util/parallel.h); the partial sums are added in chunk order. Field sums
  // are exact, so the result is the serial pass's.
  Elt bind_gh_all(
      // G bindings
      size_t logv, const Elt G0[/*logv*/], const Elt G1[/*logv*/],
      const Elt& alpha, const Elt& beta,
      // H bindings
      size_t logw, const Elt H0[/*logw*/], const Elt H1[/*logw*/],
      // field
      const Field& F, bool unit_coefficient_shortcuts = false) const {
    if (n_ == 0) return F.zero();
    const Index& ix = index();
    // The G table up to the largest gate the terms name, as in bind_g.
    const size_t nv = std::min(size_t(1) << logv, size_t(ix.gates));
    const auto eqg = eq2(logv, corner_t(nv), G0, G1, alpha, F);

    const size_t nw = size_t(1) << logw;
    Eqs<Field> eqh0(logw, nw, H0, F);
    Eqs<Field> eqh1(logw, nw, H1, F);

    const size_t nch = ix.chunks.size() - 1;
    const size_t grain = parallel::grain_for(nch, parallel::kChunks);
    std::vector<Elt> part(parallel::chunks(nch, grain), F.zero());
    const delta_corner* dt = delta_table_->data();
    const Elt* kv = kvec_->data();
    parallel::for_chunks(nch, grain, [&](size_t cb, size_t ce) {
      const Checkpoint& c0 = ix.chunks[cb];
      quad_corner_t g = c0.g, h0 = c0.h0, h1 = c0.h1;
      const index_t end = ix.chunks[ce].begin;
      Accum s{};
      for (index_t i = c0.begin; i < end; ++i) {
        const delta_corner& d = dt[vc_[i]];
        g += d.dg;
        h0 += d.dh[0];
        h1 += d.dh[1];
        Elt q = prep_v(kv[d.vi], eqg[corner_t(g)], beta, F,
                       unit_coefficient_shortcuts);
        F.mul(q, eqh0.at(corner_t(h0)));
        F.mac(s, q, eqh1.at(corner_t(h1)));
      }
      part[cb / grain] = F.reduce(s);
    });
    Elt s = F.zero();
    for (const Elt& p : part) F.add(s, p);
    return s;
  }

 private:
  static Elt prep_v(const Elt& v, const Elt& dot, const Elt& beta,
                    const Field& F, bool unit_coefficient_shortcuts) {
    if (v == F.zero()) {
      return F.mulf(beta, dot);
    } else if (unit_coefficient_shortcuts && v == F.one()) {
      // The coefficient is part of the circuit; dot still carries the
      // verifier's full-field challenge weights.
      return dot;
    } else {
      return F.mulf(v, dot);
    }
  }

  // The index: the terms cut into chunks of about kIndexChunk terms, each
  // starting at a term whose hands differ from its predecessor's, with the
  // decoder's state before it (the previous term's corners) and its first
  // output in bind_g; a last entry closes the list (begin n_, out the
  // output count). Built once, on first use, from the circuit alone.
  static constexpr size_t kIndexChunk = 1024;
  struct Checkpoint {
    index_t begin;
    quad_corner_t g, h0, h1;
    index_t out;
  };
  struct Index {
    std::vector<Checkpoint> chunks;
    index_t outputs;
    // The largest gate of a term, plus one.
    size_t gates;
  };
  const Index& index() const {
    const Index* ix = index_ptr_.load(std::memory_order_acquire);
    if (ix != nullptr) return *ix;
    std::lock_guard<std::mutex> lock(index_mu_);
    if (index_ == nullptr) {
      auto out = std::make_unique<Index>();
      quad_corner_t g(0), h0(0), h1(0);
      index_t outputs = 0, last = 0;
      size_t gates = 0;
      for (index_t i = 0; i < n_; ++i) {
        const delta_corner& d = (*delta_table_)[vc_[i]];
        const bool same = i > 0 && d.dh[0] == quad_corner_t(0) &&
                          d.dh[1] == quad_corner_t(0);
        if (!same) {
          if (i == 0 || i - last >= kIndexChunk) {
            out->chunks.push_back(Checkpoint{i, g, h0, h1, outputs});
            last = i;
          }
          ++outputs;
        }
        g += d.dg;
        h0 += d.dh[0];
        h1 += d.dh[1];
        gates = std::max(gates, size_t(g) + 1);
      }
      out->chunks.push_back(Checkpoint{n_, g, h0, h1, outputs});
      out->outputs = outputs;
      out->gates = gates;
      index_ = std::move(out);
    }
    index_ptr_.store(index_.get(), std::memory_order_release);
    return *index_;
  }
  void reset_index() {
    index_ptr_.store(nullptr, std::memory_order_release);
    index_.reset();
    by_gate_ptr_.store(nullptr, std::memory_order_release);
    by_gate_.reset();
  }

  // eq[i] = EQ[G0, i] + alpha EQ[G1, i] for i < N, as Eqs::raw_eq2: under
  // a runner and at kParallelEq entries or more, its top kEqSplit levels
  // first, then their subtrees in parallel, each element by the same
  // products and differences as the recursion.
  static constexpr size_t kParallelEq = size_t(1) << 13;
  static constexpr size_t kEqSplit = 4;
  static std::vector<Elt> eq2(size_t logn, corner_t n, const Elt* G0,
                              const Elt* G1, const Elt& alpha, const Field& F) {
    if (parallel::current == nullptr || size_t(n) < kParallelEq ||
        logn <= kEqSplit)
      return Eqs<Field>::raw_eq2(logn, n, G0, G1, alpha, F);
    std::vector<Elt> eq(n);
    const size_t sub = logn - kEqSplit;
    const corner_t s = corner_t(1) << sub;
    const size_t nsub = (size_t(n) + size_t(s) - 1) / size_t(s);
    parallel::for_each(nsub, 1, [&](size_t j) {
      Elt w0 = F.one(), w1 = alpha;
      for (size_t l = logn; l > sub; --l) {
        const Elt w0hi = F.mulf(w0, G0[l - 1]);
        const Elt w1hi = F.mulf(w1, G1[l - 1]);
        if ((j >> (l - 1 - sub)) & 1) {
          w0 = w0hi;
          w1 = w1hi;
        } else {
          w0 = F.subf(w0, w0hi);
          w1 = F.subf(w1, w1hi);
        }
      }
      const corner_t off = corner_t(j) * s;
      const corner_t m = std::min<corner_t>(s, n - off);
      fill2(&eq[off], sub, m, G0, G1, w0, w1, F);
    });
    return eq;
  }
  // Eqs::fill_recursive.
  static void fill2(Elt* eq, size_t l, corner_t n, const Elt* G0,
                    const Elt* G1, const Elt& w0, const Elt& w1,
                    const Field& F) {
    if (l > 0) {
      const size_t nl = l - 1;
      const corner_t s = corner_t(1) << nl;
      Elt w0hi = F.mulf(w0, G0[nl]);
      Elt w1hi = F.mulf(w1, G1[nl]);
      Elt w0lo = F.subf(w0, w0hi);
      Elt w1lo = F.subf(w1, w1hi);
      if (n <= s) {
        fill2(eq, nl, n, G0, G1, w0lo, w1lo, F);
      } else {
        fill2(eq, nl, s, G0, G1, w0lo, w1lo, F);
        fill2(eq + s, nl, n - s, G0, G1, w0hi, w1hi, F);
      }
    } else {
      eq[0] = F.addf(w0, w1);
    }
  }

  index_t n_;
  std::vector<uint32_t> vc_;
  std::shared_ptr<delta_table_t> delta_table_;
  std::shared_ptr<kvec_t> kvec_;
  mutable std::mutex index_mu_;
  mutable std::unique_ptr<Index> index_;
  mutable std::atomic<const Index*> index_ptr_{nullptr};
  mutable std::unique_ptr<ByGate> by_gate_;
  mutable std::atomic<const ByGate*> by_gate_ptr_{nullptr};
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_SUMCHECK_QUAD_H_
