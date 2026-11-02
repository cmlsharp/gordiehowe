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
// Modified 2026 by Chad Sharp and Paul Grubbs: templated on transcript hash, unit-coefficient shortcuts, per-phase profiling scopes, optional unsatisfied-witness proving, the circuit evaluation and the hand products in parallel by output, and a GKR kernel trace

#ifndef PRIVACY_PROOFS_ZK_LIB_SUMCHECK_PROVER_LAYERS_H_
#define PRIVACY_PROOFS_ZK_LIB_SUMCHECK_PROVER_LAYERS_H_

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <optional>
#include <string>
#include <vector>

#include "arrays/affine.h"
#include "arrays/dense.h"
#include "arrays/eqs.h"
#include "sumcheck/circuit.h"
#include "sumcheck/equad.h"
#include "sumcheck/hquad.h"
#include "sumcheck/quad.h"
#include "sumcheck/transcript_sumcheck.h"
#include "util/panic.h"
#include "util/parallel.h"
#include "util/perf.h"
#include "util/prover_profile.h"

namespace proofs {

// The sum-check's parts, for the phase timers: NAME under the field's
// characteristic prefix (bin.gkr.sc.NAME or odd.gkr.sc.NAME).
template <class Field>
const char* sumcheck_phase(const char* bin, const char* odd) {
  return Field::kCharacteristicTwo ? bin : odd;
}

// The GKR trace, a diagnostic off by default (GH_GKR_TRACE=1): each
// kernel of the circuit evaluation and of the sum-check, per layer, round
// and hand, with its size, its time and the chunks and distinct threads of
// its parallel calls (util/parallel.h's ChunkTrace), printed as GKR_TRACE
// lines to stderr when a proof's sum-check ends. It changes no result.
class GkrTrace {
 public:
  static bool on() {
    static const bool b = [] {
      const char* e = std::getenv("GH_GKR_TRACE");
      return e != nullptr && e[0] == '1';
    }();
    return b;
  }
  explicit GkrTrace(const char* field) : field_(field), on_(on()) {}
  // Fields a kernel adds to its step's line.
  static std::string& extra() {
    thread_local std::string e;
    return e;
  }
  ~GkrTrace() {
    if (!on_ || out_.empty()) return;
    std::fputs(out_.c_str(), stderr);
  }
  // FN() timed as KERNEL at (LAYER, ROUND, HAND) over N items.
  template <class Fn>
  void step(const char* kernel, size_t layer, size_t round, int hand,
            size_t n, Fn&& fn) {
    if (!on_) {
      fn();
      return;
    }
    parallel::ChunkTrace ct;
    parallel::ChunkTrace* prev = parallel::trace;
    parallel::trace = &ct;
    const auto t0 = std::chrono::steady_clock::now();
    fn();
    const double us = std::chrono::duration<double, std::micro>(
                          std::chrono::steady_clock::now() - t0)
                          .count();
    parallel::trace = prev;
    char buf[400];
    std::snprintf(buf, sizeof(buf),
                  "GKR_TRACE %s layer=%zu round=%zu hand=%d kernel=%s n=%zu "
                  "us=%.3f calls=%zu chunks=%zu split=%zu threads=%zu "
                  "max_threads=%zu %s\n",
                  field_, layer, round, hand, kernel, n, us, ct.calls,
                  ct.chunks, ct.split, ct.threads, ct.max_threads,
                  extra().c_str());
    extra().clear();
    out_ += buf;
  }

 private:
  const char* field_;
  bool on_;
  std::string out_;
};

// A high level idea is partially described in chapter 4.6.7 "Leveraging Data
// Parallelism for Further Speedups" in the book "Proofs, Arguments, and
// Zero-Knowledge" by Justin Thaler.
template <class Field>
class ProverLayers {
  using Elt = typename Field::Elt;
  using Accum = typename Field::Accum;

 public:
  // Tests clear this to model a cheating prover: evaluation keeps going past
  // a failed assertion, and the prover does not check its own layer sums.
  // The resulting proof must be rejected by the verifier.
  bool require_satisfied = true;

  using inputs = std::vector<std::unique_ptr<Dense<Field>>>;

  explicit ProverLayers(const Field& f) : f_(f) {}

  // Evaluate CIRCUIT on input wires W0.  This function stores the
  // input wires of each layer L into IN->at(L), and returns the
  // final output.  This asymmetry reflects the fact that for L
  // layers there are L+1 meaningful sets of wires, and that the
  // prover needs IN while the verifier needs the final output.
  std::unique_ptr<Dense<Field>> eval_circuit(inputs* in,
                                             const Circuit<Field>* circ,
                                             std::unique_ptr<Dense<Field>> W0,
                                             const Field& F) {
    if (in == nullptr || circ == nullptr || W0 == nullptr) return nullptr;
    PerfRegion perf("eval");
    GkrTrace trace(Field::kCharacteristicTwo ? "bin" : "odd");

    std::unique_ptr<Dense<Field>> finalV;
    size_t nl = circ->nl, nc = circ->nc;
    check(nl >= 1, "nl >= 1");
    check(nc >= 1, "nc >= 1");

    Dense<Field>* W = W0.get();

    in->resize(nl);
    in->at(nl - 1).swap(W0);

    // Allocate memory and evaluate layer on input W and output V
    for (size_t l = nl; l-- > 0;) {
      Dense<Field>* V;
      if (l > 0) {
        // input of layer l-1 = output of layer l
        in->at(l - 1) = std::make_unique<Dense<Field>>(nc, circ->l[l - 1].nw);
        V = in->at(l - 1).get();
      } else {
        // final output = output of layer 0
        finalV = std::make_unique<Dense<Field>>(nc, circ->nv);
        V = finalV.get();
      }

      bool ok = true;
      trace.step("eval", l, 0, -1, circ->l[l].quad->size(), [&] {
        ok = eval_quad(circ->l[l].quad.get(), V, W, F,
                       circ->l[l].unit_coefficient_shortcuts);
      });
      if (!ok) {
        // Early exit in case of assertion failure.
        // In this case IN is only partially allocated.
        // To avoid ambiguities, free all memory that we may have allocated.
        for (size_t i = 0; i < nl; ++i) {
          in->at(i) = nullptr;
        }
        finalV = nullptr;

        return /*finalV=*/nullptr;
      }

      W = V;
    }

    char extra[64];
    std::snprintf(extra, sizeof(extra), "esz=%zu nl=%zu", sizeof(Elt),
                  size_t(nl));
    perf.report(extra);
    return finalV;
  }

 protected:
  const Field& f_;
  // A struct that collects the bindings generated while proving one
  // layer, to serve as initial bindings for the next layer.
  // This protected class must be defined before the public section.
  struct bindings {
    size_t logv;
    Elt q[Proof<Field>::kMaxBindings];
    Elt g[2][Proof<Field>::kMaxBindings];
  };

  // Generate proof for circuit, as a protected member, the caller must
  // ensure that input parameters are valid.
  template <class Hash>
  void prove(Proof<Field>* pr, const Proof<Field>* pad,
             const Circuit<Field>* circ, const inputs& in, ProofAux<Field>* aux,
             bindings& bnd, TranscriptSumcheck<Field, Hash>& ts,
             const Field& F) {
    size_t logc = circ->logc;
    corner_t nc = circ->nc;

    check(circ->logv <= Proof<Field>::kMaxBindings,
          "CIRCUIT->logv <= kMaxBindings");

    check(pr->l.size() >= circ->nl, "Proof size must match circuit layers");
    if (pad != nullptr) {
      check(pad->l.size() >= circ->nl, "Pad size must match circuit layers");
    }
    if (aux != nullptr) {
      check(aux->bound_quad.size() >= circ->nl,
            "Aux size must match circuit layers");
    }

    bnd.logv = circ->logv;

    // obtain the initial Q and G[0] bindings from the verifier
    ts.begin_circuit(bnd.q, bnd.g[0]);

    // Duplicate the g[0] binding.
    // In general, the prover step takes two claims G[0], G[1] on the output
    // wires and reduces them to one claim on G[0] + alpha * G[1] for random
    // alpha. However, in the first step, there is only one claim, so we
    // need to make up G[1]. The code sets G[1] = G[0] and it doesn't affect
    // soundness.
    for (size_t i = 0; i < bnd.logv; ++i) {
      bnd.g[1][i] = bnd.g[0][i];
    }

    // Unpadded claims on the two hands, initially zero and updated in
    // layer()
    Elt WC[2] = {F.zero(), F.zero()};
    GkrTrace trace(Field::kCharacteristicTwo ? "bin" : "odd");

    for (size_t ly = 0; ly < circ->nl; ++ly) {
      auto clr = &circ->l.at(ly);
      Elt alpha, beta;
      ts.begin_layer(alpha, beta, ly);
      std::optional<profiling::Scope> bg;
      bg.emplace(
          sumcheck_phase<Field>("bin.gkr.sc.bind_g", "odd.gkr.sc.bind_g"));
      Eqs<Field> EQ(logc, nc, bnd.q, F);
      std::unique_ptr<HQuad<Field>> HQUAD;
      trace.step("bind_g", ly, 0, -1, clr->quad->size(), [&] {
        HQUAD = clr->quad->bind_g(bnd.logv, bnd.g[0], bnd.g[1], alpha, beta,
                                  F, clr->unit_coefficient_shortcuts);
      });
      bg.reset();

      layer(pr, pad, ts, bnd, ly, logc, clr->logw, &EQ, HQUAD.get(),
            in.at(ly).get(), alpha, WC, F, trace);

      if (aux != nullptr) {
        aux->bound_quad[ly] = HQUAD->scalar();
      }
    }
  }

 private:
  using index_t = typename EQuad<Field>::index_t;
  using CPoly = typename LayerProof<Field>::CPoly;
  using WPoly = typename LayerProof<Field>::WPoly;

  /*
  Engage in single-layer sumcheck on

          EQ[c] QUAD[r,l] W[r,c] W[l,c]

  Bind c to C, r to R, and l to L (in that order).  Store claims
  W[R,C] and W[L,C] in the proof, and set BND to the new bindings for
  the next layer.

  logw: number of sumcheck rounds in r, l
  logc: number of sumcheck rounds in c
  */
  template <class Hash>
  void layer(Proof<Field>* pr, const Proof<Field>* pad,
             TranscriptSumcheck<Field, Hash>& ts, bindings& bnd, size_t layer,
             size_t logc, size_t logw, Eqs<Field>* EQ, HQuad<Field>* HQUAD,
             Dense<Field>* W, const Elt& alpha, Elt WC[2], const Field& F,
             GkrTrace& trace) {
    check(EQ->n() == W->n0_, "EQ->n() == W->n0_");

    check(logw <= Proof<Field>::kMaxBindings, "logw <= kMaxBindings");
    check(logc <= Proof<Field>::kMaxBindings, "logc <= kMaxBindings");
    bnd.logv = logw;

    // Reconstruct the sum from the claims of the previous
    // layer.
    Elt sum = F.addf(WC[0], F.mulf(alpha, WC[1]));

    // Now  SUM = \sum_{c,l,r} EQ[c] Q[l,r] W[l,c] W[r,c]
    //
    // Bind the C variables
    std::optional<profiling::Scope> cs;
    cs.emplace(
        sumcheck_phase<Field>("bin.gkr.sc.c", "odd.gkr.sc.c"));
    for (size_t round = 0; round < logc; ++round) {
      CPoly evals = evaluations_c(EQ, W, HQUAD, sum, F);

      Elt rnd = round_c(pr, pad, ts, layer, round, evals, F);
      bnd.q[round] = rnd;

      // bind the C variable in both EQ and W
      EQ->bind(rnd, F);
      W->bind(rnd, F);
      sum = evals.eval_lagrange(rnd, F);
    }

    cs.reset();
    Elt eq0 = EQ->scalar();

    W->reshape(W->n1_);
    check(W->n1_ == 1, "W->n1_ == 1");

    // To save memory, we avoid cloning W. Instead, we use a single temporary
    // buffer Wtmp of size N/2 and start with both hand-pointers WH[0,1]
    // pointing to W. In the first round of the loop, hand 0 is bound
    // out-of-place from W into Wtmp, and we then update WH[0] to point to Wtmp.
    // Hand 1 is then bound in-place in W. This strategy uses 1.5N space instead
    // of 2N.
    auto Wtmp = std::make_unique<Dense<Field>>((W->n0_ + 1) / 2, 1);
    Dense<Field>* WH[2] = {W, W};
    // One QW buffer for every round, sized for the first.
    std::vector<Elt> QW;
    QW.reserve(W->n0_);

    // Now  SUM = \sum_{l,r} eq0 Q[l,r] Wl[l] Wr[r].  Bind l and
    // r in alternating "hands".
    for (size_t round = 0; round < logw; ++round) {
      for (size_t hand = 0; hand < 2; hand++) {
        // In \sum_{l,r} eq0 Q[l,r] Wl[l] Wl[r], first precompute
        // QW[l] = \sum_{r} Q[l,r] W[r] as a dense array, and then do
        // a round on  \sum_{l} eq0 QW[l] W[l].
        const size_t ohand = 1 - hand;
        const int th = int(hand);
        const size_t nw = WH[hand]->n0_, nq = HQUAD->n_;

        // QW[l] = \sum_{r} Q[l,r] W[r]
        std::optional<profiling::Scope> ph;
        ph.emplace(
            sumcheck_phase<Field>("bin.gkr.sc.qw", "odd.gkr.sc.qw"));
        trace.step("qw", layer, round, th, nq, [&] {
          hand_products(*HQUAD, hand, WH[ohand]->v_.data(), QW, nw, F);
        });

        // Compute the binding of \sum_{l} eq0 QW[l] W[l] as
        // a quadratic polynomial.
        ph.emplace(
            sumcheck_phase<Field>("bin.gkr.sc.evals", "odd.gkr.sc.evals"));
        WPoly evals;
        trace.step("evals", layer, round, th, nw, [&] {
          evals = evaluations(nw, eq0, QW.data(), &WH[hand]->v_[0], sum, F);
        });
        ph.reset();

        Elt rnd;
        trace.step("round", layer, round, th, 0, [&] {
          rnd = round_h(pr, pad, ts, layer, hand, round, evals, F);
        });
        bnd.g[hand][round] = rnd;
        sum = evals.eval_lagrange(rnd, F);

        // bind the r variable in W[hand] and QUAD
        ph.emplace(
            sumcheck_phase<Field>("bin.gkr.sc.wbind", "odd.gkr.sc.wbind"));
        trace.step("wbind", layer, round, th, nw, [&] {
          if (round == 0 && hand == 0) {
            WH[0] = Wtmp.get();
            WH[0]->bind(rnd, *W, F);
          } else {
            WH[hand]->bind(rnd, F);
          }
        });
        ph.emplace(
            sumcheck_phase<Field>("bin.gkr.sc.hbind", "odd.gkr.sc.hbind"));
        trace.step("hbind", layer, round, th, nq,
                   [&] { HQUAD->bind_h(rnd, hand, F); });
      }
    }

    Elt hquad = HQUAD->scalar();
    WC[0] = WH[0]->scalar();
    WC[1] = WH[1]->scalar();
    Elt expected_sum = F.mulf(eq0, F.mulf(hquad, F.mulf(WC[0], WC[1])));
    check(!require_satisfied || sum == expected_sum,
          "reconstructed sum == eq0 * quad * wl * wr");
    end_layer(pr, pad, ts, layer, WC, F);
  }

  // Evaluate the quadratic form
  //
  //         V[g,c] = QUAD[g|r,l] W[r,c] W[l,c]
  //
  // Returns false in the case the quad is an assert0 check that fails.
  //
  // Under a runner and at kParallelEval terms or more, in parallel by
  // output: the terms by gate (Quad::by_gate), each chunk owning its
  // gates. Field sums are exact, so V is the serial loop's.
  static constexpr size_t kParallelEval = size_t(1) << 12;
  bool eval_quad(const Quad<Field>* quad, Dense<Field>* V,
                 const Dense<Field>* W, const Field& F,
                 bool unit_coefficient_shortcuts) {
    check(V->n0_ == W->n0_, "V->n0_ == W->n0_");
    corner_t n0 = V->n0_;

    V->clear(F);
    if (parallel::current != nullptr && size_t(quad->size()) >= kParallelEval) {
      const auto& bg = quad->by_gate();
      const Elt* kv = quad->constants().data();
      const size_t nch = bg.first.size() - 1;
      std::atomic<bool> failed{false};
      const bool req = require_satisfied;
      parallel::for_chunks(
          nch, parallel::grain_for(nch, parallel::kChunks),
          [&](size_t cb, size_t ce) {
            for (size_t i = bg.first[cb]; i < bg.first[ce]; ++i) {
              const auto& t = bg.terms[i];
              const corner_t g(t.g), r(t.h0), l(t.h1);
              const Elt& v = kv[t.vi];
              for (corner_t c = 0; c < n0; ++c) {
                if (v == F.zero()) {
                  Elt y = W->v_[n0 * l + c];
                  F.mul(y, W->v_[n0 * r + c]);
                  if (y != F.zero() && req) {
                    failed.store(true, std::memory_order_relaxed);
                    return;
                  }
                } else {
                  Elt x = v;
                  if (unit_coefficient_shortcuts && v == F.one()) {
                    x = W->v_[n0 * l + c];
                  } else {
                    F.mul(x, W->v_[n0 * l + c]);
                  }
                  F.mul(x, W->v_[n0 * r + c]);
                  F.add(V->v_[n0 * g + c], x);
                }
              }
            }
          });
      return !failed.load();
    }
    for (const auto& ec : *quad) {
      const corner_t g(ec.g);
      const corner_t r(ec.h[0]);
      const corner_t l(ec.h[1]);
      for (corner_t c = 0; c < n0; ++c) {
        if (ec.v == F.zero()) {
          // assert that the computed W[l]W[r] is zero.
          Elt y = W->v_[n0 * l + c];
          F.mul(y, W->v_[n0 * r + c]);
          if (y != F.zero() && require_satisfied) {
            return false;
          }
        } else {
          Elt x = ec.v;
          // Both tests concern execution policy / circuit coefficients,
          // never witness values. Preserve the original path by default.
          if (unit_coefficient_shortcuts && ec.v == F.one()) {
            x = W->v_[n0 * l + c];
          } else {
            F.mul(x, W->v_[n0 * l + c]);
          }
          F.mul(x, W->v_[n0 * r + c]);
          F.add(V->v_[n0 * g + c], x);
        }
      }
    }
    return true;
  }

  template <class Hash>
  Elt /*R*/ round_c(Proof<Field>* pr, const Proof<Field>* pad,
                    TranscriptSumcheck<Field, Hash>& ts, size_t layer,
                    size_t round, CPoly poly, const Field& F) {
    check(round < Proof<Field>::kMaxBindings, "round < kMaxBindings");

    if (pad) {
      poly.sub(pad->l[layer].cp[round], F);
    }

    pr->l[layer].cp[round] = poly;
    return ts.round(poly);
  }

  template <class Hash>
  Elt /*R*/ round_h(Proof<Field>* pr, const Proof<Field>* pad,
                    TranscriptSumcheck<Field, Hash>& ts, size_t layer,
                    size_t hand, size_t round, WPoly poly, const Field& F) {
    check(round < Proof<Field>::kMaxBindings, "round < kMaxBindings");
    if (pad) {
      poly.sub(pad->l[layer].hp[hand][round], F);
    }
    pr->l[layer].hp[hand][round] = poly;
    return ts.round(poly);
  }

  template <class Hash>
  void end_layer(Proof<Field>* pr, const Proof<Field>* pad,
                 TranscriptSumcheck<Field, Hash>& ts, size_t layer,
                 const Elt wc[2], const Field& F) {
    Elt tt[2] = {wc[0], wc[1]};
    if (pad) {
      F.sub(tt[0], pad->l[layer].wc[0]);
      F.sub(tt[1], pad->l[layer].wc[1]);
    }

    pr->l[layer].wc[0] = tt[0];
    pr->l[layer].wc[1] = tt[1];

    ts.write(tt, 1, 2);
  }

  // QW[l] = \sum_{r} Q[l,r] W[r] for l < NW, the hand HAND being l and
  // the other r. Under a runner and at kParallelQW corners or more, in
  // parallel by output: QW is cut into blocks of 2^s entries and the
  // corners into runs of consecutive corners whose l lies in one block
  // (found in parallel chunks). A task owns consecutive blocks of about
  // nq / kChunks corners, zeroes them and adds its runs' products into
  // them; a block with more corners than that (a wire most corners read,
  // such as the constant one) is cut into pieces of that many, each summed
  // into its own buffer, and the pieces are added into QW in order after.
  // Field sums are exact, so the result is the serial loop's.
  // Measured break-even: 2^12 corners in odd characteristic; in
  // characteristic two, whose products are cheap, the blocking costs more
  // than it saves at every size measured (up to 2^14).
  static constexpr size_t kParallelQW =
      Field::kCharacteristicTwo ? size_t(1) << 16 : size_t(1) << 12;
  static constexpr size_t kQWBlocks = 64;
  static void hand_products(const HQuad<Field>& hq, size_t hand, const Elt* w,
                            std::vector<Elt>& QW, size_t nw, const Field& F) {
    const size_t nq = hq.n_, ohand = 1 - hand;
    const auto* hc = hq.hc_.data();
    const auto* vc = hq.vc_.data();
    if (parallel::current == nullptr || nq < kParallelQW) {
      QW.assign(nw, Elt{});
      for (size_t i = 0; i < nq; ++i) {
        const corner_t p0(hc[i].h[hand]);
        const corner_t p1(hc[i].h[ohand]);
        F.add(QW[p0], F.mulf(vc[i].v, w[p1]));
      }
      return;
    }
    QW.resize(nw);
    size_t sh = 0;
    while ((nw >> sh) > kQWBlocks) ++sh;
    const size_t nb = ((nw - 1) >> sh) + 1;
    // The runs, each its first corner and block, per chunk in order.
    const size_t grain = parallel::grain_for(nq, parallel::kChunks);
    const size_t nc = parallel::chunks(nq, grain);
    std::vector<std::vector<std::pair<size_t, size_t>>> part(nc);
    parallel::for_chunks(nq, grain, [&](size_t b, size_t e) {
      auto& r = part[b / grain];
      size_t prev = SIZE_MAX;
      for (size_t i = b; i < e; ++i) {
        const size_t blk = size_t(hc[i].h[hand]) >> sh;
        if (blk != prev) r.push_back({i, blk});
        prev = blk;
      }
    });
    std::vector<size_t> rstart, rblock;
    for (const auto& r : part)
      for (const auto& x : r) {
        rstart.push_back(x.first);
        rblock.push_back(x.second);
      }
    const size_t nr = rstart.size();
    rstart.push_back(nq);
    // The runs by block (a counting sort), and each block's corners.
    std::vector<size_t> bfirst(nb + 1, 0), load(nb, 0);
    for (size_t k = 0; k < nr; ++k) {
      ++bfirst[rblock[k] + 1];
      load[rblock[k]] += rstart[k + 1] - rstart[k];
    }
    for (size_t b = 0; b < nb; ++b) bfirst[b + 1] += bfirst[b];
    std::vector<size_t> order(nr), at(bfirst.begin(), bfirst.end() - 1);
    for (size_t k = 0; k < nr; ++k) order[at[rblock[k]]++] = k;
    // The tasks: QW entries [lo, hi), their corner ranges segs[s0, s1),
    // and the buffer they sum into (SIZE_MAX: QW itself).
    struct Task {
      size_t lo, hi, s0, s1, buf;
    };
    std::vector<Task> tasks;
    std::vector<std::pair<size_t, size_t>> segs;
    struct Heavy {
      size_t lo, hi, t0, t1;
    };
    std::vector<Heavy> heavy;
    size_t nbuf = 0;
    const size_t target = (nq + parallel::kChunks - 1) / parallel::kChunks;
    {
      size_t acc = 0, b0 = 0;
      const auto close = [&](size_t b1) {
        if (b1 == b0) return;
        Task t{b0 << sh, std::min(nw, b1 << sh), segs.size(), 0, SIZE_MAX};
        for (size_t k = bfirst[b0]; k < bfirst[b1]; ++k)
          segs.push_back({rstart[order[k]], rstart[order[k] + 1]});
        t.s1 = segs.size();
        tasks.push_back(t);
        acc = 0;
      };
      for (size_t b = 0; b < nb; ++b) {
        if (load[b] > target) {
          close(b);
          const size_t lo = b << sh, hi = std::min(nw, (b + 1) << sh);
          Heavy h{lo, hi, tasks.size(), 0};
          size_t room = target;
          Task t{lo, hi, segs.size(), 0, nbuf++};
          for (size_t k = bfirst[b]; k < bfirst[b + 1]; ++k) {
            size_t i = rstart[order[k]];
            const size_t e = rstart[order[k] + 1];
            while (i < e) {
              const size_t m = std::min(room, e - i);
              segs.push_back({i, i + m});
              i += m;
              room -= m;
              if (room == 0) {
                t.s1 = segs.size();
                tasks.push_back(t);
                t = Task{lo, hi, segs.size(), 0, nbuf++};
                room = target;
              }
            }
          }
          t.s1 = segs.size();
          if (t.s1 > t.s0) {
            tasks.push_back(t);
          } else {
            --nbuf;
          }
          h.t1 = tasks.size();
          heavy.push_back(h);
          b0 = b + 1;
          continue;
        }
        acc += load[b];
        if (acc >= target) {
          close(b + 1);
          b0 = b + 1;
        }
      }
      close(nb);
    }
    const size_t blen = size_t(1) << sh;
    std::vector<Elt> bufs(nbuf * blen);
    if (GkrTrace::on())
      GkrTrace::extra() = "runs=" + std::to_string(nr) + " tasks=" +
                          std::to_string(tasks.size()) + " heavy=" +
                          std::to_string(heavy.size()) + " pieces=" +
                          std::to_string(nbuf);
    Elt* qw = QW.data();
    parallel::for_each(tasks.size(), 1, [&](size_t k) {
      const Task& t = tasks[k];
      Elt* out = t.buf == SIZE_MAX ? qw + t.lo : bufs.data() + t.buf * blen;
      std::fill(out, out + (t.hi - t.lo), Elt{});
      for (size_t j = t.s0; j < t.s1; ++j)
        for (size_t i = segs[j].first; i < segs[j].second; ++i) {
          const corner_t p0(hc[i].h[hand]);
          const corner_t p1(hc[i].h[ohand]);
          F.add(out[p0 - t.lo], F.mulf(vc[i].v, w[p1]));
        }
    });
    for (const Heavy& h : heavy) {
      const size_t len = h.hi - h.lo;
      std::copy(bufs.data() + tasks[h.t0].buf * blen,
                bufs.data() + tasks[h.t0].buf * blen + len, qw + h.lo);
      for (size_t k = h.t0 + 1; k < h.t1; ++k) {
        const Elt* src = bufs.data() + tasks[k].buf * blen;
        for (size_t i = 0; i < len; ++i) F.add(qw[h.lo + i], src[i]);
      }
    }
  }

  // now
  //
  //   SUM = \sum_{l,r} eq0 Q[l,r] Wl[l] Wr[r]
  //       = \sum_{l} eq0 QW[l] W[l]
  //
  // having precomputed QW[l] = \sum_r Q[l, r] Wl[l], and renaming
  // Wr to W.
  //
  // Return the quadratic polynomial p(t) that represents what SUM
  // will be after binding l to t in Q and Wl.
  //
  // The pairs per chunk of evaluations below which splitting does not pay
  // (measured): 1024 in odd characteristic, 4096 in characteristic two.
  static constexpr size_t kEvalsGrain = Field::kCharacteristicTwo ? 4096 : 1024;
  WPoly evaluations(size_t n, const Elt& eq0, const Elt* QW, const Elt* W,
                    const Elt& sum, const Field& F) {
    // Compute the polynomial coefficients, and multiply the coefficients.
    size_t nodd = n / 2;

    // Compute the coefficients of p(t) = a0 + a1*t + a2*t^2, but we
    // don't need to compute a1 since we reconstruct it at the end
    // from sum.
    // One pair of partial sums per fixed chunk (util/parallel.h), summed in
    // chunk order.
    // At least kEvalsGrain pairs per chunk (measured break-even).
    const size_t grain =
        std::max<size_t>(kEvalsGrain, parallel::grain_for(nodd, parallel::kChunks));
    std::vector<std::array<Elt, 2>> part(parallel::chunks(nodd, grain));
    parallel::for_chunks(nodd, grain, [&](size_t b, size_t e) {
      Accum p0{}, p2{};
      for (size_t i = b; i < e; i++) {
        Elt qw0 = QW[2 * i];
        Elt qw1 = QW[2 * i + 1];
        Elt w0 = W[2 * i];
        Elt w1 = W[2 * i + 1];

        F.mac(p0, qw0, w0);
        Elt dqw = F.subf(qw1, qw0);
        Elt dw = F.subf(w1, w0);
        F.mac(p2, dqw, dw);
      }
      part[b / grain] = {F.reduce(p0), F.reduce(p2)};
    });
    Accum a0{}, a2{};
    Elt s0 = F.zero(), s2 = F.zero();
    for (const auto &x : part) {
      F.add(s0, x[0]);
      F.add(s2, x[1]);
    }
    F.mac(a0, s0, F.one());
    F.mac(a2, s2, F.one());
    if (2 * nodd < n) {
      size_t i = nodd;
      Elt qw0 = QW[2 * i];
      Elt w0 = W[2 * i];

      F.mac(a0, qw0, w0);
      F.mac(a2, qw0, w0);
    }

    WPoly coef;
    coef[0] = F.mulf(eq0, F.reduce(a0));
    coef[2] = F.mulf(eq0, F.reduce(a2));
    // SUM = P(0) + P(1) = 2*C0 + C1 + C2. Reconstruct C1.
    coef[1] = sum;
    F.sub(coef[1], coef[0]);
    F.sub(coef[1], coef[0]);
    F.sub(coef[1], coef[2]);

    // evaluate at the standard points
    WPoly evals{};
    for (int k = 0; k < 3; ++k) {
      evals[k] = coef.eval_monomial(F.poly_evaluation_point(k), F);
    }

    return evals;
  }

  // Now  SUM = \sum_{c,l,r} EQ[c] Q[l,r] W[l,c] W[r,c]
  //
  // Return the polynomial p(t) that represents what SUM
  // will be after binding c to t in Q and W.  Since p(t) is cubic
  // we return its values at four points.
  //
  // Compute the polynomial in the monomial basis, but since
  // we know that sum = p(0) + p(1), we can skip the computation
  // of coef[1], which we reconstruct at the end.  coef[2] would
  // work as well.
  //
  CPoly evaluations_c(const Eqs<Field>* EQ, const Dense<Field>* W,
                      const HQuad<Field>* HQUAD, const Elt& sum,
                      const Field& F) {
    // One triple of partial sums per fixed chunk of corners
    // (util/parallel.h), summed in chunk order.
    const size_t nq = HQUAD->n_;
    const size_t grain = std::max<size_t>(256, parallel::grain_for(nq, parallel::kChunks));
    std::vector<std::array<Elt, 3>> part(parallel::chunks(nq, grain));
    parallel::for_chunks(nq, grain, [&](size_t cb, size_t ce) {
    Accum acc[4]{};
    for (index_t i = index_t(cb); i < index_t(ce); i++) {
      const corner_t r(HQUAD->hc_[i].h[0]);
      const corner_t l(HQUAD->hc_[i].h[1]);
      const Elt& vc = HQUAD->vc_[i].v;

      const Elt* wr_v = &W->v_[r * W->n0_];
      const Elt* wl_v = &W->v_[l * W->n0_];

      Accum l0{}, l2{}, l3{};

      size_t nodd = W->n0_ / 2;
      for (corner_t c = 0; c < nodd; ++c) {
        Elt eq0 = EQ->at(2 * c);
        Elt eq1 = EQ->at(2 * c + 1);
        Elt wr0 = wr_v[2 * c];
        Elt wr1 = wr_v[2 * c + 1];
        Elt wl0 = wl_v[2 * c];
        Elt wl1 = wl_v[2 * c + 1];

        Elt a0 = eq0, a1 = F.subf(eq1, eq0);
        Elt b0 = wr0, b1 = F.subf(wr1, wr0);
        Elt c0 = wl0, c1 = F.subf(wl1, wl0);

        // Letting a(t) = a0 + a1 t, and similarly for b(t) and d(t),
        // compute d0, d1, and d2 via Karatsuba convolution.
        // This is simlper than usual because a0 + a1 = eq1 and
        // b0 + b1 = wr1.
        Elt d0 = F.mulf(a0, b0);
        Elt d2 = F.mulf(a1, b1);
        Elt d1 = F.mulf(eq1, wr1);
        F.sub(d1, d0);
        F.sub(d1, d2);

        // 2x3 convolution into the accumulators, but skip the
        // [1] output.
        F.mac(l0, d0, c0);
        F.mac(l2, d1, c1);
        F.mac(l2, d2, c0);
        F.mac(l3, d2, c1);
      }

      if (2 * nodd < W->n0_) {
        size_t c = nodd;
        Elt eq0 = EQ->at(2 * c);
        Elt wr0 = wr_v[2 * c];
        Elt wl0 = wl_v[2 * c];

        Elt d0 = F.mulf(eq0, wr0);
        Elt three_wl0 = F.addf(wl0, F.addf(wl0, wl0));

        F.mac(l0, d0, wl0);
        F.mac(l2, d0, three_wl0);
        F.mac(l3, d0, F.negf(wl0));
      }

      F.mac(acc[0], F.reduce(l0), vc);
      F.mac(acc[2], F.reduce(l2), vc);
      F.mac(acc[3], F.reduce(l3), vc);
    }
    part[cb / grain] = {F.reduce(acc[0]), F.reduce(acc[2]), F.reduce(acc[3])};
    });

    CPoly coefs;
    coefs[0] = F.zero();
    coefs[2] = F.zero();
    coefs[3] = F.zero();
    for (const auto &x : part) {
      F.add(coefs[0], x[0]);
      F.add(coefs[2], x[1]);
      F.add(coefs[3], x[2]);
    }
    // SUM = P(0) + P(1) = 2*C0 + C1 + C2 + C3.  Reconstruct C1.
    coefs[1] = sum;
    F.sub(coefs[1], coefs[0]);
    F.sub(coefs[1], coefs[0]);
    F.sub(coefs[1], coefs[2]);
    F.sub(coefs[1], coefs[3]);

    // evaluate at the standard points
    CPoly evals_c{};
    for (int k = 0; k < 4; ++k) {
      evals_c[k] = coefs.eval_monomial(F.poly_evaluation_point(k), F);
    }
    return evals_c;
  }
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_SUMCHECK_PROVER_LAYERS_H_
