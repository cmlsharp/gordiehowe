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
// Modified 2026 by Chad Sharp and Paul Grubbs: hash-generic verifier with list-radius low-degree test, subfield-row check and caller-supplied constraint accumulator

#ifndef PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_VERIFIER_H_
#define PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_VERIFIER_H_

#include <stddef.h>

#include <array>
#include <functional>
#include <memory>
#include <vector>

#include "algebra/blas.h"
#include "ligero/ligero_param.h"
#include "ligero/ligero_transcript.h"
#include "merkle/merkle_commitment.h"
#include "random/transcript.h"
#include "util/crypto.h"
#include "util/parallel.h"
#include "util/prover_profile.h"

namespace proofs {
template <class Field, class InterpolatorFactory, class Hash = UpstreamHash>
class LigeroVerifier {
  using Elt = typename Field::Elt;
  // The phase timers (util/prover_profile.h) name each part
  // of verify() by the field's characteristic, bin.v.ligero.<part> or
  // odd.v.ligero.<part>. The parts are disjoint and cover verify(): the
  // transcript replay (transcript); the checks at the opened columns, which
  // are the Merkle paths (merkle), the subfield rows' entries (subfield),
  // the low-degree combination of the columns (ldt.columns), the masks
  // (masks), the linear test's combination of the columns (dot.columns)
  // and the quadratic test's (quad.columns); the linear constraints'
  // combination (rows) and its rows evaluated at the opened columns
  // (dot.encode); and the responses evaluated at the opened columns and
  // compared (ldt.response, dot.response, quad.response).
  static const char* key(const char* bin, const char* odd) {
    return Field::kCharacteristicTwo ? bin : odd;
  }

 public:
  static void receive_commitment(
      const LigeroCommitment<Field, Hash>& commitment,
      BasicTranscript<Hash>& ts) {
    // P -> V
    LigeroTranscript<Field>::write_commitment(commitment, ts);
  }

  // See LigeroProver::Accumulator -- the verifier applies the identical one.
  using Accumulator = std::function<void(Elt* A, const Elt* alphal)>;

  // List-radius Ligero: the commit round after the commitment, as
  // LigeroProver::ldt_commit.  Draws u_ldt (LDT_REPS x NLDT elements,
  // repetition-major) into U_LDT and absorbs the proof's y_ldt (LDT_REPS x
  // BLOCK elements); verify() then takes U_LDT.
  static void receive_ldt(const LigeroParam<Field, Hash>& p,
                          const LigeroProof<Field, Hash>& proof,
                          BasicTranscript<Hash>& ts, std::vector<Elt>& u_ldt,
                          const Field& F) {
    check(p.mode.list_radius, "receive_ldt needs list-radius Ligero");
    check(proof.y_ldt.size() == p.mode.ldt_reps * p.block,
          "receive_ldt: the proof's low-degree responses");
    u_ldt.resize(p.mode.ldt_reps * p.nldt);

    // V -> P
    LigeroTranscript<Field>::gen_uldt(u_ldt.data(), p, ts, F);

    // P -> V
    ts.write(&proof.y_ldt[0], 1, p.mode.ldt_reps * p.block, F);
  }

  // SUBFIELD_WROWS, if nonzero, makes subfield membership of the first
  // SUBFIELD_WROWS witness rows part of the statement: every opened entry of
  // those rows must lie in the subfield.  Without it, a subfield row is only a
  // serialization convenience and the prover may commit any field values
  // there.  With it, a row that is not a subfield codeword is caught unless
  // every opened column lands where it happens to take subfield values: the
  // evaluation domain lies in the subfield, so such a row agrees with a
  // subfield codeword on fewer than BLOCK positions (the subfield subcode of a
  // Reed-Solomon code over a subfield domain is Reed-Solomon over the
  // subfield).  Callers that rely on subfield values for soundness, such as
  // packed bits, must set it; everyone else leaves it zero.
  static bool verify(const char** why, const LigeroParam<Field, Hash>& p,
                     const LigeroCommitment<Field, Hash>& commitment,
                     const LigeroProof<Field, Hash>& proof,
                     BasicTranscript<Hash>& ts, size_t nl, size_t nllterm,
                     const LigeroLinearConstraint<Field> llterm[/*nllterm*/],
                     const Elt b[/*nl*/],
                     const LigeroQuadraticConstraint lqc[/*nq*/],
                     const InterpolatorFactory& interpolator, const Field& F,
                     const Accumulator* accum = nullptr,
                     size_t subfield_wrows = 0,
                     const std::vector<Elt>* u_ldt_received = nullptr) {
    if (why == nullptr) {
      return false;
    }
    auto transcript = std::make_unique<profiling::Scope>(
        key("bin.v.ligero.transcript", "odd.v.ligero.transcript"));
    // List-radius Ligero takes u_ldt from receive_ldt.
    if (p.mode.list_radius != (u_ldt_received != nullptr) ||
        (u_ldt_received != nullptr &&
         u_ldt_received->size() != p.mode.ldt_reps * p.nldt) ||
        proof.y_ldt.size() != p.mode.ldt_reps * p.block) {
      *why = "low-degree commit round missing or unexpected";
      return false;
    }

    std::vector<Elt> u_ldt(p.mode.ldt_reps * p.nldt);
    std::vector<Elt> alphal(nl);
    std::vector<std::array<Elt, 3>> alphaq(p.nq);
    std::vector<Elt> u_quad(p.nqtriples);
    std::vector<size_t> idx(p.nreq);

    // Replay the protocol first in order to compute all the
    // challenges.  In particular, we need IDX before we can do
    // anything useful.

    // The enclosing protocol has already bound the statement into ts.

    // V -> P
    if (u_ldt_received != nullptr) {
      u_ldt = *u_ldt_received;
    } else {
      LigeroTranscript<Field>::gen_uldt(&u_ldt[0], p, ts, F);
    }

    // V -> P
    LigeroTranscript<Field>::gen_alphal(nl, &alphal[0], ts, F);
    LigeroTranscript<Field>::gen_alphaq(&alphaq[0], p, ts, F);

    // V -> P
    LigeroTranscript<Field>::gen_uquad(&u_quad[0], p, ts, F);

    // P -> V (y_ldt is already absorbed with list-radius Ligero)
    if (u_ldt_received == nullptr) ts.write(&proof.y_ldt[0], 1, p.block, F);
    ts.write(&proof.y_dot[0], 1, p.dblock, F);
    ts.write(&proof.y_quad_0[0], 1, p.r, F);
    ts.write(&proof.y_quad_2[0], 1, p.dblock - p.block, F);

    // V -> P
    LigeroTranscript<Field>::gen_idx(&idx[0], p, ts, F);

    // The last challenge point: reject if any point overran its stream
    // budget.
    if (ts.exhausted()) {
      *why = "Fiat-Shamir challenge stream budget exceeded";
      return false;
    }

    transcript.reset();

    {
      profiling::Scope sc(key("bin.v.ligero.merkle", "odd.v.ligero.merkle"));
      if (!merkle_check(p, commitment, proof, &idx[0], F)) {
        *why = "merkle_check failed";
        return false;
      }
    }

    {
      profiling::Scope sc(
          key("bin.v.ligero.subfield", "odd.v.ligero.subfield"));
      if (!subfield_check(p, proof, subfield_wrows, F)) {
        *why = "subfield_check failed";
        return false;
      }
    }

    if (!low_degree_check(p, proof, &idx[0], &u_ldt[0], interpolator, F)) {
      *why = "low_degree_check failed";
      return false;
    }

    // The masks at the opened columns: the IDOT and IQUAD rows, or the
    // recombined split pieces.
    std::vector<Elt> mask_dot(p.nreq), mask_quad(p.nreq);
    {
      profiling::Scope sc(key("bin.v.ligero.masks", "odd.v.ligero.masks"));
      open_masks(p, proof, &idx[0], &mask_dot[0], &mask_quad[0], interpolator,
                 F);
    }

    {
      // linear check
      std::vector<Elt> A(p.nwqrow * p.w);

      {
        profiling::Scope sc(key("bin.v.ligero.rows", "odd.v.ligero.rows"));
        LigeroCommon<Field>::inner_product_vector(&A[0], p, nl, nllterm,
                                                  llterm, &alphal[0], lqc,
                                                  &alphaq[0], F);
        if (accum != nullptr) {
          // Nested in the rows phase; its key has no ".v." so that the
          // outermost verifier keys still add up (VerifyPhases.SumToTotal).
          profiling::Scope acc(key("bin.ligero_rows.accumulate",
                                    "odd.ligero_rows.accumulate"));
          (*accum)(&A[0], &alphal[0]);
        }
      }

      if (!dot_check(p, proof, &idx[0], &A[0], &mask_dot[0], interpolator,
                     F)) {
        *why = "dot_check failed";
        return false;
      }

      // check the putative value of the inner product
      profiling::Scope sc(
          key("bin.v.ligero.dot.response", "odd.v.ligero.dot.response"));
      Elt want_dot = Blas<Field>::dot(nl, b, 1, &alphal[0], 1, F);
      Elt proof_dot = Blas<Field>::dot1(p.w, &proof.y_dot[p.r], 1, F);
      if (want_dot != proof_dot) {
        *why = "wrong dot product";
        return false;
      }
    }

    if (!quadratic_check(p, proof, &idx[0], &u_quad[0], &mask_quad[0],
                         interpolator, F)) {
      *why = "quadratic_check failed";
      return false;
    }

    *why = "ok";
    return true;
  }

 private:
  static void interpolate_req_columns(Elt yp[/*nreq*/],
                                      const LigeroParam<Field, Hash>& p,
                                      size_t ylen,
                                      const Elt y[/*ylen*/],
                                      const size_t idx[/*nreq*/],
                                      const InterpolatorFactory& interpolator,
                                      const Field& F) {
    const auto interpy = interpolator.make(ylen, p.block_enc);
    std::vector<Elt> yext(p.block_enc);
    Blas<Field>::copy(ylen, &yext[0], 1, y, 1);
    interpy->interpolate(&yext[0]);
    Blas<Field>::gather(p.nreq, &yp[0], &yext[p.dblock], idx);
  }

  // The dot-product and quadratic masks at the opened columns.  Split masks
  // recombine A_j + Y_j^(BLOCK - NREQ) C_j + Y_j^BLOCK B_j from the opened
  // piece rows at the column's normalized point Y_j.
  static void open_masks(const LigeroParam<Field, Hash>& p,
                         const LigeroProof<Field, Hash>& proof,
                         const size_t idx[/*nreq*/], Elt dot[/*nreq*/],
                         Elt quad[/*nreq*/],
                         const InterpolatorFactory& interpolator,
                         const Field& F) {
    if (!p.mode.split()) {
      Blas<Field>::copy(p.nreq, dot, 1, &proof.req_at(p.idot, 0), 1);
      Blas<Field>::copy(p.nreq, quad, 1, &proof.req_at(p.iquad, 0), 1);
      return;
    }
    const std::vector<Elt> y =
        LigeroCommon<Field>::split_points(p, interpolator, F);
    for (size_t j = 0; j < p.nreq; ++j) {
      Elt lo, hi;
      LigeroCommon<Field>::split_shifts(lo, hi, y[p.dblock + idx[j]], p, F);
      for (size_t m = 0; m < 2; ++m) {
        const size_t ia = p.ipiece + 3 * m;
        Elt v = proof.req_at(ia, j);
        F.add(v, F.mulf(lo, proof.req_at(ia + 1, j)));
        F.add(v, F.mulf(hi, proof.req_at(ia + 2, j)));
        (m == 0 ? dot : quad)[j] = v;
      }
    }
  }

  static bool merkle_check(const LigeroParam<Field, Hash>& p,
                           const LigeroCommitment<Field, Hash>& commitment,
                           const LigeroProof<Field, Hash>& proof,
                           const size_t idx[/*nreq*/], const Field& F) {
    auto updhash = [&](size_t r, Hash& sha) {
      LigeroCommon<Field>::column_hash(p.nrow, &proof.req_at(0, r), p.nreq, sha,
                                       F);
    };

    return BasicMerkleCommitmentVerifier<Hash>::verify(p.block_enc - p.dblock,
                                            commitment.root, proof.merkle, idx,
                                            p.nreq, updhash);
  }

  static bool subfield_check(const LigeroParam<Field, Hash>& p,
                             const LigeroProof<Field, Hash>& proof,
                             size_t subfield_wrows, const Field& F) {
    if (subfield_wrows > p.nwrow) {
      return false;
    }
    for (size_t i = 0; i < subfield_wrows; ++i) {
      for (size_t j = 0; j < p.nreq; ++j) {
        if (!F.in_subfield(proof.req_at(i + p.iw, j))) {
          return false;
        }
      }
    }
    return true;
  }

  static bool low_degree_check(const LigeroParam<Field, Hash>& p,
                               const LigeroProof<Field, Hash>& proof,
                               const size_t idx[/*nreq*/],
                               const Elt u_ldt[/*ldt_reps, nldt*/],
                               const InterpolatorFactory& interpolator,
                               const Field& F) {
    // Every repetition j at every opened column: ILDT_j with coefficient 1
    // and the low-degree rows with u_ldt[j], against response j.
    for (size_t j = 0; j < p.mode.ldt_reps; ++j) {
      const Elt* u = &u_ldt[j * p.nldt];
      std::vector<Elt> yc(p.nreq);
      auto sc = std::make_unique<profiling::Scope>(
          key("bin.v.ligero.ldt.columns", "odd.v.ligero.ldt.columns"));

      // the ILDT_j blinding row with coefficient 1
      Blas<Field>::copy(p.nreq, &yc[0], 1, &proof.req_at(p.ildt + j, 0), 1);

      // all remaining rows with coefficient u[]
      for (size_t i = 0; i < p.nldt; ++i) {
        Blas<Field>::axpy(p.nreq, &yc[0], 1, u[i], &proof.req_at(i + p.iw, 0),
                          1, F);
      }
      sc.reset();

      profiling::Scope response(
          key("bin.v.ligero.ldt.response", "odd.v.ligero.ldt.response"));
      std::vector<Elt> yp(p.nreq);
      interpolate_req_columns(&yp[0], p, p.block, &proof.y_ldt[j * p.block],
                              idx, interpolator, F);

      if (!Blas<Field>::equal(p.nreq, &yp[0], 1, &yc[0], 1, F)) {
        return false;
      }
    }

    return true;
  }

  static bool dot_check(const LigeroParam<Field, Hash>& p,
                        const LigeroProof<Field, Hash>& proof,
                        const size_t idx[/*nreq*/], const Elt A[/*nwqrow, w*/],
                        const Elt mask[/*nreq*/],
                        const InterpolatorFactory& interpolator,
                        const Field& F) {
    std::vector<Elt> yc(p.nreq);
    // The linear test's rows evaluated at the opened columns, row-major
    // [nwqrow][nreq]: each row encoded, then gathered at IDX.
    std::vector<Elt> Areq(p.nwqrow * p.nreq);
    // One partial per fixed chunk of rows, each chunk with its own
    // interpolator (util/parallel.h).
    const size_t grain = parallel::grain_for(p.nwqrow, parallel::kChunks);

    {
      profiling::Scope sc(
          key("bin.v.ligero.dot.encode", "odd.v.ligero.dot.encode"));
      parallel::for_chunks(p.nwqrow, grain, [&](size_t b, size_t e) {
        const auto interpA = interpolator.make(p.block, p.block_enc);
        std::vector<Elt> Aext(p.block_enc);
        for (size_t i = b; i < e; ++i) {
          LigeroCommon<Field>::layout_Aext(&Aext[0], p, i, &A[0], F);
          interpA->interpolate(&Aext[0]);
          Blas<Field>::gather(p.nreq, &Areq[i * p.nreq], &Aext[p.dblock], idx);
        }
      });
    }

    {
      profiling::Scope sc(
          key("bin.v.ligero.dot.columns", "odd.v.ligero.dot.columns"));
      // the dot-product mask with coefficient 1
      Blas<Field>::copy(p.nreq, &yc[0], 1, mask, 1);

      // Accumulate z += A[j] \otimes W[j], one partial per chunk of rows,
      // summed in chunk order.
      std::vector<std::vector<Elt>> part(parallel::chunks(p.nwqrow, grain));
      parallel::for_chunks(p.nwqrow, grain, [&](size_t b, size_t e) {
        auto &v = part[b / grain];
        v.assign(p.nreq, F.zero());
        for (size_t i = b; i < e; ++i) {
          Blas<Field>::vaxpy(p.nreq, v.data(), 1, &Areq[i * p.nreq], 1,
                             &proof.req_at(i + p.iw, 0), 1, F);
        }
      });
      for (const auto &v : part)
        for (size_t j = 0; j < p.nreq; ++j) F.add(yc[j], v[j]);
    }

    profiling::Scope sc(
        key("bin.v.ligero.dot.response", "odd.v.ligero.dot.response"));
    std::vector<Elt> yp(p.nreq);
    interpolate_req_columns(&yp[0], p, p.dblock, &proof.y_dot[0], idx,
                            interpolator, F);

    if (!Blas<Field>::equal(p.nreq, &yp[0], 1, &yc[0], 1, F)) {
      return false;
    }
    return true;
  }

  static bool quadratic_check(const LigeroParam<Field, Hash>& p,
                              const LigeroProof<Field, Hash>& proof,
                              const size_t idx[/*nreq*/],
                              const Elt u_quad[/*nqtriples*/],
                              const Elt mask[/*nreq*/],
                              const InterpolatorFactory& interpolator,
                              const Field& F) {
    std::vector<Elt> yc(p.nreq);

    {
      profiling::Scope sc(
          key("bin.v.ligero.quad.columns", "odd.v.ligero.quad.columns"));
      // the quadratic-test mask with coefficient 1
      Blas<Field>::copy(p.nreq, &yc[0], 1, mask, 1);

      std::vector<Elt> tmp(p.nreq);
      size_t iqx = p.iq;
      size_t iqy = iqx + p.nqtriples;
      size_t iqz = iqy + p.nqtriples;

      // all quadratic triples with coefficient u_ldt[]
      for (size_t i = 0; i < p.nqtriples; ++i) {
        // yc += u_quad[i] * (z[i] - x[i] * y[i])

        // tmp = z[i]
        Blas<Field>::copy(p.nreq, &tmp[0], 1, &proof.req_at(iqz + i, 0), 1);

        // tmp -= x[i] \otimes y[i]
        Blas<Field>::vymax(p.nreq, &tmp[0], 1, &proof.req_at(iqx + i, 0), 1,
                           &proof.req_at(iqy + i, 0), 1, F);

        // yc += u_quad[i] * tmp
        Blas<Field>::axpy(p.nreq, &yc[0], 1, u_quad[i], &tmp[0], 1, F);
      }
    }

    profiling::Scope sc(
        key("bin.v.ligero.quad.response", "odd.v.ligero.quad.response"));
    // reconstruct y_quad from the two parts in the proof
    std::vector<Elt> yquad(p.dblock);
    Blas<Field>::copy(p.r, &yquad[0], 1, &proof.y_quad_0[0], 1);
    Blas<Field>::clear(p.w, &yquad[p.r], 1, F);
    Blas<Field>::copy(p.dblock - p.block, &yquad[p.block], 1,
                      &proof.y_quad_2[0], 1);

    // interpolate y_quad at the opened columns
    std::vector<Elt> yp(p.nreq);
    interpolate_req_columns(&yp[0], p, p.dblock, &yquad[0], idx, interpolator,
                            F);

    if (!Blas<Field>::equal(p.nreq, &yp[0], 1, &yc[0], 1, F)) {
      return false;
    }
    return true;
  }
};
}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_VERIFIER_H_
