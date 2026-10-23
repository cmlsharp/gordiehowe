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
// Modified 2026 by Chad Sharp and Paul Grubbs: hash-templated prover with list-radius LDT commit round, split masks, LDT repetitions, parallel row encoding and Merkle build, and a caller's inner-product buffer

#ifndef PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_PROVER_H_
#define PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_PROVER_H_

#include <stddef.h>

#include <algorithm>
#include <array>
#include <cstring>
#include <functional>
#include <vector>

#include "algebra/blas.h"
#include "ligero/ligero_param.h"
#include "ligero/ligero_transcript.h"
#include "merkle/merkle_commitment.h"
#include "util/prover_profile.h"
#include "random/random.h"
#include "random/transcript.h"
#include "util/crypto.h"
#include "util/panic.h"
#include "util/parallel.h"

namespace proofs {
template <class Field, class InterpolatorFactory, class Hash = UpstreamHash>
class LigeroProver {
  using Elt = typename Field::Elt;

public:
  explicit LigeroProver(const LigeroParam<Field, Hash> &p)
      : p_(p), mc_(p.block_enc - p.dblock), tableau_(p.nrow * p.block_enc) {}

  // The SUBFIELD_BOUNDARY parameter is kind of a hack.
  //
  // Most, but not all, witnesses in W[] are known statically to be in
  // the subfield of Field, for example because they are bits or
  // bit-plucked values in the subfield.  For zero-knowledge, for
  // these witnesses, it suffices to choose blinding randomness in the
  // subfield, which yields a shorter proof since most column openings
  // are fully in the subfield.  The problem is now to distinguish
  // subfield witnesses from field witnesses.
  //
  // In the fullness of time we should have a compiler with typing
  // information (field vs subfield) of all input wires.  For now
  // we implement the following hack: W[i] is in the subfield for
  // i < SUBFIELD_BOUNDARY, and in the full field otherwise.
  // If you don't know better, set SUBFIELD_BOUNDARY = 0 which
  // trivially works for any input.
  void commit(LigeroCommitment<Field, Hash> &commitment,
              BasicTranscript<Hash> &ts, const Elt W[/*p_.nw*/], const size_t subfield_boundary,
              const LigeroQuadraticConstraint lqc[/*nq*/],
              const InterpolatorFactory &interpolator, RandomEngine &rng,
              const Field &F) {
    commit_compute(commitment, W, subfield_boundary, lqc, interpolator, rng,
                   F);
    commit_write(commitment, ts);
  }

  // The commitment's computation (layout, encoding, Merkle tree), which
  // touches no transcript.
  void commit_compute(LigeroCommitment<Field, Hash> &commitment,
                      const Elt W[/*p_.nw*/], const size_t subfield_boundary,
                      const LigeroQuadraticConstraint lqc[/*nq*/],
                      const InterpolatorFactory &interpolator,
                      RandomEngine &rng, const Field &F) {
    // Paranoid check on the SUBFIELD_BOUNDARY correctness condition
    for (size_t i = 0; i < subfield_boundary; ++i) {
      check(F.in_subfield(W[i]), "element not in subfield");
    }

    // The phase timers (util/prover_profile.h) name each
    // part by the field's characteristic.
    {
      profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.encode" : "odd.ligero.encode");
      layout(W, subfield_boundary, lqc, interpolator, rng, F);
    }
    if (tamper) tamper(tableau_, masks_);

    // Merkle commitment
    auto updhash = [&](size_t j, Hash &sha) {
      LigeroCommon<Field>::column_hash(p_.nrow, &tableau_at(0, j + p_.dblock),
                                       p_.block_enc, sha, F);
    };
    {
      profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.merkle" : "odd.ligero.merkle");
      commitment.root = mc_.commit(updhash, rng);
    }
  }

  // P -> V: the commitment's root.
  void commit_write(const LigeroCommitment<Field, Hash> &commitment,
                    BasicTranscript<Hash> &ts) const {
    LigeroTranscript<Field>::write_commitment(commitment, ts);
  }

  // The enclosing protocol binds its statement into TS before entering this
  // layer. ZkProver does so before GKR; Ligero continues the same transcript.
  // ACCUM, if non-null, adds a caller's contribution directly to the
  // inner-product vector A, instead of the caller materialising its constraints
  // as sparse LLTERM triples.  For a structured family (e.g. an NTT matrix) the
  // triple list is enormous -- n^2 per transform, tens of MB of 32-byte structs
  // written then re-read with random A[] writes -- while the same contribution
  // accumulates with a streaming dense loop.  The caller knows its own row
  // offsets, so the signature is just (A, alphal).
  using Accumulator = std::function<void(Elt *A, const Elt *alphal)>;

  // A test seam (a cheating prover; unset for an honest one): runs between
  // the layout and the commitment, on the tableau [NROW, BLOCK_ENC] and,
  // with split masks, the two masks [DBLOCK] the responses use (the
  // recombination of the piece rows).
  using TamperFn = std::function<void(std::vector<Elt> &tableau,
                                      std::vector<Elt> (&masks)[2])>;
  TamperFn tamper;
  // A test seam (unset for an honest prover): changes the low-degree
  // response before ldt_commit writes it.
  std::function<void(std::vector<Elt> &y_ldt)> tamper_ldt;
  // The inner-product vector's storage, when set: a caller's buffer that
  // keeps its capacity from proof to proof
  // (gordiehowe/compiler/prover_scratch.h).
  parallel::Buffer<Elt> *a_buffer = nullptr;

  // List-radius Ligero (LigeroMode::list_radius): the commit round after the
  // commitment.  V -> P the low-degree challenges u_ldt (LDT_REPS x NLDT
  // elements, repetition-major, one message), then P -> V the low-degree
  // responses y_ldt (LDT_REPS x BLOCK elements, repetition-major, one
  // message), before any other challenge.  An enclosing protocol with
  // several commitments writes every commitment first, then runs each
  // commitment's ldt_commit in order.
  void ldt_commit(LigeroProof<Field, Hash> &proof, BasicTranscript<Hash> &ts,
                  const Field &F) {
    check(p_.mode.list_radius, "ldt_commit needs list-radius Ligero");
    check(!ldt_done_, "ldt_commit runs once");
    profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.ldt" : "odd.ligero.ldt");
    const size_t reps = p_.mode.ldt_reps;
    std::vector<Elt> u_ldt(reps * p_.nldt);

    // V -> P
    LigeroTranscript<Field>::gen_uldt(u_ldt.data(), p_, ts, F);
    for (size_t j = 0; j < reps; ++j)
      low_degree_proof(&proof.y_ldt[j * p_.block], &u_ldt[j * p_.nldt], j, F);
    if (tamper_ldt) tamper_ldt(proof.y_ldt);

    // P -> V
    ts.write(&proof.y_ldt[0], 1, reps * p_.block, F);
    ldt_done_ = true;
  }

  void prove(LigeroProof<Field, Hash> &proof, BasicTranscript<Hash> &ts,
             size_t nl, size_t nllterm,
             const LigeroLinearConstraint<Field> llterm[/*nllterm*/],
             const LigeroQuadraticConstraint lqc[/*nq*/],
             const InterpolatorFactory &interpolator, const Field &F,
             const Accumulator *accum = nullptr) {
    if (p_.mode.list_radius) {
      check(ldt_done_, "list-radius Ligero: ldt_commit before prove");
    } else {
      profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.ldt" : "odd.ligero.ldt");
      std::vector<Elt> u_ldt(p_.nldt);

      // V -> P
      LigeroTranscript<Field>::gen_uldt(u_ldt.data(), p_, ts, F);
      low_degree_proof(proof.y_ldt.data(), u_ldt.data(), 0, F);
    }

    {
      std::vector<Elt> alphal(nl);
      std::vector<std::array<Elt, 3>> alphaq(p_.nq);
      parallel::Buffer<Elt> own_A;
      parallel::Buffer<Elt> &A = a_buffer != nullptr ? *a_buffer : own_A;
      A.assign(p_.nwqrow * p_.w, Elt{});

      // V -> P
      LigeroTranscript<Field>::gen_alphal(nl, alphal.data(), ts, F);
      LigeroTranscript<Field>::gen_alphaq(alphaq.data(), p_, ts, F);

      {
        profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.rows" : "odd.ligero.rows");
        LigeroCommon<Field>::inner_product_vector(A.data(), p_, nl, nllterm,
                                                  llterm, alphal.data(), lqc,
                                                  alphaq.data(), F);
        if (accum != nullptr) {
          (*accum)(A.data(), alphal.data());
        }
      }

      profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.dot" : "odd.ligero.dot");
      dot_proof(proof.y_dot.data(), A.data(), interpolator, F);
    }

    {
      std::vector<Elt> u_quad(p_.nqtriples);

      // V -> P
      LigeroTranscript<Field>::gen_uquad(u_quad.data(), p_, ts, F);
      profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.quad" : "odd.ligero.quad");
      quadratic_proof(proof.y_quad_0.data(), proof.y_quad_2.data(),
                      u_quad.data(), F);
    }

    {
      // P -> V (y_ldt is already written with list-radius Ligero)
      if (!p_.mode.list_radius) ts.write(&proof.y_ldt[0], 1, p_.block, F);
      ts.write(&proof.y_dot[0], 1, p_.dblock, F);
      ts.write(&proof.y_quad_0[0], 1, p_.r, F);
      ts.write(&proof.y_quad_2[0], 1, p_.dblock - p_.block, F);
    }

    {
      std::vector<size_t> idx(p_.nreq);
      // V -> P
      LigeroTranscript<Field>::gen_idx(idx.data(), p_, ts, F);

      // The last challenge point: abort if any point overran its stream
      // budget, before opening any column.
      check(!ts.exhausted(), "Fiat-Shamir challenge stream budget exceeded");

      profiling::Scope sc(Field::kCharacteristicTwo ? "bin.ligero.open" : "odd.ligero.open");
      compute_req(proof, idx.data());

      mc_.open(proof.merkle, idx.data(), p_.nreq);
    }
  }

private:
  Elt &tableau_at(size_t i, size_t j) {
    size_t ld = p_.block_enc;
    return tableau_[i * ld + j];
  }

  // fill t_[i, [0,n)] with random elements
  // If the base_only flag is true, then the random element is chosen from
  // the base field if F is a field extension.
  void random_row(size_t i, size_t n, RandomEngine &rng, const Field &F) {
    if constexpr (Field::kCharacteristicTwo) {
      // Binary-field sampling consumes fixed-width uniform strings. Batch the
      // entropy request, preserving fresh independent randomness for every
      // cell.
      std::vector<uint8_t> bytes(n * Field::kBytes);
      rng.bytes(bytes.data(), bytes.size());
      size_t at = 0;
      for (size_t j = 0; j < n; ++j)
        tableau_at(i, j) = F.sample([&](size_t count, uint8_t *out) {
          check(count <= bytes.size() - at, "binary sample width");
          std::memcpy(out, bytes.data() + at, count);
          at += count;
        });
      check(at == bytes.size(), "binary sample consumption");
    } else {
      for (size_t j = 0; j < n; ++j)
        tableau_at(i, j) = rng.elt(F);
    }
  }

  void random_subfield_row(size_t i, size_t n, RandomEngine &rng,
                           const Field &F) {
    if constexpr (Field::kCharacteristicTwo) {
      std::vector<uint8_t> bytes(n * Field::kSubFieldBytes);
      rng.bytes(bytes.data(), bytes.size());
      size_t at = 0;
      for (size_t j = 0; j < n; ++j)
        tableau_at(i, j) = F.sample_subfield([&](size_t count, uint8_t *out) {
          check(count <= bytes.size() - at, "binary subfield sample width");
          std::memcpy(out, bytes.data() + at, count);
          at += count;
        });
      check(at == bytes.size(), "binary subfield sample consumption");
    } else {
      for (size_t j = 0; j < n; ++j)
        tableau_at(i, j) = rng.subfield_elt(F);
    }
  }

  // generate the ILDT and IDOT blinding rows
  void layout_blinding_rows(const InterpolatorFactory &interpolator,
                            RandomEngine &rng, const Field &F) {
    {
      // blinds of size [BLOCK]
      const auto interp = interpolator.make(p_.block, p_.block_enc);

      // the low-degree blinding rows ILDT_0, ..., ILDT_{LDT_REPS - 1}, in
      // that order (ILDT_0 first, so one repetition draws as before)
      for (size_t j = 0; j < p_.mode.ldt_reps; ++j) {
        random_row(p_.ildt + j, p_.block, rng, F);
        interp->interpolate(&tableau_at(p_.ildt + j, 0));
      }
    }

    // Split masks have no IDOT or IQUAD row (layout_piece_rows).
    if (p_.mode.split()) return;

    {
      // blinds of size [DBLOCK]
      const auto interp = interpolator.make(p_.dblock, p_.block_enc);

      // dot-product blinding row constrained to SUM(W) = 0. First
      // randomize the dblock:
      random_row(p_.idot, p_.dblock, rng, F);

      // Then constrain to sum(W) = 0
      Elt sum = Blas<Field>::dot1(p_.w, &tableau_at(p_.idot, p_.r), 1, F);
      F.sub(tableau_at(p_.idot, p_.r), sum);

      interp->interpolate(&tableau_at(p_.idot, 0));

      // quadratic-test blinding row constrained to W = 0.  First
      // randomize the entire dblock:
      random_row(p_.iquad, p_.dblock, rng, F);

      // Then constrain to W = 0
      Blas<Field>::clear(p_.w, &tableau_at(p_.iquad, p_.r), 1, F);

      interp->interpolate(&tableau_at(p_.iquad, 0));
    }
  }

  // Extends rows FIRST .. FIRST + N - 1 from their first K entries to
  // BLOCK_ENC, SUB[i] (when given) marking a row of the subfield, in
  // parallel chunks of rows (util/parallel.h), each chunk with its own
  // interpolator.
  void interpolate_rows(size_t first, size_t n, size_t k,
                        const InterpolatorFactory &interpolator,
                        const std::vector<char> *sub = nullptr) {
    parallel::for_chunks(
        n, parallel::grain_for(n, parallel::kChunks), [&](size_t b, size_t e) {
          const auto interp = interpolator.make(k, p_.block_enc);
          for (size_t i = b; i < e; ++i) {
            if (sub != nullptr)
              interp->interpolate(&tableau_at(first + i, 0), (*sub)[i] != 0);
            else
              interp->interpolate(&tableau_at(first + i, 0));
          }
        });
  }

  void layout_witness_rows(const Elt W[/*nw*/], size_t subfield_boundary,
                           const InterpolatorFactory &interpolator,
                           RandomEngine &rng, const Field &F) {
    // The rows' random and witness entries first, in row order (the RNG's
    // order), then their extensions in parallel.
    std::vector<char> sub(p_.nwrow);
    // witness row EXTEND([RANDOM[R], WITNESS[W]], BLOCK)
    for (size_t i = 0; i < p_.nwrow; ++i) {
      // TRUE if the entire row is in the subfield
      bool subfield_only = ((i + 1) * p_.w <= subfield_boundary);

      if (subfield_only) {
        random_subfield_row(i + p_.iw, p_.r, rng, F);
      } else {
        random_row(i + p_.iw, p_.r, rng, F);
      }

      // Set the WITNESS columns to zero first, and then
      // overwrite with the witnesses that actually exist
      Blas<Field>::clear(p_.w, &tableau_at(i + p_.iw, p_.r), 1, F);
      size_t max_col = std::min(p_.w, p_.nw - i * p_.w);
      Blas<Field>::copy(max_col, &tableau_at(i + p_.iw, p_.r), 1, &W[i * p_.w],
                        1);
      sub[i] = subfield_only ? 1 : 0;
    }
    interpolate_rows(p_.iw, p_.nwrow, p_.block, interpolator, &sub);
  }

  void layout_quadratic_rows(const Elt W[/*nw*/],
                             const LigeroQuadraticConstraint lqc[/*nq*/],
                             const InterpolatorFactory &interpolator,
                             RandomEngine &rng, const Field &F) {
    // copy the multiplicand witnesses into the quadratic rows
    size_t iqx = p_.iq;
    size_t iqy = iqx + p_.nqtriples;
    size_t iqz = iqy + p_.nqtriples;

    for (size_t i = 0; i < p_.nqtriples; ++i) {
      random_row(iqx + i, p_.r, rng, F);
      random_row(iqy + i, p_.r, rng, F);
      random_row(iqz + i, p_.r, rng, F);

      // clear everything first, then overwrite the witnesses that
      // actually exist
      Blas<Field>::clear(p_.w, &tableau_at(iqx + i, p_.r), 1, F);
      Blas<Field>::clear(p_.w, &tableau_at(iqy + i, p_.r), 1, F);
      Blas<Field>::clear(p_.w, &tableau_at(iqz + i, p_.r), 1, F);

      for (size_t j = 0; j < p_.w && j + i * p_.w < p_.nq; ++j) {
        const auto *l = &lqc[j + i * p_.w];
        check(l->x < p_.nw, "l->x < p_.nw");
        check(l->y < p_.nw, "l->y < p_.nw");
        check(l->z < p_.nw, "l->z < p_.nw");
        check(W[l->z] == F.mulf(W[l->x], W[l->y]),
              "invalid quadratic constraints");
        tableau_at(iqx + i, j + p_.r) = W[l->x];
        tableau_at(iqy + i, j + p_.r) = W[l->y];
        tableau_at(iqz + i, j + p_.r) = W[l->z];
      }
    }
    // The x, y and z rows are consecutive: their extensions in parallel.
    interpolate_rows(iqx, 3 * p_.nqtriples, p_.block, interpolator);
  }

  // The mask of split piece rows IA, IA + 1, IA + 2 (A, C, B) at position
  // i < DBLOCK: A_i + LO_i C_i + HI_i B_i, with LO = Y^(BLOCK - NREQ) and
  // HI = Y^BLOCK.
  Elt split_mask(size_t ia, size_t i, const std::vector<Elt> &lo,
                 const std::vector<Elt> &hi, const Field &F) {
    Elt m = tableau_at(ia, i);
    F.add(m, F.mulf(lo[i], tableau_at(ia + 1, i)));
    F.add(m, F.mulf(hi[i], tableau_at(ia + 2, i)));
    return m;
  }

  // The split piece rows (LigeroMasking::kSplit).  For each mask, the
  // triple (A, C, B) is uniform among the triples whose recombination
  // M = A + Y^(BLOCK - NREQ) C + Y^BLOCK B satisfies the mask's constraint
  // on the witness positions [R, BLOCK): sum zero for IDOT, zero for IQUAD.
  // The map (A, C, B) -> M is linear and onto the polynomials of degree
  // <= 2 BLOCK - 2, so M is distributed as the untested mask row and, given
  // M, the triple is M's block split plus a uniform kernel element.  C and B
  // are uniform; A is uniform except at the witness positions, which the
  // constraint fixes.
  void layout_piece_rows(const InterpolatorFactory &interpolator,
                         RandomEngine &rng, const Field &F) {
    const std::vector<Elt> y =
        LigeroCommon<Field>::split_points(p_, interpolator, F);
    std::vector<Elt> lo(p_.dblock), hi(p_.dblock);
    for (size_t i = 0; i < p_.dblock; ++i)
      LigeroCommon<Field>::split_shifts(lo[i], hi[i], y[i], p_, F);

    const auto interp = interpolator.make(p_.block, p_.block_enc);
    const auto interpB = interpolator.make(p_.block - 1, p_.block_enc);
    for (size_t m = 0; m < 2; ++m) {
      const size_t ia = p_.ipiece + 3 * m, ic = ia + 1, ib = ia + 2;
      random_row(ic, p_.block, rng, F);
      interp->interpolate(&tableau_at(ic, 0));
      random_row(ib, p_.block - 1, rng, F);
      interpB->interpolate(&tableau_at(ib, 0));
      random_row(ia, p_.block, rng, F);
      if (m == 0) {
        // IDOT: the mask sums to zero over the witness positions.
        Elt sum = F.zero();
        for (size_t j = 0; j < p_.w; ++j)
          F.add(sum, split_mask(ia, p_.r + j, lo, hi, F));
        F.sub(tableau_at(ia, p_.r), sum);
      } else {
        // IQUAD: the mask is zero at the witness positions.
        for (size_t j = 0; j < p_.w; ++j) {
          const size_t i = p_.r + j;
          Elt c = F.mulf(lo[i], tableau_at(ic, i));
          F.add(c, F.mulf(hi[i], tableau_at(ib, i)));
          Elt a = F.zero();
          F.sub(a, c);
          tableau_at(ia, i) = a;
        }
      }
      interp->interpolate(&tableau_at(ia, 0));

      // The mask the responses use, at positions [0, DBLOCK).
      masks_[m].resize(p_.dblock);
      for (size_t i = 0; i < p_.dblock; ++i)
        masks_[m][i] = split_mask(ia, i, lo, hi, F);
    }
  }

  void layout(const Elt W[/*nw*/], size_t subfield_boundary,
              const LigeroQuadraticConstraint lqc[/*nq*/],
              const InterpolatorFactory &interpolator, RandomEngine &rng,
              const Field &F) {
    layout_blinding_rows(interpolator, rng, F);
    layout_witness_rows(W, subfield_boundary, interpolator, rng, F);
    layout_quadratic_rows(W, lqc, interpolator, rng, F);
    if (p_.mode.split()) layout_piece_rows(interpolator, rng, F);
  }

  // The mask of the dot-product (M = 0) or quadratic (M = 1) response at
  // positions [0, DBLOCK): the IDOT or IQUAD row, or the split pieces'
  // recombination.
  void mask_row(Elt y[/*dblock*/], size_t m, const Field &F) {
    if (!p_.mode.split()) {
      Blas<Field>::copy(p_.dblock, y, 1,
                        &tableau_at(m == 0 ? p_.idot : p_.iquad, 0), 1);
      return;
    }
    Blas<Field>::copy(p_.dblock, y, 1, masks_[m].data(), 1);
  }

  // ACC (N entries) += sum over rows i in [0, NROWS) of ROW(i, part),
  // ROW adding row i's contribution to the partial PART: one partial per
  // fixed chunk of rows, summed in chunk order (util/parallel.h).
  template <class RowFn>
  void reduce_rows(Elt acc[/*n*/], size_t n, size_t nrows, const Field &F,
                   RowFn row) {
    const size_t grain = parallel::grain_for(nrows, parallel::kChunks);
    const size_t nc = parallel::chunks(nrows, grain);
    std::vector<std::vector<Elt>> part(nc);
    parallel::for_chunks(nrows, grain, [&](size_t b, size_t e) {
      auto &v = part[b / grain];
      v.assign(n, F.zero());
      for (size_t i = b; i < e; ++i) row(i, v.data());
    });
    for (const auto &v : part)
      for (size_t j = 0; j < n; ++j) F.add(acc[j], v[j]);
  }

  // Repetition REP's response: its blinding row ILDT_REP with coefficient
  // 1, and the low-degree rows with its challenge U_LDT.
  void low_degree_proof(Elt y[/*block*/], const Elt u_ldt[/*nldt*/],
                        size_t rep, const Field &F) {
    // ILDT_REP blinding row with coefficient 1
    Blas<Field>::copy(p_.block, y, 1, &tableau_at(p_.ildt + rep, 0), 1);

    // all witness, quadratic and piece rows with coefficient u_ldt[]
    reduce_rows(y, p_.block, p_.nldt, F, [&](size_t i, Elt *v) {
      Blas<Field>::axpy(p_.block, v, 1, u_ldt[i], &tableau_at(i + p_.iw, 0), 1,
                        F);
    });
  }

  void dot_proof(Elt y[/*dblock*/], const Elt A[/*nwqrow, w*/],
                 const InterpolatorFactory &interpolator, const Field &F) {
    const auto interpA = interpolator.make(p_.block, p_.dblock);

    // the dot-product mask with coefficient 1
    mask_row(y, 0, F);

    (void)interpA;
    const size_t grain = parallel::grain_for(p_.nwqrow, parallel::kChunks);
    const size_t nc = parallel::chunks(p_.nwqrow, grain);
    std::vector<std::vector<Elt>> part(nc);
    parallel::for_chunks(p_.nwqrow, grain, [&](size_t b, size_t e) {
      const auto interp = interpolator.make(p_.block, p_.dblock);
      std::vector<Elt> Aext(p_.dblock);
      auto &v = part[b / grain];
      v.assign(p_.dblock, F.zero());
      for (size_t i = b; i < e; ++i) {
        LigeroCommon<Field>::layout_Aext(&Aext[0], p_, i, &A[0], F);
        interp->interpolate(&Aext[0]);

        // Accumulate y += A \otimes W.
        Blas<Field>::vaxpy(p_.dblock, v.data(), 1, &Aext[0], 1,
                           &tableau_at(i + p_.iw, 0), 1, F);
      }
    });
    for (const auto &v : part)
      for (size_t j = 0; j < p_.dblock; ++j) F.add(y[j], v[j]);
  }

  void quadratic_proof(Elt y0[/*r*/], Elt y2[/*dblock - block*/],
                       const Elt u_quad[/*nqtriples*/], const Field &F) {
    std::vector<Elt> y(p_.dblock);
    std::vector<Elt> tmp(p_.dblock);

    // the quadratic-test mask with coefficient 1
    mask_row(&y[0], 1, F);

    size_t iqx = p_.iq;
    size_t iqy = iqx + p_.nqtriples;
    size_t iqz = iqy + p_.nqtriples;

    (void)tmp;
    reduce_rows(&y[0], p_.dblock, p_.nqtriples, F, [&](size_t i, Elt *v) {
      // y += u_quad[i] * (z[i] - x[i] * y[i])
      std::vector<Elt> t(&tableau_at(iqz + i, 0), &tableau_at(iqz + i, 0) + p_.dblock);

      // t -= x[i] \otimes y[i]
      Blas<Field>::vymax(p_.dblock, &t[0], 1, &tableau_at(iqx + i, 0), 1,
                         &tableau_at(iqy + i, 0), 1, F);

      // y += u_quad[i] * t
      Blas<Field>::axpy(p_.dblock, v, 1, u_quad[i], &t[0], 1, F);
    });

    // sanity check: the W part of Y is zero
    bool ok = Blas<Field>::equal0(p_.w, &y[p_.r], 1, F);
    check(ok, "W part is nonzero");

    // extract the first and last parts
    Blas<Field>::copy(p_.r, y0, 1, &y[0], 1);
    Blas<Field>::copy(p_.dblock - p_.block, y2, 1, &y[p_.block], 1);
  }

  void compute_req(LigeroProof<Field, Hash> &proof,
                   const size_t idx[/*nreq*/]) {
    parallel::for_each(p_.nrow, parallel::grain_for(p_.nrow, parallel::kChunks),
                       [&](size_t i) {
      Blas<Field>::gather(p_.nreq, &proof.req_at(i, 0),
                          &tableau_at(i, p_.dblock), idx);
    });
  }

  const LigeroParam<Field, Hash> p_; /* safer to make copy */
  BasicMerkleCommitment<Hash> mc_;
  std::vector<Elt> tableau_ /*[nrow, block_enc]*/;
  bool ldt_done_ = false;
  // Split masks: the dot-product and quadratic masks at [0, DBLOCK).
  std::vector<Elt> masks_[2];
};
} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_LIGERO_LIGERO_PROVER_H_
