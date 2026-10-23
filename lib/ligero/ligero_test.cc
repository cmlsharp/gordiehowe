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
// Modified 2026 by Chad Sharp and Paul Grubbs: tests use a ProofSeed-keyed transcript, no hash_of_llterm, stream-budget exhaustion checks, and a subfield-rows test

#include <stdlib.h>

#include <cstdint>
#include <cstdio>
#include <functional>
#include <memory>
#include <vector>

#include "algebra/blas.h"
#include "algebra/convolution.h"
#include "algebra/fp.h"
#include "algebra/reed_solomon.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "ligero/ligero_param.h"
#include "ligero/ligero_prover.h"
#include "ligero/ligero_verifier.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "util/log.h"
#include "gtest/gtest.h"

namespace proofs {
namespace {

// The seed of one Ligero proof in isolation, shared by its prover and
// verifier transcripts.
ProofSeed test_seed() {
  SecureRandomEngine rng;
  return ProofSeed::draw(rng);
}

template <class Field, class ReedSolomonFactory>
void ligero_test(const ReedSolomonFactory &rs_factory, const Field &F) {
  const ProofSeed sigma = test_seed();
  using Elt = typename Field::Elt;
  set_log_level(INFO);
  static const constexpr size_t nw = 300000;
  static const constexpr size_t nq = 30000;
  static const constexpr size_t nreq = 189;
  static const constexpr size_t nl = 7;
  static const constexpr size_t kLargeBudget = size_t{1} << 24;
  LigeroParam<Field> param(nw, nq, /*rateinv=*/4, nreq);
  log(INFO, "%zd %zd %zd %zd %zd %zd\n", param.r, param.w, param.block,
      param.block_enc, param.nrow, param.nqtriples);

  std::vector<Elt> W(nw);
  std::vector<Elt> A(nw);
  for (size_t i = 0; i < nw; ++i) {
    W[i] = F.of_scalar_field(random());
    A[i] = F.of_scalar_field(random());
  }

  // Set up semi-random quadratic constraints.  For simplicity
  // of testing, say that the first NQ odd-index witnesses are
  // the product of two even-index witnesses
  std::vector<LigeroQuadraticConstraint> lqc(nq);
  for (size_t i = 0; i < nq; ++i) {
    lqc[i].z = 2 * i + 1;
    lqc[i].x = 2 * ((random() % nw) / 2);
    lqc[i].y = 2 * ((random() % nw) / 2);
    W[lqc[i].z] = F.mulf(W[lqc[i].x], W[lqc[i].y]);
  }

  // Generate NL linear constraints.
  std::vector<LigeroLinearConstraint<Field>> llterm;
  std::vector<Elt> b(nl);
  Blas<Field>::clear(nl, &b[0], 1, F);
  for (size_t w = 0; w < nw; ++w) {
    LigeroLinearConstraint<Field> term = {
        w % nl, // c
        w,      // w
        A[w],   // k
    };
    llterm.push_back(term);
    F.add(b[term.c], F.mulf(W[w], term.k));
  }

  LigeroCommitment<Field> commitment;
  LigeroProof<Field> proof(&param);

  {
    log(INFO, "start prover");
    SecureRandomEngine rng;
    LigeroProver<Field, ReedSolomonFactory> prover(param);
    Transcript ts((uint8_t *)"test", 4, sigma);
    // 3 * nq = 90000 quadratic challenges in one point exceed the protocol's
    // stream budget, which is sized for the benchmarked constructions.
    ts.set_stream_budget(kLargeBudget);
    prover.commit(commitment, ts, &W[0], /*subfield_boundary=*/0, &lqc[0],
                  rs_factory, rng, F);
    prover.prove(proof, ts, nl, llterm.size(), &llterm[0], &lqc[0], rs_factory,
                 F);
    log(INFO, "end prover");
  }

  {
    log(INFO, "start verifier");
    Transcript ts((uint8_t *)"test", 4, sigma);
    ts.set_stream_budget(kLargeBudget);
    LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                  ts);
    const char *why = "";
    bool ok = LigeroVerifier<Field, ReedSolomonFactory>::verify(
        &why, param, commitment, proof, ts, nl, llterm.size(), &llterm[0],
        &b[0], &lqc[0], rs_factory, F);
    EXPECT_TRUE(ok);
    log(INFO, "end verifier");
  }
}

template <class Field, class RealInterpolator> class BadInterpolator {
public:
  using Elt = typename Field::Elt;
  BadInterpolator(std::unique_ptr<RealInterpolator> real, bool should_fail,
                  size_t n, size_t m)
      : real_(std::move(real)), should_fail_(should_fail), n_(n), m_(m) {}

  void interpolate(Elt y[]) const {
    real_->interpolate(y);
    if (should_fail_ && m_ > n_) {
      Elt first = y[n_];
      for (size_t i = n_; i < m_ - 1; ++i) {
        y[i] = y[i + 1];
      }
      y[m_ - 1] = first;
    }
  }

private:
  std::unique_ptr<RealInterpolator> real_;
  bool should_fail_;
  size_t n_, m_;
};

template <class Field, class RealFactory> class BadReedSolomonFactory {
public:
  BadReedSolomonFactory(const RealFactory &real, int fail_idx)
      : real_(real), fail_idx_(fail_idx), calls_(std::make_shared<int>(0)) {}

  auto make(size_t n, size_t m) const {
    auto real_interp = real_.make(n, m);
    (*calls_)++;
    bool should_fail = (*calls_ == fail_idx_);
    using RealInterpolator = typename decltype(real_interp)::element_type;
    return std::make_unique<BadInterpolator<Field, RealInterpolator>>(
        std::move(real_interp), should_fail, n, m);
  }

private:
  const RealFactory &real_;
  int fail_idx_;
  std::shared_ptr<int> calls_;
};

template <class Field, class ReedSolomonFactory>
void test_ligero_verifier_failures(const ReedSolomonFactory &rs_factory,
                                   const Field &F) {
  const ProofSeed sigma = test_seed();
  using Elt = typename Field::Elt;
  static const constexpr size_t nw = 300;
  static const constexpr size_t nq = 30;
  static const constexpr size_t nreq = 18;
  static const constexpr size_t nl = 7;
  LigeroParam<Field> param(nw, nq, /*rateinv=*/4, nreq);

  std::vector<Elt> W(nw);
  std::vector<Elt> A(nw);
  for (size_t i = 0; i < nw; ++i) {
    W[i] = F.of_scalar_field(random());
    A[i] = F.of_scalar_field(random());
  }

  std::vector<LigeroQuadraticConstraint> lqc(nq);
  for (size_t i = 0; i < nq; ++i) {
    lqc[i].z = 3 * i + 2;
    lqc[i].x = 3 * i;
    lqc[i].y = 3 * i + 1;
    W[lqc[i].z] = F.mulf(W[lqc[i].x], W[lqc[i].y]);
  }

  std::vector<LigeroLinearConstraint<Field>> llterm;
  std::vector<Elt> b(nl);
  Blas<Field>::clear(nl, &b[0], 1, F);
  for (size_t w = 0; w < nw; ++w) {
    LigeroLinearConstraint<Field> term = {w % nl, w, A[w]};
    llterm.push_back(term);
    F.add(b[term.c], F.mulf(W[w], term.k));
  }

  LigeroCommitment<Field> commitment;
  LigeroProof<Field> proof(&param);

  SecureRandomEngine rng;
  LigeroProver<Field, ReedSolomonFactory> prover(param);
  Transcript ts_prove((uint8_t *)"test", 4, sigma);
  prover.commit(commitment, ts_prove, &W[0], 0, &lqc[0], rs_factory, rng, F);
  prover.prove(proof, ts_prove, nl, llterm.size(), &llterm[0], &lqc[0],
               rs_factory, F);

  const char *why = "";

  // 1. why == nullptr
  Transcript ts1((uint8_t *)"test", 4, sigma);
  LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                ts1);
  EXPECT_FALSE((LigeroVerifier<Field, ReedSolomonFactory>::verify(
      nullptr, param, commitment, proof, ts1, nl, llterm.size(), &llterm[0],
      &b[0], &lqc[0], rs_factory, F)));

  // 2. merkle_check failed
  Transcript ts2((uint8_t *)"test", 4, sigma);
  LigeroCommitment<Field> bad_comm = commitment;
  bad_comm.root.data[0] ^= 1;
  LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(bad_comm, ts2);
  EXPECT_FALSE((LigeroVerifier<Field, ReedSolomonFactory>::verify(
      &why, param, bad_comm, proof, ts2, nl, llterm.size(), &llterm[0], &b[0],
      &lqc[0], rs_factory, F)));
  EXPECT_STREQ(why, "merkle_check failed");

  // 3. dot_check failed (wrong dot product)
  Transcript ts3((uint8_t *)"test", 4, sigma);
  LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                ts3);
  std::vector<Elt> bad_b = b;
  F.add(bad_b[0], F.one());
  EXPECT_FALSE((LigeroVerifier<Field, ReedSolomonFactory>::verify(
      &why, param, commitment, proof, ts3, nl, llterm.size(), &llterm[0],
      &bad_b[0], &lqc[0], rs_factory, F)));
  EXPECT_STREQ(why, "wrong dot product");

  // 4. dot_check failed (bad constraint)
  Transcript ts4((uint8_t *)"test", 4, sigma);
  LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                ts4);
  std::vector<LigeroLinearConstraint<Field>> bad_llterm = llterm;
  F.add(bad_llterm[0].k, F.one());
  EXPECT_FALSE((LigeroVerifier<Field, ReedSolomonFactory>::verify(
      &why, param, commitment, proof, ts4, nl, bad_llterm.size(),
      &bad_llterm[0], &b[0], &lqc[0], rs_factory, F)));
  EXPECT_STREQ(why, "dot_check failed");

  // 5. low_degree_check failed
  Transcript ts5((uint8_t *)"test", 4, sigma);
  LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                ts5);
  BadReedSolomonFactory<Field, ReedSolomonFactory> bad_rs_1(rs_factory, 1);
  EXPECT_FALSE(
      (LigeroVerifier<Field, BadReedSolomonFactory<Field, ReedSolomonFactory>>::
           verify(&why, param, commitment, proof, ts5, nl, llterm.size(),
                  &llterm[0], &b[0], &lqc[0], bad_rs_1, F)));
  EXPECT_STREQ(why, "low_degree_check failed");

  // 6. quadratic_check failed
  Transcript ts6((uint8_t *)"test", 4, sigma);
  LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                ts6);
  BadReedSolomonFactory<Field, ReedSolomonFactory> bad_rs_4(rs_factory, 4);
  EXPECT_FALSE(
      (LigeroVerifier<Field, BadReedSolomonFactory<Field, ReedSolomonFactory>>::
           verify(&why, param, commitment, proof, ts6, nl, llterm.size(),
                  &llterm[0], &b[0], &lqc[0], bad_rs_4, F)));
  EXPECT_STREQ(why, "quadratic_check failed");

  // 7. a challenge point read past its stream budget: the verifier rejects
  // and the prover aborts.
  EXPECT_FALSE(ts_prove.exhausted());
  Transcript ts7((uint8_t *)"test", 4, sigma);
  ts7.set_stream_budget(8);
  LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                ts7);
  EXPECT_FALSE((LigeroVerifier<Field, ReedSolomonFactory>::verify(
      &why, param, commitment, proof, ts7, nl, llterm.size(), &llterm[0],
      &b[0], &lqc[0], rs_factory, F)));
  EXPECT_STREQ(why, "Fiat-Shamir challenge stream budget exceeded");
#if GTEST_HAS_DEATH_TEST
  {
    LigeroProver<Field, ReedSolomonFactory> prover8(param);
    LigeroCommitment<Field> commitment8;
    LigeroProof<Field> proof8(&param);
    Transcript ts8((uint8_t *)"test", 4, sigma);
    ts8.set_stream_budget(8);
    prover8.commit(commitment8, ts8, &W[0], 0, &lqc[0], rs_factory, rng, F);
    EXPECT_DEATH(prover8.prove(proof8, ts8, nl, llterm.size(), &llterm[0],
                               &lqc[0], rs_factory, F),
                 "budget exceeded");
  }
#endif
}

// Subfield enforcement: with SUBFIELD_WROWS set, an opened entry outside the
// subfield in one of those rows rejects the proof.  The cheating prover here
// commits subfield witness values but blinds its rows with full-field
// randomness (SUBFIELD_BOUNDARY = 0), so its rows are codewords over the full
// field, which is exactly what the check must refuse.
template <class Field, class ReedSolomonFactory>
void test_subfield_rows(const ReedSolomonFactory &rs_factory, const Field &F) {
  const ProofSeed sigma = test_seed();
  using Elt = typename Field::Elt;
  static const constexpr size_t nw = 3000;
  static const constexpr size_t nq = 30;
  static const constexpr size_t nreq = 18;
  static const constexpr size_t nl = 7;
  LigeroParam<Field> param(nw, nq, /*rateinv=*/4, nreq);
  const size_t subfield_wrows = nw / param.w;
  ASSERT_GT(subfield_wrows, 0u);

  std::vector<Elt> W(nw);
  std::vector<Elt> A(nw);
  for (size_t i = 0; i < nw; ++i) {
    W[i] = F.of_scalar(random() & 0xffff);
    A[i] = F.of_scalar_field(random());
  }
  std::vector<LigeroQuadraticConstraint> lqc(nq);
  for (size_t i = 0; i < nq; ++i) {
    lqc[i].z = 3 * i + 2;
    lqc[i].x = 3 * i;
    lqc[i].y = 3 * i + 1;
    W[lqc[i].z] = F.mulf(W[lqc[i].x], W[lqc[i].y]);
  }
  std::vector<LigeroLinearConstraint<Field>> llterm;
  std::vector<Elt> b(nl);
  Blas<Field>::clear(nl, &b[0], 1, F);
  for (size_t w = 0; w < nw; ++w) {
    LigeroLinearConstraint<Field> term = {w % nl, w, A[w]};
    llterm.push_back(term);
    F.add(b[term.c], F.mulf(W[w], term.k));
  }

  auto run = [&](size_t commit_boundary, size_t verify_wrows,
                 const char **why) {
    LigeroCommitment<Field> commitment;
    LigeroProof<Field> proof(&param);
    SecureRandomEngine rng;
    LigeroProver<Field, ReedSolomonFactory> prover(param);
    Transcript tp((uint8_t *)"test", 4, sigma);
    prover.commit(commitment, tp, &W[0], commit_boundary, &lqc[0], rs_factory,
                  rng, F);
    prover.prove(proof, tp, nl, llterm.size(), &llterm[0], &lqc[0],
                 rs_factory, F);
    Transcript tv((uint8_t *)"test", 4, sigma);
    LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                  tv);
    return LigeroVerifier<Field, ReedSolomonFactory>::verify(
        why, param, commitment, proof, tv, nl, llterm.size(), &llterm[0],
        &b[0], &lqc[0], rs_factory, F, /*accum=*/nullptr, verify_wrows);
  };

  const char *why = "";
  // Honest subfield rows pass with and without enforcement.
  EXPECT_TRUE(run(/*commit_boundary=*/nw, subfield_wrows, &why)) << why;
  EXPECT_TRUE(run(/*commit_boundary=*/0, /*verify_wrows=*/0, &why)) << why;
  // Full-field rows declared subfield are rejected.
  EXPECT_FALSE(run(/*commit_boundary=*/0, subfield_wrows, &why));
  EXPECT_STREQ(why, "subfield_check failed");
  // Only the declared rows are checked: the partial last row is blinded with
  // full-field randomness even for an honest prover.
  if (nw % param.w != 0) {
    EXPECT_FALSE(run(/*commit_boundary=*/nw, param.nwrow, &why));
    EXPECT_STREQ(why, "subfield_check failed");
  }
  // Declaring more rows than exist is rejected outright.
  EXPECT_FALSE(run(/*commit_boundary=*/nw, param.nwrow + 1, &why));
  EXPECT_STREQ(why, "subfield_check failed");
}

// List-radius Ligero (LigeroMode): the low-degree challenge and response
// right after the commitment (ldt_commit / receive_ldt), then the proof.
// TAMPER changes the prover's tableau and split masks before the
// commitment; TAMPER_PROOF changes the proof after proving.  Returns the
// verifier's verdict and reason.
template <class Field, class ReedSolomonFactory>
struct ListRadiusCase {
  using Elt = typename Field::Elt;
  using Prover = LigeroProver<Field, ReedSolomonFactory>;
  static constexpr size_t nw = 300, nq = 30, nreq = 18, nl = 7;

  const ReedSolomonFactory &rs;
  const Field &F;
  LigeroParam<Field> param;
  std::vector<Elt> W, b;
  std::vector<LigeroQuadraticConstraint> lqc;
  std::vector<LigeroLinearConstraint<Field>> llterm;

  ListRadiusCase(const ReedSolomonFactory &rs, const Field &F, LigeroMode mode)
      : rs(rs), F(F), param(nw, nq, /*rateinv=*/4, nreq, mode), W(nw),
        b(nl, F.zero()), lqc(nq) {
    for (size_t i = 0; i < nw; ++i) W[i] = F.of_scalar_field(random());
    for (size_t i = 0; i < nq; ++i) {
      lqc[i] = {3 * i, 3 * i + 1, 3 * i + 2};
      W[lqc[i].z] = F.mulf(W[lqc[i].x], W[lqc[i].y]);
    }
    for (size_t w = 0; w < nw; ++w) {
      LigeroLinearConstraint<Field> term = {w % nl, w,
                                            F.of_scalar_field(random())};
      llterm.push_back(term);
      F.add(b[term.c], F.mulf(W[w], term.k));
    }
  }

  // A codeword of a uniform polynomial of degree < BLOCK, added to row I.
  void add_codeword(std::vector<Elt> &tableau, size_t i) const {
    std::vector<Elt> v(param.block_enc);
    for (size_t j = 0; j < param.block; ++j) v[j] = F.of_scalar_field(random());
    rs.make(param.block, param.block_enc)->interpolate(v.data());
    for (size_t j = 0; j < param.block_enc; ++j)
      F.add(tableau[i * param.block_enc + j], v[j]);
  }

  bool run(const char **why,
           typename Prover::TamperFn tamper = nullptr,
           std::function<void(LigeroProof<Field> &)> tamper_proof = nullptr,
           bool skip_ldt = false,
           std::function<void(std::vector<Elt> &)> tamper_ldt = nullptr) {
    const ProofSeed sigma = test_seed();
    LigeroCommitment<Field> commitment;
    LigeroProof<Field> proof(&param);
    SecureRandomEngine rng;
    Prover prover(param);
    prover.tamper = tamper;
    prover.tamper_ldt = tamper_ldt;
    Transcript tp((uint8_t *)"test", 4, sigma);
    prover.commit(commitment, tp, &W[0], 0, &lqc[0], rs, rng, F);
    prover.ldt_commit(proof, tp, F);
    prover.prove(proof, tp, nl, llterm.size(), &llterm[0], &lqc[0], rs, F);
    if (tamper_proof) tamper_proof(proof);

    Transcript tv((uint8_t *)"test", 4, sigma);
    LigeroVerifier<Field, ReedSolomonFactory>::receive_commitment(commitment,
                                                                  tv);
    std::vector<Elt> u_ldt;
    if (!skip_ldt)
      LigeroVerifier<Field, ReedSolomonFactory>::receive_ldt(param, proof, tv,
                                                             u_ldt, F);
    return LigeroVerifier<Field, ReedSolomonFactory>::verify(
        why, param, commitment, proof, tv, nl, llterm.size(), &llterm[0],
        &b[0], &lqc[0], rs, F, /*accum=*/nullptr, /*subfield_wrows=*/0,
        skip_ldt ? nullptr : &u_ldt);
  }
};

template <class Field, class ReedSolomonFactory>
void test_list_radius(const ReedSolomonFactory &rs, const Field &F) {
  using Case = ListRadiusCase<Field, ReedSolomonFactory>;
  using Elt = typename Field::Elt;
  const char *why = "";
  for (size_t reps : {size_t(1), size_t(2), size_t(3)})
  for (LigeroMasking masking :
       {LigeroMasking::kUntested, LigeroMasking::kSplit}) {
    const bool split = masking == LigeroMasking::kSplit;
    Case c(rs, F, LigeroMode{true, masking, reps});
    const auto &p = c.param;
    EXPECT_EQ(p.r, Case::nreq);
    EXPECT_EQ(p.nldt, p.nwqrow + (split ? 6 : 0));
    // The REPS mask rows ILDT_j at rows 0 .. REPS - 1, then the rows of one
    // repetition in their order.
    EXPECT_EQ(p.nrow, p.nldt + reps + (split ? 0 : 2));
    EXPECT_EQ(p.ildt, 0u);
    EXPECT_EQ(p.iw, reps + (split ? 0 : 2));

    // Honest proofs verify.
    EXPECT_TRUE(c.run(&why)) << why << " reps=" << reps;

    // A low-degree response inconsistent with the commitment, written in
    // the commit round: any one of the REPS responses.
    for (size_t j = 0; j < reps; ++j) {
      EXPECT_FALSE(c.run(&why, nullptr, nullptr, false,
                         [&](std::vector<Elt> &y) {
                           ASSERT_EQ(y.size(), reps * p.block);
                           F.add(y[j * p.block + 1], F.one());
                         }))
          << j;
      EXPECT_STREQ(why, "low_degree_check failed") << j;
    }

    // A committed mask row ILDT_j that is not a codeword (every position
    // past the block off by one): its own repetition's check fails at every
    // opened column.
    for (size_t j = 0; j < reps; ++j) {
      EXPECT_FALSE(c.run(&why, [&](std::vector<Elt> &t,
                                   std::vector<Elt>(&)[2]) {
        for (size_t x = p.block; x < p.block_enc; ++x)
          F.add(t[(p.ildt + j) * p.block_enc + x], F.one());
      })) << j;
      EXPECT_STREQ(why, "low_degree_check failed") << j;
      // An opened entry of ILDT_j other than the committed one.
      EXPECT_FALSE(c.run(&why, nullptr, [&](LigeroProof<Field> &pr) {
        F.add(pr.req_at(p.ildt + j, 0), F.one());
      })) << j;
      EXPECT_STREQ(why, "merkle_check failed") << j;
    }

    // An opened column that is not the committed one.
    const size_t row = split ? p.ipiece : p.idot;
    EXPECT_FALSE(c.run(&why, nullptr, [&](LigeroProof<Field> &pr) {
      F.add(pr.req_at(row, 0), F.one());
    }));
    EXPECT_STREQ(why, "merkle_check failed");

    // The verifier needs the low-degree round.
    EXPECT_FALSE(c.run(&why, nullptr, nullptr, /*skip_ldt=*/true));
    EXPECT_STREQ(why, "low-degree commit round missing or unexpected");

    if (!split) continue;

    // A committed piece row (A, C or B of either mask) other than the one
    // the responses use: still a codeword, so only the mask check sees it.
    for (size_t piece = 0; piece < 6; ++piece) {
      EXPECT_FALSE(c.run(&why, [&](std::vector<Elt> &t,
                                   std::vector<Elt>(&)[2]) {
        c.add_codeword(t, p.ipiece + piece);
      })) << piece;
      EXPECT_STREQ(why, piece < 3 ? "dot_check failed"
                                  : "quadratic_check failed")
          << piece;
    }

    // A recombination off by one coefficient: the dot-product mask the
    // responses use differs from A + Y^(k-t) C + Y^k B by Y^k, or by
    // Y^(k-t).  (The quadratic mask must vanish on the witness positions,
    // which the prover checks; its pieces are covered above.)
    const std::vector<Elt> y = LigeroCommon<Field>::split_points(p, rs, F);
    for (size_t e : {p.block, p.block - p.nreq}) {
      EXPECT_FALSE(c.run(&why, [&](std::vector<Elt> &,
                                   std::vector<Elt>(&masks)[2]) {
        for (size_t i = 0; i < p.dblock; ++i)
          F.add(masks[0][i], LigeroCommon<Field>::power(y[i], e, F));
      }));
      EXPECT_STREQ(why, "dot_check failed") << e;
    }
  }

  // More than one repetition needs list-radius Ligero.
  {
    LigeroParam<Field> q(Case::nw, Case::nq, 4, Case::nreq,
                         LigeroMode{false, LigeroMasking::kUntested});
    q.mode.ldt_reps = 2;
    EXPECT_EQ(q.layout(q.block_enc), SIZE_MAX);
  }

  // Split masks need 2 t <= k.
  {
    LigeroParam<Field> p(Case::nw, Case::nq, 4, Case::nreq,
                         LigeroMode{true, LigeroMasking::kSplit});
    EXPECT_EQ(LigeroParam<Field>(Case::nw, Case::nq, 4, p.block / 2 + 1,
                                 LigeroMode{true, LigeroMasking::kSplit})
                  .layout(p.block_enc),
              SIZE_MAX);
  }
}

TEST(Ligero, Fp) {
  using Field = Fp<1>;
  using ConvolutionFactory = FFTConvolutionFactory<Field>;
  using ReedSolomonFactory = ReedSolomonFactory<Field, ConvolutionFactory>;

  const Field F("18446744069414584321");
  const ConvolutionFactory conv_factory(F, F.of_scalar(1753635133440165772ull),
                                        1ull << 32);
  const ReedSolomonFactory rs_factory(conv_factory, F);

  ligero_test(rs_factory, F);
  test_ligero_verifier_failures(rs_factory, F);
  test_list_radius(rs_factory, F);
}

TEST(Ligero, GF2_128) {
  using Field = GF2_128<>;
  const Field F;
  using ReedSolomonFactory = LCH14ReedSolomonFactory<Field>;
  const ReedSolomonFactory rs_factory(F);

  ligero_test(rs_factory, F);
  test_ligero_verifier_failures(rs_factory, F);
  test_subfield_rows(rs_factory, F);
  test_list_radius(rs_factory, F);
}

TEST(Ligero, BlockEncUnderflowInLayout) {
  using Field = Fp<1>;
  // We need to trigger the condition: block_enc < dblock on line 224 of
  // ligero_param.h. This happens when block == 0 and dblock (2*block - 1)
  // underflows to SIZE_MAX. By setting nreq (and thus r) to 0, we can bypass
  // the check (block < r), allowing block to be 0 for small values of block_enc
  // (e.g. block_enc = 1).
  LigeroParam<Field> param(300, 30, 4, /*nreq=*/0);

  // Test block_enc = 1 which yields block = (1+1)/(2+4) = 0.
  // dblock underflows to SIZE_MAX, and layout should return SIZE_MAX.
  EXPECT_EQ(param.layout(1), SIZE_MAX);
}

TEST(Ligero, ZeroSizeProof) {
  const ProofSeed sigma = test_seed();
  using Field = Fp<1>;
  using ConvolutionFactory = FFTConvolutionFactory<Field>;
  using ReedSolomonFactory = ReedSolomonFactory<Field, ConvolutionFactory>;

  const Field F("18446744069414584321");
  const ConvolutionFactory conv_factory(F, F.of_scalar(1753635133440165772ull),
                                        1ull << 32);
  const ReedSolomonFactory rs_factory(conv_factory, F);

  size_t nw = 100;
  size_t nq = 0;
  size_t nreq = 10;
  size_t nl = 0;
  LigeroParam<Field> param(nw, nq, /*rateinv=*/4, nreq);
  log(INFO, "ZeroSizeProof: param.block = %zu, param.block_enc = %zu",
      param.block, param.block_enc);

  std::vector<typename Field::Elt> W(nw, F.zero());
  std::vector<LigeroQuadraticConstraint> lqc;        // empty
  std::vector<LigeroLinearConstraint<Field>> llterm; // empty

  LigeroCommitment<Field> commitment;
  LigeroProof<Field> proof(&param);

  SecureRandomEngine rng;
  LigeroProver<Field, ReedSolomonFactory> prover(param);
  Transcript ts((uint8_t *)"test", 4, sigma);

  prover.commit(commitment, ts, W.data(), 0, lqc.data(), rs_factory, rng, F);
  prover.prove(proof, ts, nl, llterm.size(), llterm.data(), lqc.data(),
               rs_factory, F);
}

} // namespace
} // namespace proofs
