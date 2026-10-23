// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_operators_test*.cc, one binary): the
// fields, sizes and reference helpers they share. Each test file has its own
// copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_OPERATORS_TEST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_OPERATORS_TEST_H_

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <vector>

#include "algebra/fp14.h"
#include "algebra/fp14_n.h"
#include "algebra/fp24.h"
#include "algebra/fp24_6.h"
#include "algebra/fp_goldilocks.h"
#include "algebra/fp_goldilocks4.h"
#include "algebra/fp_native_wide.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/ntt/falcon_ntt.h"
#include "circuits/ntt/ntt_gadget.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "algebra/reed_solomon_fp.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {


constexpr uint64_t kFalconQ = 12289, kMLDSAQ = 8380417;
constexpr size_t kFalconN = 512, kMLDSAN = 256, kK = 4, kL = 4;

const Fp14 &fq14() {
  static const Fp14 *b = new Fp14(kFalconQ);
  return *b;
}
const Fp24 &fq24() {
  static const Fp24 *b = new Fp24(kMLDSAQ);
  return *b;
}
template <class F>
constexpr bool kCarrier = std::is_same_v<F, Fp64G2> || std::is_same_v<F, Fp64G4>;
template <class F>
constexpr bool kFalconField =
    !kCarrier<F> && std::is_same_v<typename F::BaseField, Fp14>;

// One field object per type, alive for the whole test.
template <class F>
const F &field() {
  if constexpr (kCarrier<F>) {
    static const F *f = new F;
    return *f;
  } else if constexpr (kFalconField<F>) {
    static const F *f = new F(fq14(), F::beta_);
    return *f;
  } else {
    static const F *f = new F(fq24(), F::beta_);
    return *f;
  }
}
template <class F>
uint64_t modulus() {
  if constexpr (kFalconField<F>) return kFalconQ;
  else return kMLDSAQ;
}
template <class F>
size_t ring_n() {
  if constexpr (kCarrier<F> || kFalconField<F>) return kFalconN;
  else return kMLDSAN;
}

template <class F>
std::vector<typename F::Elt> random_full(size_t n) {
  SecureRandomEngine rng;
  std::vector<typename F::Elt> v(n);
  for (auto &x : v) x = rng.elt(field<F>());
  return v;
}
// Coefficients below the scheme modulus (a public key over F_q).
std::vector<uint64_t> random_mod(size_t n, uint64_t q, uint64_t seed) {
  std::mt19937_64 g(seed);
  std::vector<uint64_t> v(n);
  for (auto &x : v) x = g() % q;
  return v;
}
template <class F>
std::vector<typename F::Elt> lift(const std::vector<uint64_t> &v) {
  std::vector<typename F::Elt> out;
  for (uint64_t x : v) out.push_back(field<F>().of_scalar(x));
  return out;
}

// op equals ref on random inputs, both ways, and apply and transpose_apply
// are adjoint: <A x, y> = <x, A^T y>.
template <class F>
void expect_matches(const LinearOperator<F> &op, const LinearOperator<F> &ref) {
  const F &f = field<F>();
  ASSERT_EQ(op.rows(), ref.rows());
  ASSERT_EQ(op.cols(), ref.cols());
  auto x = random_full<F>(op.cols()), y = random_full<F>(op.rows());
  using E = typename F::Elt;
  std::vector<E> ax(op.rows()), rax(op.rows()), aty(op.cols()),
      raty(op.cols());
  op.apply(x.data(), ax.data());
  ref.apply(x.data(), rax.data());
  op.transpose_apply(y.data(), aty.data());
  ref.transpose_apply(y.data(), raty.data());
  EXPECT_TRUE(ax == rax);
  EXPECT_TRUE(aty == raty);
  E l = f.zero(), r = f.zero();
  for (size_t i = 0; i < y.size(); ++i) f.add(l, f.mulf(ax[i], y[i]));
  for (size_t j = 0; j < x.size(); ++j) f.add(r, f.mulf(x[j], aty[j]));
  EXPECT_EQ(l, r);
}

template <class F>
std::shared_ptr<const ops::NegacyclicNtt<F>> scheme_ntt(size_t n) {
  auto t = ops::negacyclic_ntt(field<F>(), n);
  EXPECT_NE(t, nullptr);
  return t;
}


}  // namespace
}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_OPERATORS_TEST_H_
