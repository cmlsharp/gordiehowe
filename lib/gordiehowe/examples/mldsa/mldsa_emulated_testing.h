// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test support for the ML-DSA-44 emulated proof of possession
// (mldsa_emulated.h): the values each GordieHowe generator must equal on a
// signed example, from its host witness (ml_dsa_witness's compute_witness,
// ml_dsa_fp::advice) and the signature relation over the integers, and the
// plan export (export_plan, the bench hook). The native arm's support
// (mldsa_native_testing.h) supplies the shared parts: Existing and the node
// and report readers.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <fstream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "gordiehowe/examples/mldsa/ml_dsa_fp_witness.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_ref.h"
#include "gordiehowe/examples/mldsa/mldsa_builders.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/shared/system_testing.h"

namespace proofs::gordiehowe::examples::mldsa::emulated {

// The relation with the assignments of example values, for the tests and
// benchmarks that drive the prover directly. PACKING is the packing
// ablation (setup.h).
template <class P>
struct MLDSAEmulatedSystem
    : RelationSystem<typename Env<P>::Sys, MLDSAStatement<Value>,
                     MLDSAWitness<Value>> {
  using E = Env<P>;
  using Base = RelationSystem<typename E::Sys, MLDSAStatement<Value>,
                              MLDSAWitness<Value>>;
  using typename Base::Assignment;

  size_t max_bytes, ctx_bytes;

  MLDSAEmulatedSystem(const E &env, size_t max, size_t ctx,
                      PackingAblation packing = PackingAblation::kNone,
                      const BuildOptions &build = {})
      : Base(mldsa_emulated<P>(env, max, ctx, packing, build)),
        max_bytes(max),
        ctx_bytes(ctx) {}

  Assignment statement(const std::vector<uint8_t> &pk,
                       const std::vector<uint8_t> &ctx) const {
    return Base::statement(mldsa_statement(pk, ctx));
  }
  // The decoded signature's z (canonical in [0, q)) enters as the
  // carrier's signed coefficients.
  Assignment witness(const std::vector<uint8_t> &msg,
                     const Signature &sig) const {
    return Base::witness(mldsa_witness(msg, sig, max_bytes, ctx_bytes));
  }
};

}  // namespace proofs::gordiehowe::examples::mldsa::emulated

namespace proofs::gordiehowe::examples::mldsa::emulated::support {

using examples::mldsa::support::digits_of;
using examples::mldsa::support::Existing;

// The digits of the shifted coefficient z + (bound - 1), or of its
// complement 2 bound - 2 - (z + bound - 1), K each in base T (the
// planner's), [L][N][K].
inline std::vector<uint64_t> z_limbs(const Existing &e, bool complement,
                                     uint64_t T, size_t K) {
  const uint64_t top = 2 * kBound - 2;
  std::vector<uint64_t> v;
  for (size_t j = 0; j < kL; ++j)
    for (size_t k = 0; k < kN; ++k)
      v.push_back(complement ? top - e.wg->z_bits_[j][k] : e.wg->z_bits_[j][k]);
  return digits_of(v, T, K);
}
// w' in base T, K digits per coefficient.
inline std::vector<uint64_t> w_limbs(const Existing &e, uint64_t T, size_t K) {
  return digits_of(e.w(), T, K);
}

// The signature residual w' - sum_j a_j z_j + t c over the integers, [K][N],
// with the negacyclic product of Z[X]/(X^N + 1): a_j and t the coefficient
// forms (FIPS 204's NTT^-1, ml_dsa_ref.h) of the key's A_hat and of
// NTT(2^d t1), z = z' - (bound - 1) from the shifted z', and c in
// {-1, 0, 1}. ML-DSA's verification equation w' = A z - c 2^d t1 (mod q)
// makes every coordinate a multiple of q.
inline std::vector<__int128> signature_residual(const Existing &e) {
  const auto &wg = *e.wg;
  auto coefficients = [](ml_dsa::Rq spectrum) {
    ml_dsa::InvNtt(spectrum);
    std::vector<__int128> a(kN);
    for (size_t k = 0; k < kN; ++k) a[k] = __int128(ml_dsa_fp::as_u64(spectrum[k]));
    return a;
  };
  // acc += sign * (a * b) in Z[X]/(X^N + 1).
  auto mul_add = [](std::vector<__int128> &acc, const std::vector<__int128> &a,
                    const std::vector<__int128> &b, int sign) {
    for (size_t u = 0; u < kN; ++u)
      for (size_t v = 0; v < kN; ++v) {
        const __int128 t = a[u] * b[v];
        if (u + v < kN) {
          acc[u + v] += sign * t;
        } else {
          acc[u + v - kN] -= sign * t;
        }
      }
  };
  std::vector<__int128> c(kN);
  for (size_t k = 0; k < kN; ++k) {
    const uint64_t cq = ml_dsa_fp::as_u64(wg.c_coeffs_[k]);
    c[k] = cq == 0 ? 0 : (cq == kQ - 1 ? -1 : 1);
  }
  std::vector<__int128> out;
  for (size_t i = 0; i < kK; ++i) {
    std::vector<__int128> r(kN);
    for (size_t k = 0; k < kN; ++k)
      r[k] = __int128(ml_dsa_fp::as_u64(wg.w_prime_approx_[i][k]));
    mul_add(r, coefficients(wg.nttt1_[i]), c, 1);
    for (size_t j = 0; j < kL; ++j) {
      std::vector<__int128> z(kN);
      for (size_t k = 0; k < kN; ++k)
        z[k] = __int128(wg.z_bits_[j][k]) - __int128(kBound - 1);
      mul_add(r, coefficients(wg.ref_pk_.a_hat[i][j]), z, -1);
    }
    out.insert(out.end(), r.begin(), r.end());
  }
  return out;
}

// The plan export of profile P (plan_export.h): the system of the benchmark
// example's message and context lengths, compiled, written to
// DIR with its realized program (write_plan). Returns the plan's
// path.
template <class P>
std::string export_plan(const std::string &dir, const std::string &commit,
                        const std::string &run_id) {
  const auto &ex = ml_dsa::GetMlDsa44BenchmarkExample();
  const Env<P> env;
  MLDSAEmulatedSystem<P> t(env, ex.msg.size(), ex.ctx.size());
  const auto c = t.compile();
  const compiler::ExportMeta meta{"mldsa-emulated", P::kId, commit,
                        run_id, ex.msg.size(), ex.ctx.size()};
  return write_plan(*c, dir, meta);
}

}  // namespace proofs::gordiehowe::examples::mldsa::emulated::support

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_EMULATED_TESTING_H_
