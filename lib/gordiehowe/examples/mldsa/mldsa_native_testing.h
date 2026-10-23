// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Test support for the ML-DSA-44 native proof of possession
// (mldsa_native.h): the host witness of a signed example (ml_dsa_witness's
// compute_witness) and the values each GordieHowe generator must equal,
// helpers that read a proof's generated values by node name, and the plan
// export (export_plan, the bench hook).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <map>
#include <memory>
#include <regex>
#include <stdexcept>
#include <string>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_witness.h"
#include "gordiehowe/examples/mldsa/mldsa_builders.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/shared/system_testing.h"
#include "random/secure_random_engine.h"

namespace proofs::gordiehowe::examples::mldsa {

// The relation over messages of at most MAX_BYTES bytes under contexts of
// CTX_BYTES bytes, with the assignments of example values, for the tests
// and benchmarks that drive the prover directly. PACKING is the packing
// ablation.
template <class P>
struct MLDSANativeSystem
    : RelationSystem<typename Env<P>::Sys, MLDSAStatement<Value>,
                     MLDSAWitness<Value>> {
  using E = Env<P>;
  using Base = RelationSystem<typename E::Sys, MLDSAStatement<Value>,
                              MLDSAWitness<Value>>;
  using typename Base::Assignment;

  size_t max_bytes, ctx_bytes;

  MLDSANativeSystem(const E &env, size_t max, size_t ctx,
                    PackingAblation packing = PackingAblation::kNone,
                    const BuildOptions &build = {})
      : Base(mldsa_native<P>(env, max, ctx, packing, build)),
        max_bytes(max),
        ctx_bytes(ctx) {}

  Assignment statement(const std::vector<uint8_t> &pk,
                       const std::vector<uint8_t> &ctx) const {
    return Base::statement(mldsa_statement(pk, ctx));
  }
  Assignment witness(const std::vector<uint8_t> &msg,
                     const Signature &sig) const {
    return Base::witness(mldsa_witness(msg, sig, max_bytes, ctx_bytes));
  }
};

}  // namespace proofs::gordiehowe::examples::mldsa

namespace proofs::gordiehowe::examples::mldsa::support {

// The K base-T digits of each value of V, least significant first:
// [V.size()][K].
inline std::vector<uint64_t> digits_of(const std::vector<uint64_t> &v,
                                       uint64_t T, size_t K) {
  std::vector<uint64_t> out;
  for (uint64_t x : v)
    for (size_t l = 0; l < K; ++l) {
      out.push_back(x % T);
      x /= T;
    }
  return out;
}
// The digits of a realized range request: range.<NAME>.<P>0 .. <P>(K-1),
// interleaved per coordinate ([n][K]); AV reads a value's integers.
template <class AV>
std::vector<uint64_t> realized_digits(const AV &av, const std::string &name,
                                      const char *prefix, size_t K) {
  std::vector<std::vector<uint64_t>> d;
  for (size_t l = 0; l < K; ++l)
    d.push_back(av("range." + name + "." + prefix + std::to_string(l)));
  std::vector<uint64_t> out;
  for (size_t i = 0; i < d[0].size(); ++i)
    for (size_t l = 0; l < K; ++l) out.push_back(d[l][i]);
  return out;
}

// The host witness of a signed example (ml_dsa_witness's compute_witness),
// and the decoded signature the GordieHowe witness assignment takes.
struct Existing {
  const ml_dsa::MlDsa44SignatureExample &ex;
  std::unique_ptr<ml_dsa_witness<Params>> wg =
      std::make_unique<ml_dsa_witness<Params>>();
  bool ok = false;

  explicit Existing(const ml_dsa::MlDsa44SignatureExample &e) : ex(e) {
    ok = wg->compute_witness(ex.pkey, ex.sig, ex.msg, ex.ctx);
  }

  Signature signature() const {
    Signature s;
    s.c_tilde.assign(wg->c_tilde_.begin(), wg->c_tilde_.end());
    for (size_t j = 0; j < kL; ++j) {
      const auto z = host::canonical(wg->ref_sig_.z[j]);
      s.z.insert(s.z.end(), z.begin(), z.end());
    }
    for (size_t i = 0; i < kK; ++i)
      for (size_t k = 0; k < kN; ++k) s.h.push_back(wg->ref_sig_.h[i][k] ? 1 : 0);
    return s;
  }

  // c: (support, sign) per coefficient.
  std::vector<uint64_t> c_bits() const {
    std::vector<uint64_t> out;
    for (uint64_t x : host::canonical(wg->c_coeffs_)) {
      out.push_back(x != 0);
      out.push_back(x == kQ - 1);
    }
    return out;
  }
  // w' (canonical), [K][N].
  std::vector<uint64_t> w() const {
    std::vector<uint64_t> out;
    for (size_t i = 0; i < kK; ++i) {
      const auto p = host::canonical(wg->w_prime_approx_[i]);
      out.insert(out.end(), p.begin(), p.end());
    }
    return out;
  }
  // UseHint's output bits, [K][N][6], least significant first.
  std::vector<uint64_t> w1_bits() const {
    std::vector<uint64_t> out;
    for (size_t i = 0; i < kK; ++i)
      for (size_t k = 0; k < kN; ++k)
        for (size_t b = 0; b < kR1Bits; ++b)
          out.push_back((wg->w_prime_1_bits_[i][k] >> b) & 1);
    return out;
  }
  // UseHint's sign bit, offset and slack per coefficient, from r0 and w1
  // (values, before their split into base-512 digits).
  struct Hint {
    std::vector<uint64_t> nonpositive, offset, slack;
  };
  Hint hint() const {
    Hint o;
    for (size_t i = 0; i < kK; ++i)
      for (size_t j = 0; j < kN; ++j) {
        const uint64_t R =
            wg->hint_aux_bits_[i][j] & ((uint64_t{1} << Params::r0_bits) - 1);
        const uint64_t s = (R <= kGamma2) ? 1 : 0;
        const uint64_t endpoint = s && wg->w1_[i][j] == 0;
        const uint64_t v = s ? R + endpoint - 1 : (R - kGamma2 - 1);
        o.nonpositive.push_back(s);
        o.offset.push_back(v);
        o.slack.push_back(kGamma2 - 1 + endpoint - v);
      }
    return o;
  }
  // The norm digits of z: the shifted coefficient z + (bound - 1) or its
  // complement, K digits each in base T (the planner's), [L][N][K].
  std::vector<uint64_t> z_limbs(bool complement, uint64_t T, size_t K) const {
    const uint64_t top = 2 * kBound - 2;
    std::vector<uint64_t> v;
    for (size_t j = 0; j < kL; ++j)
      for (size_t k = 0; k < kN; ++k)
        v.push_back(complement ? top - wg->z_bits_[j][k] : wg->z_bits_[j][k]);
    return digits_of(v, T, K);
  }
};

// Bits (0/1 field elements) to bytes, bit i of byte k at 8k + i.
template <class F>
std::vector<uint8_t> bytes_of(const F &f, const std::vector<typename F::Elt> &b) {
  std::vector<uint8_t> out(b.size() / 8, 0);
  for (size_t i = 0; i < 8 * out.size(); ++i)
    out[i / 8] |= uint8_t(ct::bit_of(f, b[i]) << (i % 8));
  return out;
}
// Canonical integers of prime-subfield elements.
template <class F>
std::vector<uint64_t> ints_of(const F &f, const std::vector<typename F::Elt> &x) {
  std::vector<uint64_t> out;
  for (const auto &e : x) out.push_back(uint64_t(nat_of(f, e)));
  return out;
}

// The id of the node named NAME.
template <class Sys>
size_t node_id(const Sys &cs, const std::string &name) {
  const auto &N = cs.graph().nodes;
  for (size_t i = 0; i < N.size(); ++i)
    if (N[i].name == name) return i;
  throw std::runtime_error("no node named '" + name + "'");
}

// Circuit sizes of one domain in a compile report.
struct DomainSize {
  size_t layers = 0, quad = 0, committed = 0, inputs = 0, publics = 0, nw = 0,
         nq = 0, affine = 0;
};
inline DomainSize domain_size(const std::string &report, const std::string &d) {
  DomainSize s;
  const auto at = report.find("domain " + d + " (");
  if (at == std::string::npos) return s;
  const std::string r = report.substr(at, 2000);
  std::smatch m;
  if (std::regex_search(r, m, std::regex(R"(ninputs=(\d+) public=(\d+) committed=(\d+))"))) {
    s.inputs = std::stoul(m[1]);
    s.publics = std::stoul(m[2]);
    s.committed = std::stoul(m[3]);
  }
  if (std::regex_search(r, m, std::regex(R"(layers=(\d+))")))
    s.layers = std::stoul(m[1]);
  if (std::regex_search(r, m, std::regex(R"(quad_terms=(\d+))")))
    s.quad = std::stoul(m[1]);
  if (std::regex_search(r, m, std::regex(R"(nw=(\d+) nq=(\d+))"))) {
    s.nw = std::stoul(m[1]);
    s.nq = std::stoul(m[2]);
  }
  if (std::regex_search(r, m, std::regex(R"(affine_rows=(\d+))")))
    s.affine = std::stoul(m[1]);
  return s;
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
  MLDSANativeSystem<P> t(env, ex.msg.size(), ex.ctx.size());
  const auto c = t.compile();
  const compiler::ExportMeta meta{"mldsa-native", P::kId, commit,
                        run_id, ex.msg.size(), ex.ctx.size()};
  return write_plan(*c, dir, meta);
}

}  // namespace proofs::gordiehowe::examples::mldsa::support

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_MLDSA_MLDSA_NATIVE_TESTING_H_
