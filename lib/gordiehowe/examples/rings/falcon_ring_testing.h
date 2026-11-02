// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: test support for the Falcon private rings (falcon_ring.h):
// the compiled relations of both arms and FalconRingSystem, the ring
// instances (seeds, key and signature, the ring and the signer's index)
// for any ring size with the host witness values to compare
// (falcon_encoding.h, ntt_gadget's host schedule), and the plan export.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <vector>

#include "algebra/fp14.h"
#include "arrays/dense.h"
#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/ntt/emulated_signature.h"
#include "circuits/ntt/ntt_gadget.h"
#include "gordiehowe/compiler/plan_export.h"
#include "gordiehowe/examples/falcon/falcon_encoding.h"
#include "gordiehowe/examples/falcon/falcon_instance_testing.h"
#include "gordiehowe/examples/rings/falcon_ring.h"
#include "gordiehowe/examples/rings/falcon_ring_builders.h"
#include "gordiehowe/examples/rings/falcon_ring_params.h"
#include "gordiehowe/examples/shared/program_testing.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/examples/shared/system_testing.h"
#include "gordiehowe/relation.h"

namespace proofs::gordiehowe::examples::falcon::ring {

// --------------------------------------------------------------- systems --

// The relations of set S for rings of R members, compiled, named
// <S::kTag>-ring-carrier and <S::kTag>-ring-native.
template <class P, class S>
Relation<RingStatement<S, Value>, RingWitness<S, Value>> falcon_ring_carrier(
    const CarrierEnv<P> &env, size_t R) {
  using I = RingInputs<S>;
  return compile<I::template Statement, I::template Witness>(
      carrier_compile_profile(),
      [&env](typename CarrierEnv<P>::Sys &cs, RingStatement<S, In> st,
             RingWitness<S, In> w) {
        ring_carrier_relation<P, S>(cs, env, st, w);
      },
      std::string(S::kTag) + "-ring-carrier", ring_statement_shape<S>(R),
      RingWitness<S, Value>{});
}
template <class P, class S>
Relation<RingStatement<S, Value>, RingWitness<S, Value>> falcon_ring_native(
    const NativeEnv<P> &env, size_t R) {
  using I = RingInputs<S>;
  return compile<I::template Statement, I::template Witness>(
      native_compile_profile<P>(),
      [&env](typename NativeEnv<P>::Sys &cs, RingStatement<S, In> st,
             RingWitness<S, In> w) {
        ring_native_relation<P, S>(cs, env, st, w);
      },
      std::string(S::kTag) + "-ring-native", ring_statement_shape<S>(R),
      RingWitness<S, Value>{});
}

// The relations for rings of R members, with the assignments of example
// values, for the tests and benchmarks that drive the prover directly.
template <class P, class S, class E, bool kNative>
struct FalconRingSystem
    : RelationSystem<typename E::Sys, RingStatement<S, Value>,
                     RingWitness<S, Value>> {
  using Set = S;
  using Env = E;
  using AF = typename E::AF;
  using PH = typename E::PH;
  using Base = RelationSystem<typename E::Sys, RingStatement<S, Value>,
                              RingWitness<S, Value>>;
  using typename Base::Assignment;
  using typename Base::Compiled;

  FalconRingSystem(const E &env, size_t R) : Base(declare(env, R)) {}

  using Base::compile;
  // The system compiled again under C (it is lowered once, so C's name and
  // version are the profile's).
  std::unique_ptr<Compiled> compile(const CompileProfile &c) {
    return gordiehowe::compile(this->cs, c);
  }
  static CompileProfile compile_profile() {
    if constexpr (kNative)
      return native_compile_profile<P>();
    else
      return carrier_compile_profile();
  }
  Assignment statement(const std::vector<std::vector<uint64_t>> &ring,
                       const std::vector<uint64_t> &c) const {
    return Base::statement(ring_statement<S>(ring, c));
  }
  Assignment witness(size_t index, const std::vector<uint64_t> &h,
                     const std::vector<uint64_t> &s2) const {
    return Base::witness(ring_witness<S>(index, h, s2));
  }

 private:
  static Relation<RingStatement<S, Value>, RingWitness<S, Value>> declare(
      const E &env, size_t R) {
    if constexpr (kNative)
      return falcon_ring_native<P, S>(env, R);
    else
      return falcon_ring_carrier<P, S>(env, R);
  }
};
template <class P, class S = Falcon512>
using FalconRingCarrierSystem = FalconRingSystem<P, S, CarrierEnv<P>, false>;
template <class P, class S = Falcon512>
using FalconRingNativeSystem = FalconRingSystem<P, S, NativeEnv<P>, true>;

// ------------------------------------------------------------- instances --

// A ring instance: the ring's coefficients, c, the signer's index and key,
// and the signature (s1, s2), canonical below q.
struct Instance {
  size_t R = 0, signer = 0;
  std::vector<std::vector<uint64_t>> ring;
  std::vector<uint64_t> h, c, s1, s2;
};

inline uint64_t residue(int64_t v) {
  return uint64_t((v % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
}
// LIMBS base-B digits of v.
inline std::vector<uint64_t> limbs(unsigned __int128 v, uint64_t B,
                                   size_t n) {
  std::vector<uint64_t> o(n);
  for (size_t l = 0; l < n; ++l) {
    o[l] = uint64_t(v % B);
    v /= B;
  }
  if (v != 0) throw std::runtime_error("limb overflow");
  return o;
}
// The histogram of VALS over a table of T entries: m[j] = #{i : vals[i] = j}.
template <class Field>
std::vector<typename Field::Elt> logup_multiplicities(
    const Field &F, const std::vector<uint64_t> &vals, size_t T) {
  std::vector<uint64_t> cnt(T, 0);
  for (uint64_t v : vals) cnt.at(v)++;
  std::vector<typename Field::Elt> m(T);
  for (size_t j = 0; j < T; ++j) m[j] = F.of_scalar(cnt[j]);
  return m;
}

// The carrier ring's instance of set S and its host witness: short
// (s1, s2), a random key, c = s1 + h s2 mod q, the signer and the other
// members from the same generator. Falcon-512's (s1, s2) repeat fixed
// patterns; the other sets draw them (instance::short_residue) after the
// key until they are a valid signature.
struct CarrierInstance : Instance {
  std::vector<uint64_t> dq;                       // [n] reduction quotients
  std::vector<std::vector<uint64_t>> a_lo, a_hi;  // s1's magnitude limbs
  FalconEncodingAdvice enc;                       // s2's (mag, high)
  std::vector<uint64_t> sum_lo, sum_hi;           // the norm and complement
  // The range needles in the planner's two tables: kEmuB rows, and
  // kSmallTable rows (s1's magnitude limbs, the low part and the high part,
  // the quotient of mag2 = low2 (mod 128)).
  std::vector<uint64_t> needles, small_needles;
  static constexpr uint64_t kSmallTable = 128;
};

template <class P, class S = Falcon512>
CarrierInstance carrier_instance(size_t R) {
  using RP = FalconRingParams<P, S>;
  constexpr uint64_t kBetaSq = S::kBetaSq;
  CarrierInstance in;
  const size_t n = S::kN;
  const uint64_t B = RP::kEmuB;
  in.R = R;
  const std::vector<int64_t> s1c = {0, 1, -1, 50, -50, 3, -7, 12};
  const std::vector<int64_t> s2c = {0, 1, -1, 20, -20, 5, -9, 2};
  in.s1.resize(n);
  in.s2.resize(n);
  in.h.resize(n);
  in.c.resize(n);
  for (size_t i = 0; i < n; ++i) {
    in.s1[i] = residue(s1c[i % s1c.size()]);
    in.s2[i] = residue(s2c[i % s2c.size()]);
  }
  std::mt19937 g(20260920);
  for (size_t i = 0; i < n; ++i) in.h[i] = g() % kQ;
  if constexpr (instance::kGaussian<S>) {
    do {
      for (size_t i = 0; i < n; ++i) {
        in.s1[i] = instance::short_residue<S>(g);
        in.s2[i] = instance::short_residue<S>(g);
      }
    } while (!instance::valid_signature<S>(in.s1, in.s2));
  }
  const auto t = emulated_ntt::integer_convolution(in.h, in.s2);
  for (size_t i = 0; i < n; ++i)
    in.c[i] = uint64_t((((__int128_t)in.s1[i] + t[i]) % (__int128_t)kQ + kQ) %
                       kQ);
  // The relation's quotient as the assert_mod lowering commits it:
  // c - s1 - h s2 = q (qlo + dq) with qlo = -(1 + n (q - 1)), from the left
  // side c - s1 >= -q and the negacyclic product h s2 <= n (q - 1) q.
  const __int128_t shift = (__int128_t)kQ * (1 + (__int128_t)n * (kQ - 1));
  in.dq.resize(n);
  for (size_t i = 0; i < n; ++i) {
    const __int128_t num =
        (__int128_t)in.c[i] - (__int128_t)in.s1[i] + shift - t[i];
    if (num < 0 || num % kQ != 0)
      throw std::runtime_error("reduction quotient must be exact");
    in.dq[i] = uint64_t(num / kQ);
  }
  in.signer = g() % R;
  in.ring.assign(R, std::vector<uint64_t>(n));
  for (size_t j = 0; j < R; ++j)
    for (size_t k = 0; k < n; ++k) in.ring[j][k] = g() % kQ;
  in.ring[in.signer] = in.h;
  // The norm advice: s1's magnitude and its complement to q / 2, s2's
  // encoding pair, the sum and its complement to beta^2.
  unsigned __int128 sumsq = 0;
  for (size_t i = 0; i < 2 * n; ++i) {
    const uint64_t v = i < n ? in.s1[i] : in.s2[i - n];
    const uint64_t a = v <= kQ / 2 ? v : kQ - v;
    if (i < n) {
      in.a_lo.push_back(limbs(a, CarrierInstance::kSmallTable, RP::kEmuLa));
      in.a_hi.push_back(
          limbs(kQ / 2 - a, CarrierInstance::kSmallTable, RP::kEmuLa));
    }
    sumsq += (unsigned __int128)a * a;
  }
  in.enc = falcon_encoding_advice(in.s2, kQ, S::kHighBudget);
  in.sum_lo = limbs(sumsq, B, RP::kEmuLsum);
  in.sum_hi = limbs(kBetaSq - sumsq, B, RP::kEmuLsum);
  for (size_t i = 0; i < n; ++i)
    for (uint64_t x : limbs(in.dq[i], B, RP::kEmuLdq)) in.needles.push_back(x);
  for (size_t i = 0; i < n; ++i)
    for (size_t l = 0; l < RP::kEmuLa; ++l) {
      in.small_needles.push_back(in.a_lo[i][l]);
      in.small_needles.push_back(in.a_hi[i][l]);
    }
  for (size_t i = 0; i < n; ++i) {
    in.needles.push_back(in.enc.mag[i]);
    in.small_needles.push_back(in.enc.high[i]);
    in.small_needles.push_back(in.enc.mag[i] -
                               kFalconLowRadix * in.enc.high[i]);
  }
  // The budget 128 (J - sum high) below 128 J + 1 and its complement
  // 128 sum high, two digits each (two-sided).
  for (uint64_t x : limbs(kFalconLowRadix * in.enc.slack, B, 2))
    in.needles.push_back(x);
  for (uint64_t x :
       limbs(kFalconLowRadix * (S::kHighBudget - in.enc.slack), B, 2))
    in.needles.push_back(x);
  for (size_t l = 0; l < RP::kEmuLsum; ++l) {
    in.needles.push_back(in.sum_lo[l]);
    in.needles.push_back(in.sum_hi[l]);
  }
  return in;
}

// The carrier spectrum of A: ntt_gadget's own schedule, evaluated on the
// host.
template <class F>
std::vector<typename F::Elt> carrier_spectrum(const F &f,
                                              const std::vector<uint64_t> &a) {
  using EB = EvaluationBackend<F>;
  using ELC = Logic<F, EB>;
  EB bk(f, false);
  ELC lc(&bk, f);
  const auto psi = emulated_ntt::negacyclic_root(f, a.size());
  std::vector<typename ELC::EltW> w;
  for (uint64_t x : a) w.push_back(lc.konst(f.of_scalar(x)));
  ntt_gadget::Sharing sh;
  sh.forward = 0;
  ntt_gadget::transform(lc, w, f.mulf(psi, psi), /*inverse=*/false, sh, psi);
  std::vector<typename F::Elt> out;
  for (auto &x : w) out.push_back(x.elt());
  return out;
}

// The native ring's instance and its host witness: a random c, short (s1, s2),
// the key's spectrum (c^ - s1^) / s2^, the signer and the other members'
// spectra. The statement here holds coefficients: each member is the
// inverse transform of its spectrum.
struct NativeInstance : Instance {
  std::vector<uint64_t> hhat;  // the signer's spectrum (natural order)
  std::vector<std::vector<uint64_t>> spectra;
  FalconEncodingAdvice enc;
};

namespace native_internal {
inline uint64_t modpow(uint64_t a, uint64_t e) {
  uint64_t r = 1;
  a %= kQ;
  for (; e; e >>= 1, a = a * a % kQ)
    if (e & 1) r = r * a % kQ;
  return r;
}
// The native ring's host NTT: psi twist (psi = native_psi(n)), bit
// reversal, then the cyclic Cooley-Tukey stages at omega = psi^2
// (natural-order spectrum).
inline std::vector<uint64_t> host_ntt(std::vector<uint64_t> a) {
  const size_t n = a.size();
  const uint64_t psi = native_psi(n);
  const uint64_t omega = psi * psi % kQ;
  size_t levels = 0;
  for (size_t m = n; m > 1; m >>= 1) ++levels;
  uint64_t w = 1;
  for (size_t j = 0; j < n; ++j) {
    a[j] = a[j] * w % kQ;
    w = w * psi % kQ;
  }
  for (size_t i = 0; i < n; ++i) {
    size_t r = 0;
    for (size_t b = 0; b < levels; ++b) r |= ((i >> b) & 1) << (levels - 1 - b);
    if (i < r) std::swap(a[i], a[r]);
  }
  for (size_t len = 2; len <= n; len *= 2) {
    uint64_t step = 1;
    for (size_t e = 0; e < n / len; ++e) step = step * omega % kQ;
    uint64_t ww = 1;
    for (size_t j = 0; j < len / 2; ++j) {
      for (size_t start = 0; start < n; start += len) {
        const uint64_t u = a[start + j];
        const uint64_t v = a[start + j + len / 2] * ww % kQ;
        a[start + j] = (u + v) % kQ;
        a[start + j + len / 2] = (u + kQ - v) % kQ;
      }
      ww = ww * step % kQ;
    }
  }
  return a;
}
// Its inverse, by the definition: a(x) from the n values at
// x_k = psi^(2k + 1), a_i = n^-1 sum_k y_k x_k^-i.
inline std::vector<uint64_t> host_intt(const std::vector<uint64_t> &y) {
  const size_t n = y.size();
  const uint64_t ninv = modpow(n, kQ - 2);
  const uint64_t psi = native_psi(n);
  std::vector<uint64_t> a(n, 0);
  for (size_t k = 0; k < n; ++k) {
    const uint64_t x = modpow(psi, 2 * k + 1);
    const uint64_t xinv = modpow(x, kQ - 2);
    uint64_t p = 1;
    for (size_t i = 0; i < n; ++i) {
      a[i] = (a[i] + y[k] * p) % kQ;
      p = p * xinv % kQ;
    }
  }
  for (auto &v : a) v = v * ninv % kQ;
  return a;
}
}  // namespace native_internal

template <class P, class S = Falcon512>
NativeInstance native_instance(size_t R) {
  using native_internal::host_intt;
  using native_internal::host_ntt;
  using native_internal::modpow;
  NativeInstance in;
  const size_t n = S::kN;
  in.R = R;
  std::mt19937 g(20260919);
  in.s1.resize(n);
  in.s2.resize(n);
  in.c.resize(n);
  in.hhat.resize(n);
  for (auto &v : in.c) v = g() % kQ;
  const auto chat = host_ntt(in.c);
  for (;;) {
    for (size_t i = 0; i < n; ++i) {
      in.s1[i] = instance::short_residue<S>(g);
      in.s2[i] = instance::short_residue<S>(g);
    }
    if (!instance::valid_signature<S>(in.s1, in.s2)) continue;
    const auto s1hat = host_ntt(in.s1), s2hat = host_ntt(in.s2);
    bool ok = true;
    for (size_t i = 0; i < n; ++i)
      if (s2hat[i] == 0) ok = false;
    if (!ok) continue;
    for (size_t i = 0; i < n; ++i)
      in.hhat[i] = (chat[i] + kQ - s1hat[i]) % kQ *
                   modpow(s2hat[i], kQ - 2) % kQ;
    break;
  }
  in.enc = falcon_encoding_advice(in.s2, kQ, S::kHighBudget);
  in.signer = g() % R;
  in.spectra.assign(R, std::vector<uint64_t>(n));
  for (size_t j = 0; j < R; ++j)
    for (size_t k = 0; k < n; ++k) in.spectra[j][k] = g() % kQ;
  in.spectra[in.signer] = in.hhat;
  in.h = host_intt(in.hhat);
  in.ring.resize(R);
  for (size_t j = 0; j < R; ++j)
    in.ring[j] = j == in.signer ? in.h : host_intt(in.spectra[j]);
  return in;
}

// ----------------------------------------------------------- plan export --

// The plan export (plan_export.h) of system T at ring size R:
// DIR with its realized program (write_plan). Returns the plan's
// path.
template <class P, class T>
std::string export_plan(const std::string &dir, const std::string &config,
                        const std::string &commit, const std::string &run_id,
                        size_t R) {
  const typename T::Env env;
  T t(env, R);
  const auto c = t.compile();
  // The ring statement has no message: msgLen is 0, and the ring size has
  // no field in the schema (a gap); the header's run id names it.
  const compiler::ExportMeta meta{config, P::kId, commit, run_id, 0};
  return write_plan(*c, dir, meta);
}

}  // namespace proofs::gordiehowe::examples::falcon::ring

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_RINGS_FALCON_RING_TESTING_H_
