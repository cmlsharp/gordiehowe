// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Falcon-512 proof of possession, emulated arm. The prover
// shows it holds a nonce, a message and s2 such that, for the public key h
// and c = HashToPoint(nonce || message), s1 = c - s2 h mod q satisfies
// ||(s1, s2)||^2 <= beta^2 and s2 fits Falcon's compressed encoding.
// Domain H hashes (falcon_hash.h); the samples cross into domain A by one
// MAC equality. Domain A is the parameter set's Goldilocks extension,
// where every Falcon value is a small integer: the key equation is a
// congruence mod q over the integers with a committed quotient
// (assert_mod), and the magnitudes, the encoding budget and the norm are
// integer equations with range requests.
//
// The relation and magnitude gadgets also serve the Falcon rings, with a
// committed key (CommittedKey, FalconBounds). The generators' host code is
// in falcon_emulated_witness.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/examples/falcon/falcon_emulated_witness.h"
#include "gordiehowe/examples/falcon/falcon_hash.h"
#include "gordiehowe/examples/falcon/falcon_params.h"
#include "gordiehowe/examples/shared/setup.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/ops/spectral.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/relation.h"
#include "gordiehowe/system.h"
#include "circuits/ntt/falcon_ntt.h"

namespace proofs::gordiehowe::examples::falcon::emulated {

// ------------------------------------------------------------ parameters --

using examples::falcon::kBetaSq;
using examples::falcon::kBias;
using examples::falcon::kCutoff;
using examples::falcon::kHighBudget;
using examples::falcon::kLowRadix;
using examples::falcon::kMagnitudeLimit;
using examples::falcon::kN;
using examples::falcon::kNonceBytes;
using examples::falcon::kOutBytes;
using examples::falcon::kQ;
using examples::falcon::kSamples;

// The committed-key relation's bias and its quotient's honest bound n and
// maximum m, for the field characteristic p, with checked 128-bit
// integers. The range lowering selects N in [n, m]. The bias is kBias by
// default; a ring passes its own (FalconRingParams::kBias), whose c is
// reduced below q.
struct Interval {
  Bound honest;
  Bound max;
};
struct FalconBounds {
  Bound bias = 0;
  Interval quot;
  static FalconBounds derive(Bound p, Bound bias = kBias) {
    const Bound q = kQ;
    FalconBounds r;
    r.bias = bias;
    r.quot = {(2 * bias + q - 1) / q, (p - 1) / q + 1};
    return r;
  }
};

// --------------------------------------------------------------- gadgets --

// The key: the statement member HHAT, 512 NTT coordinates, each
// canonical below q (the member's codec: a malformed key fails
// verification), as Subfield values of A.
template <class D, class M>
auto falcon_key(D &A, const In<M> &hhat) {
  hhat.check(computes("falcon_key_canonical", {kQ}),
             [](const std::vector<uint16_t> &k) {
               for (uint16_t x : k)
                 if (x >= kQ) return false;
               return true;
             });
  return hhat.values(A);
}

// FalconDecodeSpectrum: h = INTT(key) over Z_q, the key's coefficients,
// computed from the statement member HHAT's bytes (each coordinate a
// little-endian 16-bit integer): a cached statement value bounded by q.
// The inverse transform reduces every coefficient mod q, so an honest
// statement always meets the bound.
template <class D, class AF, class M>
Ref<AF, Subfield<>, Public> decode_key(const Scope &s, D &A,
                                       const In<M> &hhat) {
  const std::vector<uint64_t> z = falcon_ntt_zetas(kN, kQ);
  return s[A]
      .pub(Subfield{}, "coefficients", kN, depends_on(hhat),
           computes("falcon_decode_spectrum", {kN, kQ}),
           [z](const std::vector<uint8_t> &b) {
             std::vector<uint64_t> k(b.size() / 2);
             for (size_t i = 0; i < k.size(); ++i)
               k[i] = uint64_t(b[2 * i]) | (uint64_t(b[2 * i + 1]) << 8);
             return host::decode_spectrum(k, z);
           })
      .cache()
      .bounded(kQ);
}

// The crossing: c_A, the samples c_H carried into A (a Bit copy and the
// MAC equality across the domains). Returns c_A.
template <class D, class HF, class P>
auto crossing(const Scope &s, D &A, const Ref<HF, Bit, P> &c_H) {
  return c_H.to(s[A], "c_A");
}

// The key as the signature relation reads it.
//   PublicKey     the proof of possession's statement: its NTT coordinates
//                 (s1's generator reads them) and its coefficients h, read
//                 through NegacyclicConv(h): the relation is one affine
//                 row per coefficient.
//   CommittedKey  a ring's selected member: its spectrum under the staged
//                 transform NTT, read through SpectralProduct: the relation
//                 is one circuit: the transforms of s2 and of the
//                 left-hand side, and n pointwise products.
template <class AF>
struct PublicKey {
  Ref<AF, Subfield<>, Public> spectrum;
  Ref<AF, Subfield<>, Public> h;
};
template <class AF>
struct CommittedKey {
  Ref<AF, Subfield<>, Committed> spectrum;
  Op<AF> ntt;
};

// The challenge c as the relation reads it: the integers of the selected
// 16-bit samples (Bit [N][16], from domain H through the crossing) or
// the coefficients themselves (Subfield [N], a statement value).
template <class AF, class P>
Lin<AF> challenge_value(const Ref<AF, Bit, P> &c) {
  return c.from_digits(2);
}
template <class AF, class P>
Lin<AF> challenge_value(const Ref<AF, Subfield<>, P> &c) {
  return Lin<AF>(c);
}

// The signature relation of a public key: s1 = c - s2 h mod q, stated as
//   s1 + h s2 = c (mod q)
// over the integers, h s2 through NegacyclicConv(h), h's coefficients below
// q. The assert_mod lowering reads s1 and s2 in [0, q] (the magnitudes'
// roots), derives the quotient's interval and commits it with the
// relation as one affine row per coefficient. s1 has no range request: the
// magnitudes bound it. Returns s1.
template <class D, class AF, class C>
Ref<AF, Subfield<>, Committed> signature_relation(
    const Scope &s, D &A, const PublicKey<AF> &key, const C &c,
    const Ref<AF, Subfield<>, Committed> &s2) {
  using U64s = std::vector<uint64_t>;
  const U64s z = falcon_ntt_zetas(kN, kQ);
  const auto s1 = s[A].priv(
      Subfield{}, "s1", kN, depends_on(key.spectrum, c, s2),
      [z](const U64s &k, const Tensor<uint64_t> &cv, const U64s &s2v) {
        return host::s1_of(k, host::challenge_integers(cv), s2v, z);
      });
  assert_mod(s1 + ops::NegacyclicConv(key.h, ops::EntryBound{kQ})(s2),
             challenge_value(c), kQ, s.name("equation"));
  return s1;
}

// The signature relation of a committed key (a ring's selected member):
// s1 = c - s2 h mod q and the quotient, with
//   bias + c - h s2 - s1 - q quot = 0
// over the integers (FalconBounds' bias and quotient interval), h s2 as a
// spectral circuit. s1 has no range request: the magnitudes bound it.
// Returns s1.
template <class D, class AF, class C>
Ref<AF, Subfield<>, Committed> signature_relation(
    const Scope &s, D &A, const CommittedKey<AF> &key, const C &c,
    const Ref<AF, Subfield<>, Committed> &s2, const FalconBounds &b) {
  using U64s = std::vector<uint64_t>;
  using Elt = typename AF::Elt;
  const U64s z = falcon_ntt_zetas(kN, kQ);
  const uint64_t bias = uint64_t(b.bias);
  const AF *pa = &A.field();
  const auto t = key.ntt.spec->staged;
  const std::vector<size_t> cdims = c.dims();
  // Field form: the spectrum is read as elements; c, s2 and s1 are
  // canonical integers below 2^16.
  auto ints = [pa](const std::vector<Elt> &v) {
    uint64_t ok = 1;
    U64s out(v.size());
    for (size_t i = 0; i < v.size(); ++i)
      out[i] = uint64_t(nat_of_ct(*pa, v[i], ok));
    return out;
  };
  auto c_ints = [ints, cdims](const std::vector<Elt> &cv) {
    const U64s v = ints(cv);
    return host::challenge_integers(Tensor<uint64_t>(v, cdims));
  };
  auto elts = [pa](const U64s &v) {
    std::vector<Elt> out(v.size());
    for (size_t i = 0; i < v.size(); ++i) out[i] = pa->of_scalar(v[i]);
    return out;
  };
  const auto s1 = s[A].priv(
      Subfield{}, "s1", kN, depends_on(key.spectrum, c, s2),
      [=](const std::vector<Elt> &spec, const std::vector<Elt> &cv,
          const std::vector<Elt> &s2v) {
        U64s hhat = host::key_coefficients(*pa, *t, spec);
        falcon_ntt_ref<kQ>(hhat, z);
        return elts(host::s1_of(hhat, c_ints(cv), ints(s2v), z));
      });
  const auto quot = s[A].priv(
      Subfield{}, "quot", kN, depends_on(key.spectrum, c, s2, s1),
      [=](const std::vector<Elt> &spec, const std::vector<Elt> &cv,
          const std::vector<Elt> &s2v, const std::vector<Elt> &s1v) {
        return elts(host::quot_of(host::key_coefficients(*pa, *t, spec),
                                  c_ints(cv), ints(s2v), ints(s1v), bias));
      });
  // Planned change 5 (docs/planned-changes.md): assert_mod, spectral side.
  ops::assert_spectral(s, "equation",
                       bias + challenge_value(c) - s1 - kQ * quot,
                       ops::SpectralProduct(key.spectrum, s2, key.ntt));
  assert_range(quot, b.quot.honest, MaxBound{b.quot.max}, s.name("quot"));
  return s1;
}

// The centered magnitude mag = |x| mod q of the vector X: committed as NM,
// mag in {x, q - x} (degree 2, so in the circuit) as the predicate X_NAME,
// and mag below LIMIT. Returns mag.
template <class D, class AF>
Ref<AF, Subfield<>, Committed> centered_magnitude(
    const Scope &s, D &A, const Ref<AF, Subfield<>, Committed> &x,
    const std::string &x_name, const std::string &nm, uint64_t limit) {
  const auto mag =
      s[A].priv(Subfield{}, nm, kN, depends_on(x), host::magnitude);
  assert_zero((mag - x) * (mag - (kQ - x)), s.name(x_name));
  assert_range(mag, limit, s.name(nm));
  return mag;
}

// The centered magnitudes of s1 and s2: the norm reads both, the encoding
// mag2.
template <class F>
struct Magnitudes {
  Ref<F, Subfield<>, Committed> mag1;
  Ref<F, Subfield<>, Committed> mag2;
};
// Proves mag = |x| centered mod q for x = s1 and x = s2, one vector at a
// time (centered_magnitude): mag1 below q / 2 + 1, which also pins s1 to
// [0, q], and mag2 below the encoding's magnitude limit b = 2048. The
// Falcon rings use the same gadget.
template <class D, class AF>
Magnitudes<AF> magnitudes(const Scope &s, D &A,
                          const Ref<AF, Subfield<>, Committed> &s1,
                          const Ref<AF, Subfield<>, Committed> &s2) {
  const auto mag1 = centered_magnitude(s, A, s1, "s1", "mag1", kQ / 2 + 1);
  const auto mag2 = centered_magnitude(s, A, s2, "s2", "mag2", kMagnitudeLimit);
  return {mag1, mag2};
}

// The encoding budget of Falcon's compressed encoding: the low part
// low2 = mag2 mod 128, below 128, and mag2 = low2 (mod 128), whose quotient
// is the high part mag2 / 128; the high parts sum to at most J, stated over
// the integers as 128 J - sum (mag2 - low2) in [0, 128 J].
template <class D, class AF>
void assert_encoding_budget(const Scope &s, D &A,
                            const Ref<AF, Subfield<>, Committed> &mag2) {
  const auto low2 =
      s[A].priv(Subfield{}, "low2", kN, depends_on(mag2), host::low_of);
  assert_range(low2, kLowRadix, s.name("low2"));
  assert_mod(mag2, low2, kLowRadix, s.name("high2"));
  assert_range(kLowRadix * kHighBudget - mag2.sum() + low2.sum(),
               kLowRadix * kHighBudget + 1, s.name("budget"));
}

// The norm: squares = sum mag1^2 + sum mag2^2 (the circuit) and
// squares <= beta^2.
template <class D, class AF>
void assert_norm(const Scope &s, D &A,
                 const Ref<AF, Subfield<>, Committed> &mag1,
                 const Ref<AF, Subfield<>, Committed> &mag2) {
  const auto squares = s[A].priv(Subfield{}, "squares", 1,
                                   depends_on(mag1, mag2),
                                   host::sum_of_squares);
  assert_zero(squares - (mag1 * mag1).sum() - (mag2 * mag2).sum(), s.name("sum"));
  assert_range(squares, kBetaSq + 1, s.name("bound"));
}

// ---------------------------------------------------------------- system --

// The relation over the statement ST and the witness W. Each range table
// holds its needles in request order, so the gadgets are declared in a
// fixed order: the signature relation, the magnitudes, the encoding
// budget, the norm.
template <class P>
void falcon_emulated_relation(typename Env<P>::Sys &cs, const Env<P> &env,
                              FalconStatement<In> st, FalconWitness<In> w,
                              size_t max_bytes) {
  using AF = typename Env<P>::AF;
  const auto hash = examples::falcon::falcon_hash_domain(
      cs, domain_profile<P>(env.hf, env.rsh), w.nonce, w.message,
      w.msg_length, max_bytes);
  auto &A = cs.domain(domain_profile<P>(env.af, env.rsa.factory()), "A");
  const auto key = falcon_key(A, st.hhat);
  const auto h =
      decode_key<std::decay_t<decltype(A)>, AF>(cs.scope("key"), A, st.hhat);
  const auto c_A = crossing(cs.scope("crossing"), A, hash.c_H);
  const auto s2 = A.priv(Subfield{}, w.s2);
  const auto s1 = signature_relation(cs.scope("signature"), A,
                                     PublicKey<AF>{key, h}, c_A, s2);
  const auto mag = magnitudes(cs.scope("magnitudes"), A, s1, s2);
  assert_encoding_budget(cs.scope("encoding"), A, mag.mag2);
  assert_norm(cs.scope("norm"), A, mag.mag1, mag.mag2);
}

// The relation for messages of at most MAX_BYTES bytes, compiled under
// BUILD.
template <class P>
Relation<FalconStatement<Value>, FalconWitness<Value>> falcon_emulated(
    const Env<P> &env, size_t max_bytes, const BuildOptions &build = {}) {
  return compile<FalconStatement, FalconWitness>(
      build.profile(compile_profile<P>()),
      [&env, max_bytes](typename Env<P>::Sys &cs, FalconStatement<In> st,
                        FalconWitness<In> w) {
        falcon_emulated_relation<P>(cs, env, st, w, max_bytes);
      },
      "falcon-emulated-possession", FalconStatement<Value>{},
      falcon_witness_shape(max_bytes), build.compile);
}

}  // namespace proofs::gordiehowe::examples::falcon::emulated

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_FALCON_FALCON_EMULATED_H_
