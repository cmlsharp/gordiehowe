// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe tests (gordiehowe_batch_test*.cc, one binary): the
// characteristic-2 domain (GF(2^256), source subfield GF(2^16)), its profile,
// the Goldilocks^4 aliases and the SHAKE256 system they share. Each test file
// has its own copy (anonymous namespace).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_BATCH_TEST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_BATCH_TEST_H_

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <random>
#include <string>
#include <type_traits>
#include <vector>

#include "gordiehowe/compile_error_testing.h"
#include "algebra/fp_goldilocks4.h"
#include "gordiehowe/examples/shared/keccak_host.h"
#include "algebra/reed_solomon_fp.h"
#include "gordiehowe/examples/shared/packed_bits.h"
#include "params/param_sets.h"
#include "params/param_sets_testing.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/instances.h"
#include "gordiehowe/system.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {


using HF = GF2_256<>;
using HElt = HF::Elt;
using RSH = LCH14ReedSolomonFactory<HF>;
using Vec = std::vector<HElt>;
// The systems of one binary domain; tests with more fields name their own.
using Sys = ConstraintSystem<SHA384, HF>;
using SysValue = Sys::Value;
using Assignment = Sys::Assignment;
using ProveOptions = Sys::ProveOptions;

// The compiler tier, for tests that exercise the GKR circuit itself (its
// token circuits, the wires of bit views, its input claim).
struct L : compiler::Lowering {
  using compiler::Lowering::gkr;
};

// BLOCK_ENC = kSearch: the packed-layout search of the PQ H halves
// (h_block_enc).
constexpr size_t kSearch = ~size_t(0);

// The profile of an H domain over field G with protocol hash PH.
template <class G, class PH>
DomainProfile<G, LCH14ReedSolomonFactory<G>, PH> h_profile(
    const G &g, const LCH14ReedSolomonFactory<G> &rs, size_t rate, size_t nreq,
    size_t block_enc) {
  DomainProfile<G, LCH14ReedSolomonFactory<G>, PH> p;
  p.f = &g;
  p.rsf = &rs;
  p.field_name = "GF(2^" + std::to_string(G::kBits) + ")";
  p.rate = rate;
  p.nreq = nreq;
  p.has_subfield = true;
  p.prime = Space::kPrime;
  p.rates = param_sets::placement_rates<G>();
  if (block_enc == kSearch) {
    p.block_enc = [rate, nreq](const Circuit<G> &c, size_t, size_t) {
      return h_block_enc<PH>("GH-H", c, rate, nreq);
    };
  } else if (block_enc) {
    p.block_enc = [block_enc](const Circuit<G> &, size_t, size_t) {
      return block_enc;
    };
  }
  return p;
}

struct Env {
  HF hf;
  RSH rs{hf};
  DomainProfile<HF, RSH, SHA384> profile(size_t rate = 4, size_t nreq = 64,
                                 size_t block_enc = 0) const {
    return h_profile<HF, SHA384>(hf, rs, rate, nreq, block_enc);
  }
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}

// A prover that changes zerocheck message AT of the first batch before it
// is absorbed. The transcript absorbs the changed message, but the later
// rounds are not recomputed from it, so this tests a tampered message (like
// a byte flip), not an adaptive cheater.
bool tampered_message_accepted(const Sys::Prepared &prep, const Assignment &w,
                               size_t at) {
  ProveOptions opt;
  opt.batch_tamper = [at](size_t d, size_t b, SysValue &m) {
    if (d != 0 || b != 0) return;
    auto &v = std::get<Vec>(m);
    env().hf.add(v.at(at), env().hf.one());
  };
  SecureRandomEngine rng;
  return prep.verify(prep.prove(w, rng, opt));
}


using AF = Fp64G4;
using AElt = AF::Elt;
using AVec = std::vector<AElt>;
using RSA = BasicFpReedSolomon<AF>;

std::vector<uint8_t> shake_ref(const std::vector<uint8_t> &in, size_t out) {
  KeccakHost host;
  KeccakSpongeHost sponge(host);
  return sponge.hash(kShake256, in, out);
}

// SHAKE256 of a random MSG_BYTES message, squeezed to OUT_BYTES and read
// through the output bit view, over field G with protocol hash PH and the
// packing tree's D_MAX.
template <class G, class PH>
struct BasicShakeSystem {
  using Elt = typename G::Elt;
  using Vec = std::vector<Elt>;
  G f;
  LCH14ReedSolomonFactory<G> rs{f};
  using Sys = ConstraintSystem<PH, G>;
  using Assignment = typename Sys::Assignment;
  Sys cs{"gordiehowe-m2-shake256"};
  Domain<G> *H;
  Ref<G, Bit, Committed> msg;
  Ref<G> digest;
  lib::keccak::Shake256<G> sh;
  std::vector<uint8_t> in;
  size_t nwords;
  BasicShakeSystem(size_t msg_bytes, size_t out_bytes, size_t rate,
                   size_t nreq, size_t block_enc = 0, unsigned width = 16,
                   size_t d_max = 16) {
    auto prof = h_profile<G, PH>(f, rs, rate, nreq, block_enc);
    prof.d_max = d_max;
    declare(prof, msg_bytes, out_bytes);
  }
  // H at the profile MAKE(f, rs) returns, such as the field's default
  // profile (examples/shared/domain_profile.h).
  template <class Make,
            class = std::enable_if_t<std::is_invocable_v<
                Make, const G &, const LCH14ReedSolomonFactory<G> &>>>
  BasicShakeSystem(size_t msg_bytes, size_t out_bytes, Make make) {
    declare(make(f, rs), msg_bytes, out_bytes);
  }
  template <class Profile>
  void declare(const Profile &prof, size_t msg_bytes, size_t out_bytes) {
    H = &cs.domain(prof, "H");
    std::mt19937 g(20261002);
    for (size_t i = 0; i < msg_bytes; ++i) in.push_back(uint8_t(g()));
    nwords = out_bytes / 2;
    digest = H->pub(Field{}, "digest", nwords);
    msg = H->priv(Bit{}, "msg", 8 * msg_bytes);
    sh = lib::keccak::shake256(*H, "shake", msg, out_bytes);
    // The output as bits: each digest word is the packing of sixteen output
    // bits, read through the bit view.
    const G *pf = &f;
    const size_t n = nwords;
    const Ref<G, Bit, Committed> out = sh.out;
    std::vector<typename G::Elt> beta(16);
    for (size_t j = 0; j < 16; ++j) beta[j] = pf->beta(j);
    const Expr<G> words =
        (Expr<G>(Expr<G, Bit>(out.reshape({n, 16}))) * H->constant(beta))
            .sum(1);
    assert_equal(words, digest, "digest").pin(Placement::kCircuit);
  }
  // The words node that round state C of the call is stored as (the
  // words its bit view reads).
  size_t round_words(size_t c) const {
    return cs.graph().nodes.at(sh.states.at(c).id).deps.at(0);
  }
  Assignment statement(bool wrong = false) const {
    const auto out = shake_ref(in, 2 * nwords);
    Vec d;
    for (size_t i = 0; i < nwords; ++i)
      d.push_back(f.of_scalar(uint16_t(out[2 * i] | (out[2 * i + 1] << 8))));
    if (wrong) d[nwords / 2] = f.addf(d[nwords / 2], f.one());
    Assignment st;
    st.set(digest, d);
    return st;
  }
  Assignment witness() const {
    Vec bits;
    for (uint8_t b : in)
      for (size_t i = 0; i < 8; ++i) bits.push_back((b >> i) & 1 ? f.one() : f.zero());
    Assignment w;
    w.set(msg, bits);
    return w;
  }
};
using ShakeSystem = BasicShakeSystem<HF, SHA384>;

}  // namespace
}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TESTS_GORDIEHOWE_BATCH_TEST_H_
