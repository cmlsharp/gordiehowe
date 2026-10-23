// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Self-test of the wide hash domain on upstream's ZK stack: GF(2^256)
// (gf2k/gf2_256.h) with upstream's LCH14 Reed-Solomon, the SHA-384 Merkle
// and Ligero shadows and the fork's SHA-384 transcript (shadow
// random/transcript.h).  A circuit asserts c = a * b in GF(2^256) on bit
// wires (gf2_256_mul) for private a, b and public c; the honest proof must
// verify, a wrong public c must be rejected, and a proof read back from its
// bytes must verify.  Prints the proof size.
#include <cstdint>
#include <cstdio>
#include <memory>
#include <vector>

#include "arrays/dense.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "gf2k/gf2_256.h"
#include "gf2k/lch14_reed_solomon.h"
#include "lfb_wide/gf2_256_mul.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/readbuffer.h"
#include "util/sha384.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

using namespace proofs;

using F256 = GF2_256<>;
using CBK = CompilerBackend<F256>;
using LC = Logic<F256, CBK>;
using RSF = LCH14ReedSolomonFactory<F256>;

static_assert(std::is_same_v<Transcript, BasicTranscript<proofs::SHA384>>,
              "the shadow transcript is in effect");
static_assert(Digest::kLength == 48, "the shadow Merkle digest is in effect");

int main() {
  set_log_level(ERROR);
  const F256 F;
  QuadCircuit<F256> Q(F);
  const CBK cbk(&Q);
  const LC L(&cbk, F);
  LC::v256 c = L.vinput<256>();
  Q.private_input();
  LC::v256 a = L.vinput<256>();
  LC::v256 b = L.vinput<256>();
  LC::v256 ab;
  gf2_256_mul(L, ab, a, b);
  L.vassert_eq(ab, c);
  auto circuit = Q.mkcircuit(1);

  // Host values: a = x^3 + 1, b = x^255 + x; c = a * b in the field.
  auto bits_of = [&](const F256::Elt& e, std::vector<bool>& out) {
    uint8_t buf[F256::kBytes];
    F.to_bytes_field(buf, e);
    out.resize(256);
    for (size_t i = 0; i < 256; ++i) out[i] = (buf[i / 8] >> (i % 8)) & 1;
  };
  uint8_t ab_bytes[F256::kBytes] = {}, bb_bytes[F256::kBytes] = {};
  ab_bytes[0] = 0x09;
  bb_bytes[0] = 0x02;
  bb_bytes[31] = 0x80;
  const F256::Elt ea = F.of_bytes_field(ab_bytes).value();
  const F256::Elt eb = F.of_bytes_field(bb_bytes).value();
  const F256::Elt ec = F.mulf(ea, eb);
  std::vector<bool> va, vb, vc;
  bits_of(ea, va);
  bits_of(eb, vb);
  bits_of(ec, vc);

  auto fill = [&](Dense<F256>& W, bool full, bool wrong_c) {
    DenseFiller<F256> f(W);
    f.push_back(F.one());
    for (size_t i = 0; i < 256; ++i) {
      bool bit = vc[i] ^ (wrong_c && i == 7);
      f.push_back(bit ? F.one() : F.zero());
    }
    if (!full) return;
    for (size_t i = 0; i < 256; ++i) f.push_back(va[i] ? F.one() : F.zero());
    for (size_t i = 0; i < 256; ++i) f.push_back(vb[i] ? F.one() : F.zero());
  };
  Dense<F256> W(1, circuit->ninputs);
  fill(W, true, false);

  const RSF rsf(F);
  SecureRandomEngine rng;
  const size_t rate = 6, nreq = 64;
  ZkProof<F256> proof(*circuit, rate, nreq);
  ZkProver<F256, RSF> prover(*circuit, F, rsf);
  Transcript tp((const uint8_t*)"wide", 4);
  prover.commit(proof, W, tp, rng);
  const bool pok = prover.prove(proof, W, tp);
  std::vector<uint8_t> buf;
  proof.write(buf, F);

  int failures = 0;
  auto verify = [&](bool wrong_c) {
    ZkProof<F256> rp(*circuit, rate, nreq);
    ReadBuffer rb(buf);
    if (!rp.read(rb, F)) return false;
    Dense<F256> pub(1, circuit->ninputs);
    fill(pub, false, wrong_c);
    ZkVerifier<F256, RSF> v(*circuit, rsf, rate, nreq, F);
    Transcript tv((const uint8_t*)"wide", 4);
    v.recv_commitment(rp, tv);
    return v.verify(rp, pub, tv);
  };
  const bool ok = pok && verify(false);
  const bool rej = !verify(true);
  std::printf("%s honest proof verifies (proof %zu bytes, digest %zu)\n",
              ok ? "PASS" : "FAIL", buf.size(), Digest::kLength);
  std::printf("%s wrong public c rejected\n", rej ? "PASS" : "FAIL");
  failures += !ok + !rej;
  std::printf("failures=%d\n", failures);
  return failures == 0 ? 0 : 1;
}
