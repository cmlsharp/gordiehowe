// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// SHA-256 of a private message to a public digest, proved alone with
// upstream Longfellow, configured as mdoc's hash circuit
// (circuits/mdoc/mdoc_hash.h, mdoc_generate_circuit.cc):
//  - the circuit is FlatSHA256Circuit::assert_message_hash over the padded
//    message of a public fixed length n: nb = ceil((n + 9) / 64) blocks,
//    the n message bytes private and the padding (0x80, zeros, the 64-bit
//    bit length) and nb constants, so the relation is GordieHowe's
//    SHA-256 relation (sha256_compare_test.cc, lib/sha256.h's fixed-length
//    sha256, which pads with constants); the block witnesses packed by
//    mdoc's BitPlucker of kSHAPluckerBits = 4 bits per element;
//  - the digest is the public input, a v256 with bit i the bit i of the
//    digest as a big-endian integer (mdoc's e);
//  - every private input precedes begin_full_field, so the whole witness
//    lies in the subfield rows, as in mdoc's hash circuit;
//  - the block witnesses from FlatSHA256Witness::
//    transform_and_witness_message (as mdoc_witness.h);
//  - Ligero at mdoc v7's rate 7, block_enc by circuit_maker.cc's optimize()
//    search, LCH14 Reed-Solomon, upstream's ZkProver / ZkVerifier over the
//    serialized proof, and the transcript at version 7. The salts (Merkle
//    nonces) and the transcript hash are upstream's.
// The narrow executable (sha256_driver) runs over upstream's GF(2^128) with
// SHA-256; the wide one (sha256_driver_wide, built with
// baselines/common-wide) over GF(2^256) with common-wide's SHA-384
// transcript and Merkle trees.
//
// Opened columns: kColumns below, per profile and message length.
//
// Usage:
//   sha256_driver test PROFILE          honest proofs and rejections at every
//                                       message length; circuit-level checks
//   sha256_driver stats PROFILE         circuit and Ligero shape per length
//   sha256_driver plan PROFILE MSG T... the tableau at T opened columns
//                                       (block_enc by the search at T)
//   sha256_driver worker PROFILE MSG    one length served to common/bench.py
// PROFILE is narrow (sha256_driver) or wide (sha256_driver_wide).

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <random>
#include <string>
#include <vector>

#include "arrays/dense.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/bit_plucker.h"
#include "circuits/logic/bit_plucker_encoder.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/sha/flatsha256_circuit.h"
#include "circuits/sha/flatsha256_witness.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "ligero/ligero_param.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "sumcheck/prover_layers.h"
#include "util/crypto.h"
#include "util/log.h"
#include "util/panic.h"
#include "util/readbuffer.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"
#if LFB_WIDE_HASH_DOMAIN
#include "gf2k/gf2_256.h"
#endif

// longfellow-baselines: the worker mode of common/bench.py.
#include "bench_worker.h"

namespace proofs {
namespace {

// mdoc_hash.h's kSHAPluckerBits.
constexpr size_t kSHAPluckerBits = 4;
// mdoc v7 (mdoc_zk.h's kLigeroRatev7, ZkSpec version 7).
constexpr size_t kRate = 7;
constexpr size_t kTranscriptVersion = 7;
const uint8_t kSeed[] = "sha256-private-message";

// The message lengths: 503 and 1079 bytes (8 and 17 blocks, the GordieHowe
// sha256-batched and sha256-batched-17 cases), 64 and 2048 bytes (the
// RSA baselines' messages) and 8192 bytes (129 blocks, the GordieHowe
// sha256-batched-8KiB case). FlatSHA256Circuit and FlatSHA256Witness carry
// the block count in 8 bits, so a message has at most 255 blocks (16,311
// bytes).
constexpr size_t kMessages[] = {64, 503, 1079, 2048, 8192};

// The opened columns per message length: the least t meeting the
// profile's per-round target by the round-by-round analysis of
// longfellow-zk's equal-security study (experiments/pq-migration/
// lf-per-round/ldt_move.py t_min: Longfellow's order, untested masks, DKT26
// counts, no subfield term), on the tableau (N, k) the block_enc search
// gives at that t, N = block_enc - (2k - 1) query positions of message
// length k = block. Narrow: the GordieHowe ROM per-round target 2^-113.5
// over GF(2^128); wide: the QROM per-round target 2^-236 over GF(2^256).
struct Columns {
  size_t msg, nreq;
};

struct Narrow {
  using Field = GF2_128<>;
  static constexpr const char* kId = "narrow";
  static constexpr double kTarget = 113.5;
  // 64 B: (1694, 242) at 120, 2^-113.66 (119: 2^-113.48); 503 B:
  // (2800, 400) at 130, 2^-113.66 (129: 2^-113.33); 1079 B: (3626, 518) at
  // 137, 2^-113.59 (136: 2^-113.19); 2048 B: (4095, 585) at 138, 2^-114.08
  // (137: 2^-113.24); 8192 B: (8365, 1195) at 139, 2^-113.52 (138:
  // 2^-112.70).
  static constexpr Columns kColumns[] = {
      {64, 120}, {503, 130}, {1079, 137}, {2048, 138}, {8192, 139}};
};
#if LFB_WIDE_HASH_DOMAIN
struct Wide {
  using Field = GF2_256<>;
  static constexpr const char* kId = "wide";
  static constexpr double kTarget = 236;
  // 64 B: (3493, 499) at 248, 2^-236.37; 503 B: (3486, 498) at 248,
  // 2^-236.45; 1079 B: (4088, 584) at 250, 2^-236.46; 2048 B: (4088, 584)
  // at 250, 2^-236.46 (each 2^-235.4 to 2^-235.6 at one column fewer);
  // 8192 B: (8701, 1243) at 256, 2^-236.34 (255: 2^-235.43).
  static constexpr Columns kColumns[] = {
      {64, 248}, {503, 248}, {1079, 250}, {2048, 250}, {8192, 256}};
};
using Profile = Wide;
#else
using Profile = Narrow;
#endif

size_t columns_of(size_t msg) {
  for (const Columns& c : Profile::kColumns) {
    if (c.msg == msg) return c.nreq;
  }
  return 0;
}

size_t sha_blocks(size_t n) { return (n + 9 + 63) / 64; }

// The fork's sha256_compare_test.cc workload(blocks), at any length: n
// bytes of mt19937(20261004 + blocks); at 503 and 1079 bytes the fork's
// messages.
std::vector<uint8_t> workload(size_t n) {
  std::mt19937 g(20261004 + uint32_t(sha_blocks(n)));
  std::vector<uint8_t> m(n);
  for (auto& b : m) b = uint8_t(g());
  return m;
}

std::vector<uint8_t> sha256_of(const std::vector<uint8_t>& m) {
  SHA256 h;
  h.Update(m.data(), m.size());
  std::vector<uint8_t> d(kSHA256DigestSize);
  h.DigestData(d.data());
  return d;
}

using Clock = std::chrono::steady_clock;
double ms_since(Clock::time_point t0) {
  return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
}

// The block_enc of the smallest proof (circuit_maker.cc's optimize()), over
// every block_enc from 100 to 2^17, as rsa-pkcs1's rsa_zk.cc.
template <class Field>
size_t best_block_enc(const Circuit<Field>& c, size_t nreq) {
  LigeroParam<Field> lp((c.ninputs - c.npub_in) + ZkCommon<Field>::pad_size(c),
                        c.nl, kRate, nreq);
  size_t best = lp.block_enc;
  size_t min_size = lp.layout(best);
  for (size_t e = 100; e <= (1 << 17); e++) {
    size_t sz = lp.layout(e);
    if (sz < min_size) {
      min_size = sz;
      best = e;
    }
  }
  return best;
}

struct Trial {
  double witness, commit, prove, serialize, v_read, verify;
  size_t bytes;
  bool prover_ok, verified;
};

template <class P>
struct System {
  using Field = typename P::Field;
  using Elt = typename Field::Elt;
  using RS = LCH14ReedSolomonFactory<Field>;
  using CB = CompilerBackend<Field>;
  using LC = Logic<Field, CB>;
  using Flat = FlatSHA256Circuit<LC, BitPlucker<LC, kSHAPluckerBits>>;

  const Field F;
  const RS rs;
  // The message length and the circuit's blocks.
  size_t n, nb;
  std::vector<uint8_t> msg, digest;
  std::unique_ptr<Circuit<Field>> c;
  size_t depth = 0, wires = 0, terms = 0;
  size_t nreq, be;
  double compile_ms;

  System(size_t msg_len, size_t t)
      : F(), rs(F), n(msg_len), nb(sha_blocks(msg_len)),
        msg(workload(msg_len)), digest(sha256_of(msg)), nreq(t) {
    auto t0 = Clock::now();
    QuadCircuit<Field> Q(F);
    const CB cbk(&Q);
    const LC lc(&cbk, F);
    const auto e = lc.template vinput<256>();
    Q.private_input();
    // The message bytes, then the block witnesses (mdoc_hash.h's input
    // order without nb).
    std::vector<typename LC::v8> in(64 * nb);
    for (size_t i = 0; i < n; ++i) in[i] = lc.template vinput<8>();
    std::vector<typename Flat::BlockWitness> bw(nb);
    for (auto& b : bw) b.input(lc);
    Q.begin_full_field();
    // The padding of a public length n, and nb, as constants.
    for (size_t i = n; i < 64 * nb; ++i) {
      uint64_t byte = 0;
      if (i == n) byte = 0x80;
      if (i + 8 >= 64 * nb) byte = (uint64_t(n) * 8 >> (8 * (64 * nb - 1 - i))) & 0xff;
      in[i] = lc.template vbit<8>(byte);
    }
    const auto nbw = lc.template vbit<8>(nb);
    const Flat sha(lc);
    sha.assert_message_hash(nb, nbw, in.data(), e, bw.data());
    c = Q.mkcircuit(1);
    depth = Q.depth_;
    wires = Q.nwires_;
    terms = Q.nquad_terms_;
    compile_ms = ms_since(t0);
    be = best_block_enc(*c, nreq);
  }

  // The witness of message m (of length len = n) under the public digest
  // d: 1, d, then the message bytes and the block witnesses.
  // flip_byte >= 0 flips bit 0 of that message byte after the block
  // witnesses are computed; tamper_bw changes one word of the last block's
  // witness.
  void fill(Dense<Field>& W, const uint8_t* m, size_t len,
            const std::vector<uint8_t>& d, int flip_byte = -1,
            bool tamper_bw = false) const {
    check(len == n, "the message has the circuit's length");
    DenseFiller<Field> f(W);
    f.push_back(F.one());
    for (size_t i = 0; i < 32; ++i) f.push_back(d[31 - i], 8, F);
    std::vector<uint8_t> in(64 * nb);
    std::vector<FlatSHA256Witness::BlockWitness> bw(nb);
    uint8_t numb = 0;
    FlatSHA256Witness::transform_and_witness_message(len, m, nb, numb,
                                                     in.data(), bw.data());
    check(numb == nb, "block count");
    if (flip_byte >= 0) in[flip_byte] ^= 1;
    if (tamper_bw) bw[nb - 1].outa[5] ^= 1;
    for (size_t i = 0; i < n; ++i) f.push_back(in[i], 8, F);
    BitPluckerEncoder<Field, kSHAPluckerBits> enc(F);
    for (const auto& b : bw) {
      for (size_t k = 0; k < 48; ++k) f.push_back(enc.mkpacked_v32(b.outw[k]));
      for (size_t k = 0; k < 64; ++k) {
        f.push_back(enc.mkpacked_v32(b.oute[k]));
        f.push_back(enc.mkpacked_v32(b.outa[k]));
      }
      for (size_t k = 0; k < 8; ++k) f.push_back(enc.mkpacked_v32(b.h1[k]));
    }
    check(f.size() == c->ninputs, "witness size");
  }

  // One proof of message m under the prover's digest dp, verified under
  // dv; tamper 1 flips a byte in the middle of the serialized proof.
  Trial run(const std::vector<uint8_t>& m, const std::vector<uint8_t>& dp,
            const std::vector<uint8_t>& dv, int tamper = 0) const {
    Trial tr{};
    SecureRandomEngine rng;
    auto W = Dense<Field>(1, c->ninputs);
    auto t0 = Clock::now();
    fill(W, m.data(), m.size(), dp);
    tr.witness = ms_since(t0);

    Transcript tp(kSeed, sizeof(kSeed), kTranscriptVersion);
    ZkProof<Field> zk(*c, kRate, nreq, be);
    ZkProver<Field, RS> prover(*c, F, rs);
    t0 = Clock::now();
    prover.commit(zk, W, tp, rng);
    tr.commit = ms_since(t0);
    t0 = Clock::now();
    tr.prover_ok = prover.prove(zk, W, tp);
    tr.prove = ms_since(t0);
    if (!tr.prover_ok) return tr;

    t0 = Clock::now();
    std::vector<uint8_t> buf;
    zk.write(buf, F);
    tr.serialize = ms_since(t0);
    tr.bytes = buf.size();
    if (tamper == 1) buf[buf.size() / 2] ^= 1;
    tr.verified = verify(buf, dv, tr);
    return tr;
  }

  // v_read: the proof's parsing; verify: the ZkVerifier's construction,
  // the commitment, the public inputs and the checks.
  bool verify(const std::vector<uint8_t>& proof, const std::vector<uint8_t>& d,
              Trial& tr) const {
    auto t0 = Clock::now();
    ReadBuffer rb(proof);
    ZkProof<Field> vz(*c, kRate, nreq, be);
    if (!vz.read(rb, F) || rb.remaining() != 0) return false;
    tr.v_read = ms_since(t0);
    t0 = Clock::now();
    ZkVerifier<Field, RS> v(*c, rs, kRate, nreq, be, F);
    Transcript tv(kSeed, sizeof(kSeed), kTranscriptVersion);
    v.recv_commitment(vz, tv);
    auto pub = Dense<Field>(1, c->npub_in);
    DenseFiller<Field> pf(pub);
    pf.push_back(F.one());
    for (size_t i = 0; i < 32; ++i) pf.push_back(d[31 - i], 8, F);
    check(pf.size() == c->npub_in, "public input size");
    const bool ok = v.verify(vz, pub, tv);
    tr.verify = ms_since(t0);
    return ok;
  }

  // The tableau at t opened columns: block_enc by the search at t.
  void print_tableau(size_t t) const {
    const size_t e = best_block_enc(*c, t);
    ZkProof<Field> zk(*c, kRate, t, e);
    const size_t k = zk.param.block;
    printf("TABLEAU profile=%s msg=%zu t=%zu block_enc=%zu block=%zu N=%zu "
           "k=%zu nrow=%zu\n",
           P::kId, n, t, e, k, e - (2 * k - 1), k, zk.param.nrow);
    fflush(stdout);
  }

  void print_plan(const char* tag) const {
    ZkProof<Field> zk(*c, kRate, nreq, be);
    const size_t k = zk.param.block;
    printf("CIRCUIT %s profile=%s msg=%zu blocks=%zu nreq=%zu depth=%zu "
           "layers=%zu wires=%zu terms=%zu inputs=%zu public=%zu "
           "subfield_boundary=%zu block_enc=%zu block=%zu N=%zu nrow=%zu "
           "compile_ms=%.1f\n",
           tag, P::kId, n, nb, nreq, depth, c->nl, wires, terms, c->ninputs,
           c->npub_in, c->subfield_boundary, be, k, be - (2 * k - 1),
           zk.param.nrow, compile_ms);
    fflush(stdout);
  }
};

// Whether every output of c (the assert0 wires) is zero at the inputs W.
template <class Field>
bool satisfied(const Circuit<Field>& c, const Dense<Field>& W,
               const Field& F) {
  typename ProverLayers<Field>::inputs in;
  ProverLayers<Field> pl(F);
  auto V = pl.eval_circuit(&in, &c, W.clone(), F);
  if (V == nullptr) return false;
  for (size_t i = 0; i < V->n1_; ++i) {
    if (V->v_[i] != F.zero()) return false;
  }
  return true;
}

int failures = 0;
void expect(bool c, const std::string& what) {
  printf("%s %s\n", c ? "PASS" : "FAIL", what.c_str());
  fflush(stdout);
  if (!c) ++failures;
}

void test_length(size_t n) {
  using Field = Profile::Field;
  System<Profile> sys(n, columns_of(n));
  sys.print_plan("test");
  const std::string nm = std::string(Profile::kId) + " msg=" +
                         std::to_string(n) + ": ";
  const Trial t = sys.run(sys.msg, sys.digest, sys.digest);
  expect(t.prover_ok && t.verified, nm + "honest proof verifies");
  {
    auto d2 = sys.digest;
    d2[5] ^= 0x04;
    const Trial u = sys.run(sys.msg, sys.digest, d2);
    expect(u.prover_ok && !u.verified, nm + "wrong digest: rejected");
  }
  {
    const Trial u = sys.run(sys.msg, sys.digest, sys.digest, 1);
    expect(u.prover_ok && !u.verified, nm + "proof byte flipped: rejected");
  }
  {
    auto m2 = sys.msg;
    m2[3] ^= 1;
    const Trial u = sys.run(m2, sys.digest, sys.digest);
    expect(!u.prover_ok,
           nm + "message not hashing to the digest: prover rejects");
  }
  // Circuit level (no proof).
  const Field& F = sys.F;
  auto W = Dense<Field>(1, sys.c->ninputs);
  sys.fill(W, sys.msg.data(), n, sys.digest);
  expect(satisfied(*sys.c, W, F), nm + "circuit: honest witness satisfied");
  sys.fill(W, sys.msg.data(), n, sys.digest, 7);
  expect(!satisfied(*sys.c, W, F),
         nm + "circuit: message byte changed: unsatisfied");
  sys.fill(W, sys.msg.data(), n, sys.digest, -1, true);
  expect(!satisfied(*sys.c, W, F),
         nm + "circuit: last block's witness changed: unsatisfied");
}

int serve_length(size_t n) {
  const size_t t = columns_of(n);
  if (t == 0) return 2;
  System<Profile> sys(n, t);
  sys.print_plan("worker");
  lfb::info({{"profile", Profile::kId},
             {"msg", std::to_string(n)},
             {"blocks", std::to_string(sys.nb)},
             {"nreq", std::to_string(sys.nreq)},
             {"block_enc", std::to_string(sys.be)}});
  lfb::serve([&]() {
    const Trial t = sys.run(sys.msg, sys.digest, sys.digest);
    lfb::Trial T;
    T.commit_ms = t.commit;
    T.prove_ms = t.prove;
    T.verify_ms = t.verify;
    T.proof_bytes = t.bytes;
    T.ok = t.prover_ok && t.verified;
    T.add("witness", t.witness);
    T.add("serialize", t.serialize);
    T.add("v_read", t.v_read);
    return T;
  });
  return 0;
}

}  // namespace
}  // namespace proofs

int main(int argc, char** argv) {
  using namespace proofs;
  set_log_level(ERROR);
  if (argc < 3 || std::string(argv[2]) != Profile::kId) {
    std::fprintf(stderr,
                 "usage: %s test|stats %s | plan %s MSG T... | worker %s "
                 "MSG\n",
                 argv[0], Profile::kId, Profile::kId, Profile::kId);
    return 2;
  }
  const std::string mode = argv[1];
  if (mode == "test" && argc == 3) {
    for (size_t n : kMessages) test_length(n);
    printf("failures=%d\n", failures);
    return failures == 0 ? 0 : 1;
  }
  if (mode == "stats" && argc == 3) {
    for (size_t n : kMessages) System<Profile>(n, columns_of(n)).print_plan("stats");
    return 0;
  }
  if (mode == "plan" && argc >= 5) {
    const size_t n = strtoul(argv[3], nullptr, 10);
    const System<Profile> sys(n, kRate + 1);
    for (int i = 4; i < argc; ++i) sys.print_tableau(strtoul(argv[i], nullptr, 10));
    return 0;
  }
  if (mode == "worker" && argc == 4) {
    return serve_length(strtoul(argv[3], nullptr, 10));
  }
  std::fprintf(stderr, "unknown mode %s\n", mode.c_str());
  return 2;
}
