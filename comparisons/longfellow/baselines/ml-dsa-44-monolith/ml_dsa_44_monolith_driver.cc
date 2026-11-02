// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA proof of possession (ML-DSA-44, -65 or -87) over upstream's
// monolith circuit, a worker of common/bench.py.
//
// usage: ml_dsa_44_monolith [--param-set SET] [RATE NREQ BLOCK_ENC] [test]
//
// SET is ml-dsa-44 (the default), ml-dsa-65 or ml-dsa-87 (ml_dsa_sets.h);
// the flag may stand anywhere among the arguments.  The Ligero parameters
// default to kLigero below (7 134 8192 at every set); BLOCK_ENC 0 lets
// ZkProof search.
// The last argument test runs three trials instead of serving: the honest
// instance must verify, and the tampered signature (the lowest bit of its
// first z coefficient flipped) and the tampered message (the committed
// message differs from the signed one in one bit), each with the whole
// witness recomputed from it, must be rejected; it exits 0 exactly then.
//
// The statement, GordieHowe's proof of possession's: "I hold a message M of
// private length L <= 32 bytes and an ML-DSA signature on M under the
// public key pk and the public (empty) context", with M and the signature
// private.  One proof over upstream's Fp24_6 = GF(q^6), q = 8380417,
// verifies the whole signature with upstream's MLDSAVerify
// (circuits/tests/pq/ml_dsa/ml_dsa_circuit.h) as ml_dsa_monolith_verify.h
// runs it: SampleInBall over the 272-byte stream, A*z - c*t1*2^d, UseHint
// with the exact Decompose, the norm bounds and SHAKE256(mu || w1') ==
// c_tilde, with mu derived in the circuit as FIPS 204 does,
// mu = SHAKE256(tr || 0 || |ctx| || ctx || M, 64), by upstream's Sha3Circuit
// for M of private length (ml-dsa-44-split's ml_dsa_mu.h).  Upstream's own
// test takes mu as a public input instead.
//
// Upstream's Reed-Solomon encoder for Fp24_6 (ReedSolomonExtensionFactory,
// algebra/reed_solomon_extension.h), upstream's SHA-256 transcript.
//
// The example: the set's benchmark instance (ml-dsa-44-split's
// ml_dsa_benchmark_example.h: a 32-byte message 00..1f, empty context).
//
// Per trial: witness (a detail, outside the totals) = the full witness from
// the instance (ml-dsa-44-split's ml_dsa_host.h HostWitness, the fill),
// commit_ms = ZkProver::commit, prove_ms = ZkProver::prove, verify_ms = the
// statement from pk's bytes (pkDecode, ExpandA, NTT(2^d t1), tr), the
// ZkVerifier's construction (its Reed-Solomon setup), the public inputs,
// recv_commitment and verify.  The circuit is built once, before PQ_READY.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <string>
#include <vector>

#include "algebra/fp24.h"
#include "algebra/fp24_6.h"
#include "algebra/reed_solomon_extension.h"
#include "arrays/dense.h"
#include "bench_worker.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_circuit.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "ml_dsa_benchmark_example.h"
#include "ml_dsa_host.h"
#include "ml_dsa_monolith_verify.h"
#include "ml_dsa_mu.h"
#include "ml_dsa_sets.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/panic.h"
#include "util/readbuffer.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace proofs {
namespace {

using Field6 = Fp24_6;
using CBK = CompilerBackend<Field6>;
using LogicCircuit = Logic<Field6, CBK>;
using RSF = ReedSolomonExtensionFactory;
using ml_dsa::MlDsa44SignatureExample;

// Upstream's ml_dsa_circuit_test: Fp24_6 = Fp24[x]/(x^6 - 7).
constexpr uint32_t kBeta = 7;

// The default Ligero parameters, by ML-DSA-44's rule at every set: rate 7;
// block_enc 8192, the power of two upstream's search (ZkProof without
// block_enc, BLOCK_ENC 0 here) picks for the set's circuit at 134 opened
// columns (8192 at ML-DSA-44, -65 and -87 alike); and 134 opened columns,
// the least number that reaches Longfellow's deployed 2^-108 target on that
// tableau under unique decoding (analysis/screen_run.py's ud_min_t at
// N = block_enc - (2 block - 1) = 6373, k = block = (block_enc + 1) / 9 =
// 910).  The search depends on the set only through the tableau's row
// count, so the defaults coincide.
struct LigeroDefaults {
  size_t rate, nreq, block_enc;
};
template <class Set>
constexpr LigeroDefaults kLigero{7, 134, 8192};

// The first 8 bytes of a circuit's id, in hex.
std::string id_hex(const uint8_t id[/*32*/]) {
  char buf[17];
  for (size_t i = 0; i < 8; ++i) std::snprintf(buf + 2 * i, 3, "%02x", id[i]);
  return std::string(buf, 16);
}

// Public: pk, then ctx.  Private: the signature, upstream's verification
// witness, the SampleInBall stream's second block witness, M (kMax bytes),
// its in-message flags, and the block witnesses of mu's SHAKE256.
template <class Set>
std::unique_ptr<Circuit<Field6>> make_circuit(const Field6& f6,
                                              const MlDsa44SignatureExample& ex,
                                              size_t* nquad, size_t* depth) {
  using Params = typename Set::Reference;
  using VerifyCircuit = MLDSAVerify<LogicCircuit, Field6, Params>;
  constexpr size_t kMax = ml_dsa_host::kMaxMessageBytes;
  QuadCircuit<Field6> Q(f6);
  const CBK cbk(&Q);
  const LogicCircuit LC(&cbk, f6);
  VerifyCircuit verify(LC);

  auto pk = std::make_unique<typename VerifyCircuit::Pk>();
  pk->input(LC);
  std::vector<LogicCircuit::v8> ctx(ex.ctx.size());
  for (auto& byte : ctx) byte = LC.vinput<8>();

  Q.private_input();
  auto sig = std::make_unique<typename VerifyCircuit::SignatureW>();
  sig->input(LC);
  auto w = std::make_unique<typename VerifyCircuit::Witness>();
  w->c_prime_tilde_bws_.resize(Set::kCPrimeTildeBlocks);
  w->input(LC);
  std::vector<Sha3Circuit<LogicCircuit>::BlockWitness> sib_extra(
      ml_dsa_host::kSibBytes / 136 - 1);
  for (auto& bw : sib_extra) bw.input(LC);

  std::vector<LogicCircuit::v8> msg(kMax);
  for (auto& byte : msg) byte = LC.vinput<8>();
  std::vector<LogicCircuit::BitW> flags(kMax);
  for (auto& flag : flags) flag = LC.input();
  std::vector<Sha3Circuit<LogicCircuit>::BlockWitness> mu_bws(
      lfb::shake256_private_length_blocks(ml_dsa_host::kMuPrefixBytes, kMax,
                                          64));
  for (auto& bw : mu_bws) bw.input(LC);
  auto mu = ml_dsa_derive_mu(LC, pk->tr, ctx, msg, flags, mu_bws);

  ml_dsa_baseline::assert_valid_signature_on_mu<Params,
                                                ml_dsa_host::kSibBytes>(
      LC, verify, *pk, *sig, mu, *w, sib_extra);
  auto c = Q.mkcircuit(1);
  *nquad = Q.nquad_terms_;
  *depth = Q.depth_;
  return c;
}

// The instance a trial proves: the benchmark example, or a tampered copy.
struct Instance {
  std::vector<uint8_t> pk, sig, msg, ctx;
};

template <class Set>
int run(size_t rate, size_t nreq, size_t block_enc, bool test) {
  using Params = typename Set::Reference;
  using HostWitness = ml_dsa_host::HostWitness<Params>;
  using Statement = ml_dsa_host::Statement<Params>;
  set_log_level(ERROR);
  const Fp24& fq = ml_dsa::Fq();
  const Field6 f(fq, kBeta);
  const MlDsa44SignatureExample& ex = ml_dsa_sets::benchmark_example<Set>();
  const Instance honest{ex.pkey, ex.sig, ex.msg, ex.ctx};
  Instance inst = honest;

  size_t nquad = 0, depth = 0;
  auto circuit = make_circuit<Set>(f, ex, &nquad, &depth);

  // The full witness from the instance (pk, signature, message, context):
  // ml_dsa_host.h's HostWitness (pk and signature decoding, ExpandA, tr,
  // SampleInBall, the NTTs, mu's and c_tilde's block witnesses) and the
  // fill.  Computed here once and again in every trial, timed as the
  // witness.  fill_witness is fill_pk followed by upstream's private
  // witness; with an empty context the ctx slots between them are absent.
  check(ex.ctx.empty(), "the benchmark example has an empty context");
  std::unique_ptr<HostWitness> wgp;
  bool inst_verified = false;
  Dense<Field6> W(1, circuit->ninputs);
  auto witness = [&]() {
    wgp = std::make_unique<HostWitness>();
    auto& wg = *wgp;
    check(wg.compute(inst.pk, inst.sig, inst.msg, inst.ctx, &inst_verified),
          "ML-DSA witness");
    DenseFiller<Field6> filler(W);
    filler.push_back(f.one());
    wg.fill_witness(filler, f);
    for (size_t b = 1; b < wg.sib_bws_.size(); ++b)
      Sha3Witness::fill_witness(filler, wg.sib_bws_[b], f);
    for (uint8_t byte : wg.msg_) filler.push_back(byte, 8, f);
    for (uint8_t flag : wg.in_message_) filler.push_back(flag ? f.one() : f.zero());
    for (const auto& bw : wg.mu_bws_) Sha3Witness::fill_witness(filler, bw, f);
    check(filler.size() == circuit->ninputs, "witness size");
  };
  witness();
  check(inst_verified, "the benchmark example verifies");

  const RSF rsf(fq);
  SecureRandomEngine rng;
  // BLOCK_ENC 0: upstream's constructors without block_enc, which search it.
  auto make_proof = [&]() {
    return block_enc == 0
               ? std::make_unique<ZkProof<Field6>>(*circuit, rate, nreq)
               : std::make_unique<ZkProof<Field6>>(*circuit, rate, nreq,
                                                   block_enc);
  };
  auto make_verifier = [&]() {
    return block_enc == 0
               ? std::make_unique<ZkVerifier<Field6, RSF>>(*circuit, rsf, rate,
                                                           nreq, f)
               : std::make_unique<ZkVerifier<Field6, RSF>>(
                     *circuit, rsf, rate, nreq, block_enc, f);
  };
  {
    auto probe_ptr = make_proof();
    const ZkProof<Field6>& probe = *probe_ptr;
    ::lfb::info({{"scheme", Set::kName},
                 {"field", "Fp24_6"},
                 {"rate", std::to_string(rate)},
                 {"nreq", std::to_string(nreq)},
                 {"block_enc", std::to_string(probe.param.block_enc)},
                 {"block", std::to_string(probe.param.block)},
                 {"nrow", std::to_string(probe.param.nrow)},
                 {"ninputs", std::to_string(circuit->ninputs)},
                 {"npub_in", std::to_string(circuit->npub_in)},
                 {"nl", std::to_string(circuit->nl)},
                 {"nquad_terms", std::to_string(nquad)},
                 {"depth", std::to_string(depth)},
                 {"id", id_hex(circuit->id)},
                 {"msg_bytes", std::to_string(ml_dsa_host::kMaxMessageBytes)},
                 {"mu_blocks", std::to_string(wgp->mu_bws_.size())}});
  }

  auto trial = [&]() {
    ::lfb::Trial T;
    ::lfb::Marks M;
    witness();
    T.add("witness", M.mark());
    auto proof_ptr = make_proof();
    ZkProof<Field6>& proof = *proof_ptr;
    ZkProver<Field6, RSF> prover(*circuit, f, rsf);
    Transcript tp((const uint8_t*)"test", 4);
    T.add("prover_setup", M.mark());
    prover.commit(proof, W, tp, rng);
    T.commit_ms = M.mark();
    const bool ok = prover.prove(proof, W, tp);
    T.prove_ms = M.mark();
    std::vector<uint8_t> buf;
    proof.write(buf, f);
    T.proof_bytes = buf.size();
    T.add("serialize", M.mark());

    auto received_ptr = make_proof();
    ZkProof<Field6>& received = *received_ptr;
    ReadBuffer rb(buf);
    const bool read_ok = received.read(rb, f);
    T.add("v_proof_read", M.mark());
    // The statement from the key's bytes: A_hat, NTT(2^d t1), tr.
    const Statement st = Statement::of_pk(inst.pk);
    auto verifier_ptr = make_verifier();
    ZkVerifier<Field6, RSF>& verifier = *verifier_ptr;
    Dense<Field6> pub(1, circuit->ninputs);
    {
      DenseFiller<Field6> filler(pub);
      filler.push_back(f.one());
      st.fill_pk(filler, f);
      for (uint8_t byte : inst.ctx) filler.push_back(byte, 8, f);
      check(filler.size() == circuit->npub_in, "public input size");
    }
    Transcript tv((const uint8_t*)"test", 4);
    const double v_setup = M.mark();
    verifier.recv_commitment(received, tv);
    const double v_recv = M.mark();
    const bool vok = read_ok && verifier.verify(received, pub, tv);
    const double v_verify = M.mark();
    T.add("v_setup", v_setup);
    T.add("v_recv_commitment", v_recv);
    T.add("v_verify", v_verify);
    T.verify_ms = v_setup + v_recv + v_verify;
    // Opened tableau entries the proof carries as GF(q) elements (4 bytes)
    // rather than Fp24_6 ones (24 bytes): ZkProof's run-length encoding.
    size_t opened_subfield = 0;
    for (const auto& e : proof.com_proof.req) {
      if (f.in_subfield(e)) ++opened_subfield;
    }
    T.add("opened_entries", double(proof.com_proof.req.size()));
    T.add("opened_subfield", double(opened_subfield));
    T.add("nrow", double(proof.param.nrow));
    T.add("block", double(proof.param.block));
    T.ok = ok && vok;
    return T;
  };

  if (!test) {
    ::lfb::serve(trial);
    return 0;
  }
  // The tampered instances: the lowest bit of z[0][0]'s encoding (the byte
  // after c_tilde, sigEncode's BitPack of gamma1 - z), and the message's
  // first bit.
  Instance bad_sig = honest, bad_msg = honest;
  bad_sig.sig[Params::c_tilde_bytes] ^= 1;
  bad_msg.msg[0] ^= 1;
  auto run_on = [&](const Instance& i, const char* name) {
    inst = i;
    const ::lfb::Trial T = trial();
    std::printf("%s: signature verifies %d, proof %s\n", name,
                inst_verified ? 1 : 0, T.ok ? "accepted" : "rejected");
    std::fflush(stdout);
    return T.ok;
  };
  const bool h = run_on(honest, "honest");
  const bool s = run_on(bad_sig, "tamper_sig");
  const bool m = run_on(bad_msg, "tamper_msg");
  std::printf("TEST %s monolith: %s\n", Set::kName,
              (h && !s && !m) ? "PASS" : "FAIL");
  return (h && !s && !m) ? 0 : 1;
}

}  // namespace
}  // namespace proofs

using namespace proofs;

int main(int argc, char** argv) {
  std::vector<std::string> args(argv + 1, argv + argc);
  std::string set = ml_dsa_sets::MlDsa44::kName;
  bool test = false;
  if (ml_dsa_sets::take_param_set(args, set) && !args.empty() &&
      args.back() == "test") {
    test = true;
    args.pop_back();
  }
  if (!ml_dsa_sets::take_param_set(args, set) ||
      (args.size() != 0 && args.size() != 3)) {
    std::fprintf(stderr,
                 "usage: %s [--param-set ml-dsa-44|ml-dsa-65|ml-dsa-87] "
                 "[RATE NREQ BLOCK_ENC] [test]\n",
                 argv[0]);
    return 2;
  }
  int rc = 2;
  if (!ml_dsa_sets::with_param_set(set, [&](auto s) {
        using Set = decltype(s);
        LigeroDefaults l = kLigero<Set>;
        if (args.size() == 3) {
          l.rate = std::strtoull(args[0].c_str(), nullptr, 10);
          l.nreq = std::strtoull(args[1].c_str(), nullptr, 10);
          l.block_enc = std::strtoull(args[2].c_str(), nullptr, 10);
        }
        rc = run<Set>(l.rate, l.nreq, l.block_enc, test);
      })) {
    std::fprintf(stderr, "unknown parameter set %s\n", set.c_str());
    return 2;
  }
  return rc;
}
