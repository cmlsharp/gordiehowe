// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// ML-DSA-44 proof of possession over upstream's monolith circuit, a worker
// of common/bench.py.
//
// usage: ml_dsa_44_monolith_driver [RATE NREQ BLOCK_ENC]
//        (default 7 134 8192: rate 7 and the block_enc and opened columns of
//        the narrow tableau (6373, 910) at Longfellow's deployed soundness
//        target; BLOCK_ENC 0 lets ZkProof search)
//
// The statement: "I hold a message M and an ML-DSA-44 signature on M under
// the public key pk", with pk public and M and the signature private.  One
// proof over upstream's Fp24_6 = GF(q^6), q = 8380417, verifies the whole
// signature: upstream's MLDSAVerify (circuits/tests/pq/ml_dsa/
// ml_dsa_circuit.h) checks SampleInBall, A*z - c*t1*2^d, UseHint, the norm
// bounds and SHAKE256(mu || w1') == c_tilde, with mu derived in the circuit
// as FIPS 204 does, mu = SHAKE256(tr || 0 || |ctx| || ctx || M, 64), by
// upstream's Sha3Circuit (ml_dsa_mu.h).  Upstream's own test takes mu as a
// public input instead; the derivation is what this baseline adds.
//
// Upstream's Reed-Solomon encoder for Fp24_6 (ReedSolomonExtensionFactory,
// algebra/reed_solomon_extension.h), upstream's SHA-256 transcript.
//
// The example: ml_dsa_44_benchmark.inc (32-byte message 00..1f, empty
// context; the fork's shared ML-DSA-44 benchmark fixture, OpenSSL 3.6.4).
//
// Per trial: witness (a detail, outside the totals) = the full witness from
// the instance (compute_witness, mu's block witnesses, the fill),
// commit_ms = ZkProver::commit, prove_ms = ZkProver::prove, verify_ms = the
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
#include "circuits/tests/pq/ml_dsa/ml_dsa_witness.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "ml_dsa_mu.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/panic.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace proofs {
namespace {

using Field6 = Fp24_6;
using CBK = CompilerBackend<Field6>;
using LogicCircuit = Logic<Field6, CBK>;
using Params = ml_dsa::MLDsa44Params;
using VerifyCircuit = MLDSAVerify<LogicCircuit, Field6, Params>;
using RSF = ReedSolomonExtensionFactory;
using ml_dsa::MlDsa44SignatureExample;

// Upstream's ml_dsa_circuit_test: Fp24_6 = Fp24[x]/(x^6 - 7).
constexpr uint32_t kBeta = 7;
// Upstream's MLDsaCircuitTestTraits<MLDsa44Params>::kCPrimeTildeBlocks.
constexpr size_t kCPrimeTildeBlocks = 7;

std::vector<uint8_t> bench_hex(const std::string& hex) {
  std::vector<uint8_t> out;
  for (size_t i = 0; i + 1 < hex.size(); i += 2) {
    out.push_back(
        static_cast<uint8_t>(std::stoul(hex.substr(i, 2), nullptr, 16)));
  }
  return out;
}

const MlDsa44SignatureExample& benchmark_example() {
#define hexToBytes bench_hex
  static const MlDsa44SignatureExample example = {
#include "ml_dsa_44_benchmark.inc"
  };
#undef hexToBytes
  return example;
}

// The number of SHAKE256 blocks absorbing tr || 0 || |ctx| || ctx || M.
size_t mu_blocks(const MlDsa44SignatureExample& ex) {
  return (66 + ex.ctx.size() + ex.msg.size()) / 136 + 1;
}

// Public: pk, then ctx.  Private: the signature, upstream's verification
// witness, M, and the block witnesses of mu's SHAKE256.
std::unique_ptr<Circuit<Field6>> make_circuit(const Field6& f6,
                                              const MlDsa44SignatureExample& ex,
                                              size_t* nquad, size_t* depth) {
  QuadCircuit<Field6> Q(f6);
  const CBK cbk(&Q);
  const LogicCircuit LC(&cbk, f6);
  VerifyCircuit verify(LC);

  auto pk = std::make_unique<VerifyCircuit::Pk>();
  pk->input(LC);
  std::vector<LogicCircuit::v8> ctx(ex.ctx.size());
  for (auto& byte : ctx) byte = LC.vinput<8>();

  Q.private_input();
  auto sig = std::make_unique<VerifyCircuit::SignatureW>();
  sig->input(LC);
  auto w = std::make_unique<VerifyCircuit::Witness>();
  w->c_prime_tilde_bws_.resize(kCPrimeTildeBlocks);
  w->input(LC);

  std::vector<LogicCircuit::v8> msg(ex.msg.size());
  for (auto& byte : msg) byte = LC.vinput<8>();
  std::vector<Sha3Circuit<LogicCircuit>::BlockWitness> mu_bws(mu_blocks(ex));
  for (auto& bw : mu_bws) bw.input(LC);
  auto mu = ml_dsa_derive_mu(LC, pk->tr, msg, mu_bws, ctx);

  verify.assert_valid_signature_on_mu(*pk, *sig, mu, *w);
  auto c = Q.mkcircuit(1);
  *nquad = Q.nquad_terms_;
  *depth = Q.depth_;
  return c;
}

}  // namespace
}  // namespace proofs

using namespace proofs;

int main(int argc, char** argv) {
  size_t rate = 7, nreq = 134, block_enc = 8192;
  if (argc == 4) {
    rate = std::strtoull(argv[1], nullptr, 10);
    nreq = std::strtoull(argv[2], nullptr, 10);
    block_enc = std::strtoull(argv[3], nullptr, 10);
  } else if (argc != 1) {
    std::fprintf(stderr, "usage: %s [RATE NREQ BLOCK_ENC]\n", argv[0]);
    return 2;
  }
  set_log_level(ERROR);
  const Fp24& fq = ml_dsa::Fq();
  const Field6 f(fq, kBeta);
  const MlDsa44SignatureExample& ex = benchmark_example();

  size_t nquad = 0, depth = 0;
  auto circuit = make_circuit(f, ex, &nquad, &depth);

  // LFB_NEGATIVE=msg: the committed message differs from the signed one in
  // one bit (with its mu witness recomputed), so every proof must fail.
  std::vector<uint8_t> msg = ex.msg;
  const char* negative = std::getenv("LFB_NEGATIVE");
  if (negative != nullptr && std::string(negative) == "msg") msg[0] ^= 1;

  // The full witness from the instance (pk, signature, message, context):
  // upstream's ml_dsa_witness::compute_witness (pk and signature decoding,
  // ExpandA, tr, SampleInBall, the NTTs), mu's block witnesses and the
  // fill.  Computed here once and again in every trial, timed as the
  // witness.  fill_witness is fill_pk followed by the private witness; with
  // an empty context the ctx slots between them are absent.
  check(ex.ctx.empty(), "the benchmark example has an empty context");
  std::unique_ptr<ml_dsa_witness<Params>> wgp;
  std::vector<Sha3Witness::BlockWitness> mu_bws;
  Dense<Field6> W(1, circuit->ninputs);
  auto witness = [&]() {
    wgp = std::make_unique<ml_dsa_witness<Params>>();
    auto& wg = *wgp;
    check(wg.compute_witness(ex.pkey, ex.sig, ex.msg, ex.ctx),
          "invalid ML-DSA-44 example");
    mu_bws.clear();
    ml_dsa_mu_witness(std::vector<uint8_t>(wg.tr_.begin(), wg.tr_.end()), msg,
                      mu_bws, ex.ctx);
    DenseFiller<Field6> filler(W);
    filler.push_back(f.one());
    wg.fill_witness(filler, f);
    for (uint8_t byte : msg) filler.push_back(byte, 8, f);
    for (const auto& bw : mu_bws) Sha3Witness::fill_witness(filler, bw, f);
    check(filler.size() == circuit->ninputs, "witness size");
  };
  witness();
  Dense<Field6> pub(1, circuit->ninputs);
  {
    DenseFiller<Field6> filler(pub);
    filler.push_back(f.one());
    wgp->fill_pk(filler, f);
    check(filler.size() == circuit->npub_in, "public input size");
  }

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
    lfb::info({{"scheme", "ML-DSA-44"},
               {"field", "Fp24_6"},
               {"rate", std::to_string(rate)},
               {"nreq", std::to_string(nreq)},
               {"block_enc", std::to_string(block_enc)},
               {"block", std::to_string(probe.param.block)},
               {"nrow", std::to_string(probe.param.nrow)},
               {"ninputs", std::to_string(circuit->ninputs)},
               {"npub_in", std::to_string(circuit->npub_in)},
               {"nl", std::to_string(circuit->nl)},
               {"nquad_terms", std::to_string(nquad)},
               {"depth", std::to_string(depth)},
               {"msg_bytes", std::to_string(ex.msg.size())},
               {"mu_blocks", std::to_string(mu_bws.size())}});
  }

  lfb::serve([&]() {
    lfb::Trial T;
    lfb::Marks M;
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
    auto verifier_ptr = make_verifier();
    ZkVerifier<Field6, RSF>& verifier = *verifier_ptr;
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
  });
  return 0;
}
