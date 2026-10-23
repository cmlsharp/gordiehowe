// Copyright 2026 Google LLC.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// Modified 2026 by Chad Sharp and Paul Grubbs: adapted from lib/circuits/mdoc/mdoc_zk.cc: benchmark driver with timing marks in the mdoc prover and verifier

// Longfellow mdoc (ZkSpec v7) benchmark driver, a worker of common/bench.py.
//
// usage: mdoc_v7_driver DOC_INDEX NATTR
//
// DOC_INDEX selects upstream's mdoc_tests[] example; NATTR (1-4) the first
// NATTR of age_over_18, familyname_mustermann, birthdate_1971_09_01,
// height_175 (doc 3 only for NATTR > 1), with ZkSpec kZkSpecs[NATTR - 1]
// (version 7: rate 7, 132 opened columns, upstream's block_enc).
//
// timed_prover and timed_verifier are upstream's run_mdoc_prover and
// run_mdoc_verifier (upstream/lib/circuits/mdoc/mdoc_zk.cc) with marks
// between their phases; apart from the marks and the removed INFO logs the
// bodies are the library's.  The driver #includes mdoc_zk.cc so that the
// file-local helpers resolve.  The circuit is generated once, before
// PQ_READY.
//
// Per trial:
//   commit_ms = hash_commit + sig_commit
//   prove_ms  = macs + hash_prove + sig_prove
//   verify_ms = everything run_mdoc_verifier does after it has parsed the
//               circuits and read the proof: the Reed-Solomon factories and
//               ZkVerifiers, both commitments, the MAC key, the public
//               inputs and both ZkVerifier::verify calls
// Circuit decompression and parsing (which the library repeats on every
// call), witness generation and serialization are details only.
//
// Built twice (CMakeLists.txt): mdoc_v7 against upstream as is, and
// mdoc_v7_nomac (baselines/mdoc-v7-mac-ablation) with that baseline's copy
// of circuits/mac/mac_circuit.h first on the include path.
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>

#include "bench_worker.h"
#include "circuits/mdoc/mdoc_zk.cc"
#include "circuits/mdoc/mdoc_examples.h"
#include "circuits/mdoc/mdoc_test_attributes.h"

namespace proofs {

MdocProverErrorCode timed_prover(
    lfb::Trial& T, const uint8_t* bcp, size_t bcsz, /* circuit data */
    const uint8_t* mdoc, size_t mdoc_len, const char* pkx,
    const char* pky,                          /* string rep of public key */
    const uint8_t* transcript, size_t tr_len, /* session transcript */
    const RequestedAttribute* attrs, size_t attrs_len,
    const char* now, /* time formatted as "2023-11-02T09:00:00Z" */
    uint8_t** prf, size_t* proof_len, const ZkSpecStruct* zk_spec) {
  if (bcp == nullptr || mdoc == nullptr || pkx == nullptr || pky == nullptr ||
      transcript == nullptr || attrs == nullptr || now == nullptr ||
      prf == nullptr || proof_len == nullptr || zk_spec == nullptr) {
    return MDOC_PROVER_NULL_INPUT;
  }

  for (size_t i = 0; i < attrs_len; ++i) {
    if (attrs[i].namespace_len > 64 || attrs[i].id_len > 32 ||
        attrs[i].cbor_value_len > 64) {
      return MDOC_PROVER_INVALID_INPUT;
    }
  }

  Elt pkX, pkY;
  if (!parsePk(pkx, pky, pkX, pkY)) {
    log(ERROR, "invalid pkx, pky");
    return MDOC_PROVER_INVALID_INPUT;
  }

  if (!sameNamespace(attrs, attrs_len)) {
    log(ERROR, "attributes must all be in the same namespace");
    return MDOC_PROVER_INVALID_INPUT;
  }

  lfb::Marks M;
  // Parse circuits from cached byte representation.
  const f2_p256 p256_2(p256_base);
  const f_128 Fs;

  std::unique_ptr<Circuit<Fp256Base>> c_sig = nullptr;
  std::unique_ptr<Circuit<f_128>> c_hash = nullptr;
  /* scope for the bytes array */ {
    size_t len = kCircuitSizeMax;
    std::vector<uint8_t> bytes(len);
    size_t full_size = decompress(bytes, bcp, bcsz);

    if (full_size == 0) {
      return MDOC_PROVER_CIRCUIT_PARSING_FAILURE;
    }

    ReadBuffer rb_circuit(bytes.data(), full_size);

    CircuitReader<Fp256Base> cr_s(p256_base, P256_ID);
    c_sig = cr_s.from_bytes(rb_circuit, enforce_circuit_id_in_prover);
    if (c_sig == nullptr) {
      log(ERROR, "signature circuit could not be parsed");
      return MDOC_PROVER_CIRCUIT_PARSING_FAILURE;
    }
    CircuitReader<f_128> cr_h(Fs, GF2_128_ID);
    c_hash = cr_h.from_bytes(rb_circuit, enforce_circuit_id_in_prover);

    if (c_hash == nullptr) {
      log(ERROR, "hash circuit could not be parsed");
      return MDOC_PROVER_HASH_PARSING_FAILURE;
    }
  }
  T.add("circuit_parse", M.mark());

  //  ============ Produce zk witness ==============
  auto W_sig = Dense<Fp256Base>(1, c_sig->ninputs);
  auto W_hash = Dense<f_128>(1, c_hash->ninputs);
  DenseFiller<Fp256Base> sig_filler(W_sig);
  DenseFiller<f_128> hash_filler(W_hash);

  SecureRandomEngine rng;
  ProverState state;
  MdocProverErrorCode ok = fill_witness(
      sig_filler, hash_filler, mdoc, mdoc_len, pkX, pkY, transcript, tr_len,
      attrs, attrs_len, (const uint8_t*)now, state, rng, Fs, zk_spec->version);
  if (ok != MDOC_PROVER_SUCCESS) {
    log(ERROR, "fill_witness failed");
    return ok;
  }
  T.add("witness", M.mark());

  // ========= Run prover ==============
  // Use the transcript from the session to select the random oracle.
  Transcript tp(transcript, tr_len, zk_spec->version);

  const Elt2 omega = p256_2.of_string(kRootX, kRootY);
  const FftExtConvolutionFactory fft_b(p256_base, p256_2, omega, 1ull << 31);
  const RSFactory_b rsf_b(fft_b, p256_base);
  const RSFactory the_reed_solomon_factory(Fs);

  size_t r = zk_spec->version < 7 ? kLigeroRate : kLigeroRatev7;
  size_t req = zk_spec->version < 7 ? kLigeroNreq : kLigeroNreqv7;
  ZkProof<f_128> h_zk(*c_hash, r, req, zk_spec->block_enc_hash);
  ZkProof<Fp256Base> sig_zk(*c_sig, r, req, zk_spec->block_enc_sig);

  ZkProver<f_128, RSFactory> hash_p(*c_hash, Fs, the_reed_solomon_factory);
  ZkProver<Fp256Base, RSFactory_b> sig_p(*c_sig, p256_base, rsf_b);
  const double setup = M.mark();

  hash_p.commit(h_zk, W_hash, tp, rng);
  const double hash_commit = M.mark();
  sig_p.commit(sig_zk, W_sig, tp, rng);
  const double sig_commit = M.mark();

  // After prover has committed to the public inputs, compute
  // verifier challenge av, and then compute MACs of the common public
  // inputs.

  gf2k av = generate_mac_key(tp), macs[6];
  uint8_t macs_b[6 * f_128::kBytes];
  compute_macs(3, state.common, macs, macs_b, state.ap, av);
  update_macs(W_sig, W_hash, kSigMacIndex,
              getHashMacIndex(attrs_len, zk_spec->version), macs, av, Fs);
  const double mac_ms = M.mark();

  if (!hash_p.prove(h_zk, W_hash, tp)) {
    return MDOC_PROVER_GENERAL_FAILURE;
  };
  const double hash_prove = M.mark();

  if (!sig_p.prove(sig_zk, W_sig, tp)) {
    return MDOC_PROVER_GENERAL_FAILURE;
  };
  const double sig_prove = M.mark();

  // Serialize proof to bytes.
  // [6 mac values] [docType] [hash proof] [sig proof]
  std::vector<uint8_t> buf;
  // This sum will not overflow based on constraints of circuit & proof size.
  size_t tt = 6 * f_128::kBytes + h_zk.size() + sig_zk.size();
  buf.reserve(tt);
  buf.insert(buf.begin(), macs_b, macs_b + 6 * f_128::kBytes);
  h_zk.write(buf, Fs);
  sig_zk.write(buf, p256_base);
  *proof_len = buf.size();
  T.add("serialize", M.mark());

  T.add("prover_setup", setup);
  T.add("hash_commit", hash_commit);
  T.add("sig_commit", sig_commit);
  T.add("macs", mac_ms);
  T.add("hash_prove", hash_prove);
  T.add("sig_prove", sig_prove);
  T.commit_ms = hash_commit + sig_commit;
  T.prove_ms = mac_ms + hash_prove + sig_prove;
  {
    std::vector<uint8_t> hb, sb;
    h_zk.write(hb, Fs);
    sig_zk.write(sb, p256_base);
    T.add("hash_proof_bytes", double(hb.size()));
    T.add("sig_proof_bytes", double(sb.size()));
  }
  T.add("hash_nrow", double(h_zk.param.nrow));
  T.add("hash_block", double(h_zk.param.block));
  T.add("sig_nrow", double(sig_zk.param.nrow));
  T.add("sig_block", double(sig_zk.param.block));

  // Allocate memory and copy proof bytes.
  *prf = (uint8_t*)malloc(*proof_len);
  if (!*prf) {
    log(ERROR, "malloc failed");
    return MDOC_PROVER_MEMORY_ALLOCATION_FAILURE;
  }
  memcpy(*prf, buf.data(), buf.size());
  return MDOC_PROVER_SUCCESS;
}

MdocVerifierErrorCode timed_verifier(
    lfb::Trial& T, const uint8_t* bcp, size_t bcsz, /* circuit data */
    const char* pkx, const char* pky,         /* string rep of public key */
    const uint8_t* transcript, size_t tr_len, /* session Transcript */
    const RequestedAttribute* attrs, size_t attrs_len,
    const char* now, /* time formatted as "2023-11-02T09:00:00Z" */
    const uint8_t* zkproof, size_t proof_len, const char* docType,
    const ZkSpecStruct* zk_spec) {
  if (bcp == nullptr || pkx == nullptr || pky == nullptr ||
      transcript == nullptr || now == nullptr || attrs == nullptr ||
      zkproof == nullptr || docType == nullptr || zk_spec == nullptr) {
    return MDOC_VERIFIER_NULL_INPUT;
  }

  for (size_t i = 0; i < attrs_len; ++i) {
    if (attrs[i].namespace_len > 64 || attrs[i].id_len > 32 ||
        attrs[i].cbor_value_len > 64) {
      return MDOC_VERIFIER_INVALID_INPUT;
    }
  }

  Elt pkX, pkY;
  if (!parsePk(pkx, pky, pkX, pkY)) {
    log(ERROR, "invalid pkx, pky");
    return MDOC_VERIFIER_INVALID_INPUT;
  }

  if (!sameNamespace(attrs, attrs_len)) {
    log(ERROR, "attributes must all be in the same namespace");
    return MDOC_VERIFIER_INVALID_INPUT;
  }

  // Verify that the values in the RequestedAttribute structure are valid cbor.
  for (size_t i = 0; i < attrs_len; ++i) {
    if (!cbor_validate(attrs[i].cbor_value, attrs[i].cbor_value_len)) {
      log(ERROR, "invalid cbor value");
      return MDOC_VERIFIER_INVALID_CBOR;
    }
  }

  const f_128 Fs;

  // Sanity check input sizes.
  if (bcsz < 50000 || tr_len < 1 || attrs_len < 1 || proof_len < 20000) {
    return MDOC_VERIFIER_ARGUMENTS_TOO_SMALL;
  }

  lfb::Marks V;
  const f2_p256 p256_2(p256_base);

  // Parse circuits from cached byte representation.
  size_t len = kCircuitSizeMax;
  std::vector<uint8_t> bytes(len);
  size_t full_size = decompress(bytes, bcp, bcsz);

  ReadBuffer rb_circuit(bytes.data(), full_size);
  CircuitReader<Fp256Base> cr_s(p256_base, P256_ID);
  auto c_sig = cr_s.from_bytes(rb_circuit, enforce_circuit_id_in_verifier);
  if (c_sig == nullptr) {
    log(ERROR, "signature circuit could not be parsed");
    return MDOC_VERIFIER_CIRCUIT_PARSING_FAILURE;
  }

  CircuitReader<f_128> cr_h(Fs, GF2_128_ID);
  auto c_hash = cr_h.from_bytes(rb_circuit, enforce_circuit_id_in_verifier);

  if (c_hash == nullptr) {
    log(ERROR, "circuit could not be parsed");
    return MDOC_VERIFIER_CIRCUIT_PARSING_FAILURE;
  }
  T.add("v_circuit_parse", V.mark());

  // Parse proofs
  size_t r = zk_spec->version < 7 ? kLigeroRate : kLigeroRatev7;
  size_t req = zk_spec->version < 7 ? kLigeroNreq : kLigeroNreqv7;
  ZkProof<f_128> pr_hash(*c_hash, r, req, zk_spec->block_enc_hash);
  ZkProof<Fp256Base> pr_sig(*c_sig, r, req, zk_spec->block_enc_sig);

  const std::vector<uint8_t> zbuf(zkproof, zkproof + proof_len);
  ReadBuffer rb(zbuf);

  // Read macs from proof string.
  // The sanity check above ensures that the proof is big enough for the MACs.
  gf2k macs[6];

  for (size_t i = 0; i < 6; ++i) {
    macs[i] = Fs.of_bytes_field(rb.next(f_128::kBytes)).value();
  }

  // The proof read methods check proof length internally.
  if (!pr_hash.read(rb, Fs)) {
    log(ERROR, "hash proof could not be parsed");
    return MDOC_VERIFIER_HASH_PARSING_FAILURE;
  };
  if (!pr_sig.read(rb, p256_base)) {
    log(ERROR, "sig proof could not be parsed");
    return MDOC_VERIFIER_SIGNATURE_PARSING_FAILURE;
  }
  if (rb.remaining() != 0) {
    log(ERROR, "proof bytes contains extra data: %zu bytes", rb.remaining());
    return MDOC_VERIFIER_SIGNATURE_PARSING_FAILURE;
  }
  T.add("v_proof_read", V.mark());

  // =============== Verify

  const Elt2 omega = p256_2.of_string(kRootX, kRootY);
  const FftExtConvolutionFactory fft_b(p256_base, p256_2, omega, 1ull << 31);
  const RSFactory_b rsf_b(fft_b, p256_base);
  const RSFactory the_reed_solomon_factory(Fs);

  ZkVerifier<f_128, RSFactory> hash_v(*c_hash, the_reed_solomon_factory, r, req,
                                      zk_spec->block_enc_hash, Fs);
  ZkVerifier<Fp256Base, RSFactory_b> sig_v(*c_sig, rsf_b, r, req,
                                           zk_spec->block_enc_sig, p256_base);
  const double v_setup = V.mark();

  // Use the transcript from the session to select the random oracle.
  class Transcript tv(transcript, tr_len, zk_spec->version);

  hash_v.recv_commitment(pr_hash, tv);
  sig_v.recv_commitment(pr_sig, tv);

  gf2k av = generate_mac_key(tv);
  const double v_commitments = V.mark();

  // =============== Create public inputs
  auto pub_hash = Dense<f_128>(1, c_hash->npub_in);
  auto pub_sig = Dense<Fp256Base>(1, c_sig->npub_in);
  DenseFiller<f_128> hash_filler(pub_hash);
  DenseFiller<Fp256Base> sig_filler(pub_sig);

  size_t dlen = strlen(docType);
  if (!fill_public_inputs(sig_filler, hash_filler, pkX, pkY, transcript, tr_len,
                          attrs, attrs_len, (const uint8_t*)now,
                          (const uint8_t*)docType, dlen, macs, av, Fs,
                          zk_spec->version)) {
    return MDOC_VERIFIER_GENERAL_FAILURE;
  }

  if (hash_filler.size() != c_hash->npub_in ||
      sig_filler.size() != c_sig->npub_in) {
    return MDOC_VERIFIER_ATTRIBUTE_NUMBER_MISMATCH;
  }
  const double v_public = V.mark();

  bool ok = hash_v.verify(pr_hash, pub_hash, tv);
  const double v_hash = V.mark();
  bool ok2 = sig_v.verify(pr_sig, pub_sig, tv);
  const double v_sig = V.mark();

  T.add("v_setup", v_setup);
  T.add("v_commitments", v_commitments);
  T.add("v_public_inputs", v_public);
  T.add("v_hash_verify", v_hash);
  T.add("v_sig_verify", v_sig);
  T.verify_ms = v_setup + v_commitments + v_public + v_hash + v_sig;

  return ok && ok2 ? MDOC_VERIFIER_SUCCESS : MDOC_VERIFIER_GENERAL_FAILURE;
}

}  // namespace proofs

using namespace proofs;

int main(int argc, char** argv) {
  if (argc != 3) {
    std::fprintf(stderr, "usage: %s DOC_INDEX NATTR\n", argv[0]);
    return 2;
  }
  const int doc = std::atoi(argv[1]);
  const size_t na = std::strtoull(argv[2], nullptr, 10);
  if (na < 1 || na > 4 || (doc != 3 && na != 1)) return 2;
  set_log_level(ERROR);
  const RequestedAttribute all[4] = {
      test::age_over_18, test::familyname_mustermann,
      test::birthdate_1971_09_01, test::height_175};
  const MdocTests* t = &mdoc_tests[doc];
  const ZkSpecStruct* spec = &kZkSpecs[na - 1];
  uint8_t* circuit;
  size_t clen;
  if (generate_circuit(spec, &circuit, &clen) != CIRCUIT_GENERATION_SUCCESS) {
    return 3;
  }
  lfb::info({{"doc", std::to_string(doc)},
             {"nattr", std::to_string(na)},
             {"spec_version", std::to_string(spec->version)},
             {"block_enc_hash", std::to_string(spec->block_enc_hash)},
             {"block_enc_sig", std::to_string(spec->block_enc_sig)},
             {"rate", std::to_string(kLigeroRatev7)},
             {"nreq", std::to_string(kLigeroNreqv7)},
             {"mdoc_bytes", std::to_string(t->mdoc_size)},
             {"circuit_zst_bytes", std::to_string(clen)}});
  lfb::serve([&]() {
    lfb::Trial T;
    uint8_t* prf = nullptr;
    size_t plen = 0;
    auto rc = timed_prover(T, circuit, clen, t->mdoc, t->mdoc_size,
                           t->pkx.as_pointer, t->pky.as_pointer, t->transcript,
                           t->transcript_size, all, na, (const char*)t->now,
                           &prf, &plen, spec);
    if (rc != MDOC_PROVER_SUCCESS) {
      std::printf("prover failed %d\n", (int)rc);
      return T;
    }
    T.proof_bytes = plen;
    auto rv = timed_verifier(T, circuit, clen, t->pkx.as_pointer,
                             t->pky.as_pointer, t->transcript,
                             t->transcript_size, all, na, (const char*)t->now,
                             prf, plen, t->doc_type, spec);
    free(prf);
    T.ok = rv == MDOC_VERIFIER_SUCCESS;
    return T;
  });
  free(circuit);
  return 0;
}
