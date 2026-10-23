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
// Modified 2026 by Chad Sharp and Paul Grubbs: prove_zk and verify_zk helpers with seeded transcript and statement absorption, and check_zk_proofs on two proofs

#ifndef PRIVACY_PROOFS_ZK_LIB_ZK_ZK_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_ZK_ZK_TESTING_H_

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "algebra/convolution.h"
#include "algebra/fp2.h"
#include "algebra/reed_solomon.h"
#include "arrays/dense.h"
#include "random/secure_random_engine.h"
#include "random/transcript.h"
#include "sumcheck/circuit.h"
#include "util/log.h"
#include "util/readbuffer.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"
#include "gtest/gtest.h"

namespace proofs {

constexpr size_t kLigeroRate = 7;
constexpr size_t kLigeroNreq = 132;
constexpr size_t kVersion = 7;

// One serialized proof: the seed sigma (BasicProofSeed), then the ZkProof.
template <class Field, class RSFactory>
std::vector<uint8_t> prove_zk(const Circuit<Field>& circuit, Dense<Field>& W,
                              const RSFactory& rsf, const Field& F,
                              SecureRandomEngine& rng, ZkProof<Field>& zkpr) {
  const ProofSeed sigma = ProofSeed::draw(rng);
  Transcript tp((uint8_t*)"zk_test", 7, sigma, kVersion);
  absorb_circuit_statement(tp, circuit, W, F);
  ZkProver<Field, RSFactory> prover(circuit, F, rsf);
  prover.commit(zkpr, W, tp, rng);
  EXPECT_TRUE(prover.prove(zkpr, W, tp));
  log(INFO, "ZK Prover done");

  std::vector<uint8_t> zbuf;
  sigma.write(zbuf);
  zkpr.write(zbuf, F);
  log(INFO, "zkp len: %zu bytes", zbuf.size());
  return zbuf;
}

// Parses a serialized proof, as a different client would, and verifies it:
// the seed comes from the proof.
template <class Field, class RSFactory>
bool verify_zk(const Circuit<Field>& circuit, const Dense<Field>& pub,
               const RSFactory& rsf, const Field& F,
               const std::vector<uint8_t>& zbuf) {
  ReadBuffer rb(zbuf);
  ProofSeed sigma;
  if (!sigma.read(rb)) return false;
  ZkProof<Field> zkpv(circuit, kLigeroRate, kLigeroNreq);
  if (!zkpv.read(rb, F)) return false;

  ZkVerifier<Field, RSFactory> verifier(circuit, rsf, kLigeroRate, kLigeroNreq,
                                        F);
  Transcript tv((uint8_t*)"zk_test", 7, sigma, kVersion);
  absorb_circuit_statement(tv, circuit, pub, F);
  verifier.recv_commitment(zkpv, tv);
  return verifier.verify(zkpv, pub, tv);
}

// Proves twice and verifies. The two proofs of one statement have different
// seeds and different leaf nonces, and a proof with a changed seed is
// rejected.
template <class Field, class RSFactory>
void check_zk_proofs(const Circuit<Field>& circuit, Dense<Field>& W,
                     const Dense<Field>& pub, const RSFactory& rsf,
                     const Field& F) {
  SecureRandomEngine rng;
  ZkProof<Field> zk1(circuit, kLigeroRate, kLigeroNreq);
  ZkProof<Field> zk2(circuit, kLigeroRate, kLigeroNreq);
  std::vector<uint8_t> buf1 = prove_zk(circuit, W, rsf, F, rng, zk1);
  const std::vector<uint8_t> buf2 = prove_zk(circuit, W, rsf, F, rng, zk2);
  EXPECT_TRUE(verify_zk(circuit, pub, rsf, F, buf1));
  EXPECT_TRUE(verify_zk(circuit, pub, rsf, F, buf2));
  log(INFO, "ZK Verify done");

  EXPECT_NE(std::memcmp(buf1.data(), buf2.data(), ProofSeed::kLength), 0);
  const auto& n1 = zk1.com_proof.merkle.nonce;
  const auto& n2 = zk2.com_proof.merkle.nonce;
  ASSERT_EQ(n1.size(), n2.size());
  for (size_t i = 0; i < n1.size(); ++i) {
    EXPECT_NE(std::memcmp(n1[i].bytes, n2[i].bytes, MerkleNonce::kLength), 0);
  }

  buf1[0] ^= 1;
  EXPECT_FALSE(verify_zk(circuit, pub, rsf, F, buf1));
}

// Runs a zk prover and verifier for a field that requires a field extension
// to perform the commitment.
template <class Field>
void run2_test_zk(const Circuit<Field>& circuit, Dense<Field>& W,
                  const Dense<Field>& pub, const Field& base,
                  const typename Field::Elt& root_x,
                  const typename Field::Elt& root_y, size_t root_order) {
  // Build the relevant algebra objects.
  using Field2 = Fp2<Field>;
  using Elt2 = typename Field2::Elt;
  using FftExtConvolutionFactory = FFTExtConvolutionFactory<Field, Field2>;
  using RSFactory = ReedSolomonFactory<Field, FftExtConvolutionFactory>;

  const Field2 base_2(base);
  const Elt2 omega{root_x, root_y};
  const FftExtConvolutionFactory fft(base, base_2, omega, root_order);
  const RSFactory rsf(fft, base);

  check_zk_proofs<Field>(circuit, W, pub, rsf, base);
}

template <class Field>
void run_failing_test_zk2(const Circuit<Field>& circuit, Dense<Field>& W,
                          const Dense<Field>& pub, const Field& base,
                          const typename Field::Elt& root_x,
                          const typename Field::Elt& root_y,
                          size_t root_order) {
  // Build the relevant algebra objects.
  using Field2 = Fp2<Field>;
  using Elt2 = typename Field2::Elt;
  using FftExtConvolutionFactory = FFTExtConvolutionFactory<Field, Field2>;
  using RSFactory = ReedSolomonFactory<Field, FftExtConvolutionFactory>;

  const Field2 base_2(base);
  const Elt2 omega{root_x, root_y};
  const FftExtConvolutionFactory fft(base, base_2, omega, root_order);
  const RSFactory rsf(fft, base);

  ZkProof<Field> zkpr(circuit, kLigeroRate, kLigeroNreq);

  SecureRandomEngine rng;
  Transcript tp((uint8_t*)"zk_test", 7, ProofSeed::draw(rng), kVersion);
  absorb_circuit_statement(tp, circuit, W, base);
  ZkProver<Field, RSFactory> prover(circuit, base, rsf);
  prover.commit(zkpr, W, tp, rng);
  bool p_ok = prover.prove(zkpr, W, tp);
  EXPECT_FALSE(p_ok);
}

// Runs a zk prover and verifier for a field that has a suitable root of unity.
template <class Field>
void run_test_zk(const Circuit<Field>& circuit, Dense<Field>& W,
                 const Dense<Field>& pub, const typename Field::Elt& omega,
                 uint64_t omega_order, const Field& F) {
  using FftConvolutionFactory = FFTConvolutionFactory<Field>;

  FftConvolutionFactory fft(F, omega, omega_order);
  using RSFactory = ReedSolomonFactory<Field, FftConvolutionFactory>;
  const RSFactory rsf(fft, F);

  check_zk_proofs<Field>(circuit, W, pub, rsf, F);
}

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_ZK_ZK_TESTING_H_
