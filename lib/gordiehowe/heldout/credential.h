// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Held-out program: a toy credential, SHA3-256 with a Lamport one-time
// signature over SHA-256.
//
// A credential is 20 attribute bytes: a 16-byte name, a birth year (2
// bytes, little-endian) and a 2-byte country code. The issuer signs the
// first 16 bits of its SHA3-256 digest with a Lamport key: the public key
// holds two SHA-256 digests per bit, pk[i][0] and pk[i][1], and the
// signature reveals the preimage of pk[i][b_i] for each digest bit b_i.
// The statement is the issuer's public key and the current year; the
// witness is the credential and the 16 revealed preimages. The relation
// proves, without revealing the credential,
//   domain H (GF(2^128))       SHA3-256 of the attributes, and
//                              SHA-256(preimage_i) = pk[i][b_i], the key
//                              digest selected by a multiplexer;
//   domain A (Goldilocks^2)    the birth year's and country's bits (MAC
//                              equalities from H) as integers: an age in
//                              [18, 118) and a country in a public list
//                              of four codes (a lookup).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CREDENTIAL_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CREDENTIAL_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "circuits/tests/sha3/sha3_reference.h"
#include "gordiehowe/heldout/heldout_env.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/lib/sha256.h"
#include "util/crypto.h"

namespace proofs::gordiehowe::heldout::credential {

constexpr size_t kAttrBytes = 20;
constexpr size_t kSignedBits = 16;
using Digest = std::array<uint8_t, 32>;
// The countries a credential may name, as 16-bit little-endian codes.
inline const std::vector<uint64_t> kCountries = {
    uint64_t('U') | uint64_t('S') << 8, uint64_t('C') | uint64_t('A') << 8,
    uint64_t('D') | uint64_t('E') << 8, uint64_t('J') | uint64_t('P') << 8};

template <template <class> class F>
struct Statement {
  F<std::array<std::array<Digest, 2>, kSignedBits>> pk;
  F<std::array<uint16_t, 1>> current_year;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint8_t, kAttrBytes>> attrs;
  F<std::array<Digest, kSignedBits>> preimages;
};

inline auto relation() {
  return compile<Statement, Witness>(
      compile_profile("credential"),
      [](MixedSys &cs, Statement<In> st, Witness<In> w) {
        auto &H = cs.domain(binary_profile(), "H");
        auto &A = cs.domain(gold_profile(), "A");
        const GF &f = A.field();
        // Bit [20, 8].
        const auto attrs = H.priv(w.attrs);
        const auto digest = lib::keccak::sha3_256(
            lib::keccak::keccak_batch(H, "keccak"), "digest",
            lib::keccak::sponge_input(attrs.flat()));
        const auto preimages = H.priv(w.preimages);
        const auto pk = st.pk.bits(H);
        const auto ots = lib::sha256::sha256_batch(H, "ots");
        const std::vector<size_t> each(256, 0);
        for (size_t i = 0; i < kSignedBits; ++i) {
          const std::string nm = "ots" + std::to_string(i);
          const auto h =
              lib::sha256::sha256(ots, nm, preimages.at(0, i).flat());
          const auto bit = digest.out.slice(i, i + 1).reindex(each);
          const auto key0 = pk.at(0, i).at(0, 0).flat();
          const auto key1 = pk.at(0, i).at(0, 1).flat();
          assert_equal(h, bit.mux(key1, key0), nm + ".key");
        }
        // The birth year and the country in A.
        const auto year =
            attrs.slice(16, 18).flat().to(A, "year_bits").from_digits(2);
        const auto country =
            attrs.slice(18, 20).flat().to(A, "country_bits").from_digits(2);
        const auto now = st.current_year.values(A);
        assert_range(now - year - 18, 100, "age");
        std::vector<GF::Elt> codes;
        for (uint64_t c : kCountries) codes.push_back(f.of_scalar(c));
        assert_in(country, in_table(cs, "countries",
                                    A.constant("country_codes", codes)),
                  "country");
      },
      "heldout-credential");
}

// ------------------------------------------------------------------ host --

inline Digest sha256_of(const Digest &m) {
  SHA256 sha;
  sha.Update(m.data(), m.size());
  Digest d;
  sha.DigestData(d.data());
  return d;
}
inline Digest sha3_of(const std::array<uint8_t, kAttrBytes> &m) {
  Sha3Reference h(32);
  h.update(reinterpret_cast<const char *>(m.data()), m.size());
  Digest d;
  h.final(d.data());
  return d;
}

struct Instance {
  Statement<Value> statement;
  Witness<Value> witness;
};
// A credential born in BIRTH_YEAR from country COUNTRY (an index into
// kCountries), signed under a random key, in CURRENT_YEAR.
inline Instance instance(uint64_t seed, uint16_t birth_year,
                         uint16_t current_year, size_t country = 0) {
  std::mt19937_64 g(seed);
  Instance in;
  auto &a = in.witness.attrs;
  for (size_t k = 0; k < 16; ++k) a[k] = uint8_t('a' + g() % 26);
  a[16] = uint8_t(birth_year);
  a[17] = uint8_t(birth_year >> 8);
  a[18] = uint8_t(kCountries[country]);
  a[19] = uint8_t(kCountries[country] >> 8);
  const Digest d = sha3_of(a);
  for (size_t i = 0; i < kSignedBits; ++i) {
    Digest sk[2];
    for (auto &s : sk)
      for (auto &b : s) b = uint8_t(g());
    in.statement.pk[i][0] = sha256_of(sk[0]);
    in.statement.pk[i][1] = sha256_of(sk[1]);
    in.witness.preimages[i] = sk[(d[i / 8] >> (i % 8)) & 1];
  }
  in.statement.current_year[0] = current_year;
  return in;
}

}  // namespace proofs::gordiehowe::heldout::credential

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_HELDOUT_CREDENTIAL_H_
