// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// SHA-256 of the private message for the RSA proof of possession, over
// GF(2^128), in the style of circuits/mdoc/mdoc_hash.h.
//
// The message has a private length n <= n_m, n_m the relation's maximum.
// The witness is mdoc's: a private block count nb and a buffer of
// nb_max = ceil((n_m + 9) / 64) blocks that the prover fills with the
// SHA-256 padded message and zeros (FlatSHA256Witness::
// transform_and_witness_message, as mdoc_witness.h does). The circuit
// checks it as mdoc_hash.h's assert_valid_hash_mdoc does: nb is asserted to
// be bits, and upstream's FlatSHA256Circuit::assert_message_hash runs every
// block, asserts the blocks past nb zero and takes block nb's chaining
// value as the digest. assert_padding then checks the SHA-256 padding with
// upstream's Logic gadgets (mdoc does not): the length field of block nb
// (FlatSHA256Circuit::find_len_bits) is 8 n for a byte length n < 2^16,
// byte n is 0x80, every byte after it up to that length field is zero, and
// nb is the padded length's block count, 64 (nb - 1) - 8 <= n < 64 nb - 8.
// So the buffer is exactly the SHA-256 padding of its first n bytes. The
// block witnesses are packed 4 bits per element (mdoc's kSHAPluckerBits);
// e is the digest as the 256 bits of the integer D (bit i at index i, as
// mdoc's e), which the caller MACs with MACGF2.

#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_HASH_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_HASH_H_

#include <cstddef>
#include <vector>

#include "circuits/logic/bit_plucker.h"
#include "circuits/sha/flatsha256_circuit.h"

namespace proofs {

// mdoc_hash.h's kSHAPluckerBits.
static constexpr size_t kRsaSHAPluckerBits = 4u;

inline size_t rsa_sha_blocks(size_t n) { return (n + 9 + 63) / 64; }

template <class Logic>
class RsaHash {
 public:
  using v8 = typename Logic::v8;
  using v256 = typename Logic::v256;
  using Flatsha =
      FlatSHA256Circuit<Logic, BitPlucker<Logic, kRsaSHAPluckerBits>>;
  using ShaBlockWitness = typename Flatsha::BlockWitness;

  // mdoc_hash.h's Witness, its hash part, for messages of at most n_m
  // bytes: nb, the padded buffer, the block witnesses (in that input
  // order).
  class Witness {
   public:
    v8 nb_;
    std::vector<v8> in_;
    std::vector<ShaBlockWitness> sha_;

    explicit Witness(size_t n_m)
        : in_(64 * rsa_sha_blocks(n_m)), sha_(rsa_sha_blocks(n_m)) {}

    void input(const Logic& lc) {
      nb_ = lc.template vinput<8>();
      for (auto& b : in_) b = lc.template vinput<8>();
      for (auto& bw : sha_) bw.input(lc);
    }
  };

  explicit RsaHash(const Logic& lc) : lc_(lc), sha_(lc) {}

  void assert_message_hash(const v256& e, const Witness& vw) const {
    lc_.vassert_is_bit(vw.nb_);
    sha_.assert_message_hash(vw.sha_.size(), vw.nb_, vw.in_.data(), e,
                             vw.sha_.data());
    assert_padding(vw);
  }

  // The SHA-256 padding of the buffer's first n bytes, n read from block
  // nb's length field.
  void assert_padding(const Witness& vw) const {
    const size_t nb_max = vw.sha_.size();
    const auto len = sha_.find_len_bits(nb_max, vw.in_.data(), vw.nb_);
    // The bit length is 8 n with n < 2^16.
    for (size_t j = 0; j < 3; ++j) lc_.assert0(len[j]);
    for (size_t j = 19; j < 64; ++j) lc_.assert0(len[j]);
    typename Logic::template bitvec<16> n;
    for (size_t j = 0; j < 16; ++j) n[j] = len[3 + j];
    for (size_t b = 0; b < nb_max; ++b) {
      // Block b is block nb, or a block before nb.
      const auto at_nb = lc_.veq(vw.nb_, b + 1);
      const auto before_nb = lc_.vlt(b + 1, vw.nb_);
      // nb is the block count of n + 9 bytes.
      lc_.assert_implies(at_nb, lc_.vlt(n, 64 * b + 56));
      if (b > 0) {
        lc_.assert_implies(at_nb, lc_.lnot(lc_.vlt(n, 64 * b - 8)));
      }
      for (size_t k = 0; k < 64; ++k) {
        const size_t i = 64 * b + k;
        // Bytes before block nb's length field.
        const auto padded = k < 56 ? lc_.lor(before_nb, at_nb) : before_nb;
        lc_.assert_implies(lc_.veq(n, i), lc_.veq(vw.in_[i], 0x80));
        lc_.assert_implies(lc_.land(lc_.vlt(n, i), padded),
                           lc_.veq(vw.in_[i], 0));
      }
    }
  }

 private:
  const Logic& lc_;
  Flatsha sha_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_CIRCUITS_RSA_RSA_HASH_H_
