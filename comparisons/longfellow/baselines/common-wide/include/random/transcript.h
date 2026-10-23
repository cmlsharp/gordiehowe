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
// Modified 2026 by Chad Sharp and Paul Grubbs: replaced by the GordieHowe transcript: SHA-384 tagged writes with cSHAKE256 challenge streams, upstream's constructor

// longfellow-baselines, baselines/common-wide: a shadow of upstream's
// lib/random/transcript.h for the wide profile.  It is the fork's
// lib/random/transcript.h (branch mac-bench, 8d8e0aa4), which the fork's wide
// baselines ran with PROOFS_HASH384, i.e. BasicTranscript<SHA384>: tagged
// writes into SHA-384, each challenge point's stream cSHAKE256 (vendored
// XKCP) keyed by the running digest, and the challenge write-back.  Two
// changes: util/sha384.h supplies SHA384 and ProtocolHash = SHA384 (upstream's
// util/crypto.h has neither), and a constructor with upstream's signature
// (zero seed).  Transcript is BasicTranscript<SHA384>.
#ifndef PRIVACY_PROOFS_ZK_LIB_RANDOM_TRANSCRIPT_H_
#define PRIVACY_PROOFS_ZK_LIB_RANDOM_TRANSCRIPT_H_

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <vector>

#include "random/random.h"
#include "util/crypto.h"
#include "util/sha384.h"
#include "util/panic.h"
#include "util/readbuffer.h"
#include "util/serialization.h"

extern "C" {
#include "SP800-185.h"  // lib/third_party/xkcp
}

namespace proofs {

// FSXOF and BasicTranscript together implement the Fiat-Shamir transform.
//
// The transcript absorbs tagged writes into the running hash Hash, whose
// digest is k = Hash::kDigestSize bytes. Its first two writes are the label
// and the proof's seed sigma (BasicProofSeed, k bytes), both as byte strings
// TAG_BSTR || u64le(n) || bytes. A challenge point starts at the first
// challenge drawn after a write: its key is the digest of the running hash,
// and its stream is cSHAKE256 (NIST SP 800-185) with function name N = "",
// customization S = kFSXOFCustomization (without its terminating NUL), on
// input key || sigma. Every challenge of the point, rejection sampling included, reads
// consecutive stream bytes from stream byte 0. The next write closes the
// point: it first absorbs the challenge write-back
//     TAG_CHALLENGE || u64le(k) || the first k bytes of the stream,
// so the next key depends on the challenges. A point may read at most
// fs_stream_budget<Hash>() bytes of its stream; reading more marks the
// transcript exhausted, and the Ligero prover aborts and the Ligero verifier
// rejects on an exhausted transcript.
constexpr char kFSXOFCustomization[] = "Longfellow-FS-XOF-v1";

// e: the stream bytes a challenge point may read beyond the first k. An
// honest run of any pq_report_bench construction overruns with probability
// at most 2^-256 per proof in both profiles
// (experiments/pq-migration/fs_budget.py). The squeeze is lazy, so the
// budget costs nothing.
constexpr size_t kFSStreamExtraBytes = 206848;

// k + e: the stream bytes one challenge point may read.
template <class Hash>
constexpr size_t fs_stream_budget() {
  return Hash::kDigestSize + kFSStreamExtraBytes;
}

// The challenge stream of one point: cSHAKE256 (XKCP, lib/third_party/xkcp)
// with N = "" and S = kFSXOFCustomization on key || seed, squeezed lazily. Reads
// start at stream byte 0 and are counted; the first k stream bytes are kept
// for the write-back, and head() squeezes any of them not yet read.
class FSXOF {
 public:
  static constexpr size_t kMaxHead = kMaxProtocolDigestSize;

  FSXOF(const uint8_t key[/*n*/], size_t n, const uint8_t seed[/*m*/],
        size_t m, size_t k = 0)
      : k_(k), read_(0) {
    check(k <= kMaxHead, "FSXOF: head longer than kMaxHead");
    int ret = cSHAKE256_Initialize(
        &xof_, 0, nullptr, 0,
        reinterpret_cast<const BitSequence *>(kFSXOFCustomization),
        8 * (sizeof(kFSXOFCustomization) - 1));
    check(ret == 0, "cSHAKE256_Initialize failed");
    ret = cSHAKE256_Update(&xof_, key, 8 * n);
    check(ret == 0, "cSHAKE256_Update failed");
    ret = cSHAKE256_Update(&xof_, seed, 8 * m);
    check(ret == 0, "cSHAKE256_Update failed");
    ret = cSHAKE256_Final(&xof_, nullptr);
    check(ret == 0, "cSHAKE256_Final failed");
  }

  FSXOF(const FSXOF &) = delete;
  FSXOF &operator=(const FSXOF &) = delete;

  void bytes(uint8_t *out, size_t n) {
    squeeze(out, n);
    // keep what falls in the first k bytes
    for (size_t i = 0; i < n && read_ + i < k_; ++i) {
      head_[read_ + i] = out[i];
    }
    read_ += n;
  }

  // The first k stream bytes. Squeezes those not read yet, so call it only
  // when the point is done.
  const uint8_t *head() {
    if (read_ < k_) {
      uint8_t rest[kMaxHead];
      bytes(rest, k_ - read_);
    }
    return head_;
  }

  // Stream bytes read so far.
  size_t read() const { return read_; }

 private:
  void squeeze(uint8_t *out, size_t n) {
    if (n == 0) {
      return;
    }
    int ret = cSHAKE256_Squeeze(&xof_, out, 8 * n);
    check(ret == 0, "cSHAKE256_Squeeze failed");
  }

  cSHAKE_Instance xof_;
  uint8_t head_[kMaxHead];
  size_t k_;
  size_t read_;
};

// The per-proof seed sigma: k = Hash::kDigestSize bytes the prover draws
// from its RNG for each proof (once per transcript, so once for the two
// halves of a split proof). The transcript writes it right after the label and
// appends it to every challenge XOF input. In a serialized proof sigma is the
// first k bytes, before the first half's commitment root.
template <class Hash = ProtocolHash>
struct BasicProofSeed {
  static constexpr size_t kLength = Hash::kDigestSize;
  uint8_t bytes[kLength];

  static BasicProofSeed draw(RandomEngine &rng) {
    BasicProofSeed s;
    rng.bytes(s.bytes, kLength);
    return s;
  }

  bool operator==(const BasicProofSeed &y) const {
    return std::memcmp(bytes, y.bytes, kLength) == 0;
  }

  void write(std::vector<uint8_t> &buf) const {
    buf.insert(buf.end(), bytes, bytes + kLength);
  }

  // False on underflow.
  bool read(ReadBuffer &buf) {
    if (!buf.have(kLength)) {
      return false;
    }
    buf.next(kLength, bytes);
    return true;
  }
};

// Counters of one transcript, kept for the parameter dump
// (circuits/tests/pq/pq_params.h). A write is one typed write: its bytes are
// its tag, its length field if any, and its payload. A challenge point is
// counted when it opens; its write-back (1 + 8 + k bytes) is counted when it
// closes. The counters never enter the hash.
struct TranscriptStats {
  size_t writes = 0;          // typed writes
  size_t write_bytes = 0;     // bytes absorbed by typed writes
  size_t writeback_bytes = 0; // bytes absorbed by challenge write-backs
  size_t max_write_bytes = 0; // largest single typed write
  size_t points = 0;          // challenge points opened
  size_t read_bytes = 0;      // stream bytes read by challenges
  size_t max_point_read = 0;  // most stream bytes read at one point
};

template <class Hash = ProtocolHash>
class BasicTranscript : public RandomEngine {
  enum { TAG_BSTR = 0, TAG_FIELD_ELEM = 1, TAG_ARRAY = 2, TAG_CHALLENGE = 3 };

public:
  static constexpr size_t kDigestSize = Hash::kDigestSize;
  // The tag byte opening each typed write, and the write-back's.
  static constexpr uint8_t kTagBstr = TAG_BSTR, kTagFieldElem = TAG_FIELD_ELEM,
                           kTagArray = TAG_ARRAY,
                           kTagChallenge = TAG_CHALLENGE;

  using Seed = BasicProofSeed<Hash>;

  // A transcript must be explicitly initialized so that each instance of
  // the Random oracle is unique: its label, then the proof's seed.
  BasicTranscript(const uint8_t init[], size_t init_len, const Seed &seed,
                  size_t version = 6)
      : sha_(), xof_(), seed_(seed), budget_(fs_stream_budget<Hash>()),
        exhausted_(false), version_(version) {
    write(init, init_len);
    write(seed_.bytes, Seed::kLength);
  }

  // longfellow-baselines: upstream's Transcript constructor, so that
  // upstream's ZK stack and drivers construct this transcript unchanged.
  // The seed is the all-zero one, as the fork's mdoc prover used it
  // (Transcript::Seed{}); the proof carries no seed.
  BasicTranscript(const uint8_t init[], size_t init_len, size_t version = 6)
      : BasicTranscript(init, init_len, Seed{}, version) {}

  // Remove default copy and move implementations.
  BasicTranscript(const BasicTranscript &) = delete;
  BasicTranscript &operator=(const BasicTranscript &) = delete;

  // Explicit copy to avoid accidental passing by value. The copy has the
  // running hash, budget and exhaustion flag; an open challenge point
  // restarts at stream byte 0 in the copy, and its write-back is the same.
  BasicTranscript clone() {
    return BasicTranscript(sha_, seed_, budget_, exhausted_, version_, stats_);
  }

  // The proof's seed.
  const Seed &seed() const { return seed_; }

  // The counters so far (TranscriptStats).
  const TranscriptStats &stats() const { return stats_; }

  // Read bytes from the stream of the current challenge point, opening the
  // point if none is open. Reading past the budget marks the transcript
  // exhausted; the bytes are still stream bytes.
  void bytes(uint8_t buf[/*n*/], size_t n) override {
    if (!xof_) {
      uint8_t key[kDigestSize];
      get(key);
      xof_ = std::make_unique<FSXOF>(key, sizeof(key), seed_.bytes,
                                     Seed::kLength, kDigestSize);
      ++stats_.points;
    }
    xof_->bytes(buf, n);
    stats_.read_bytes += n;
    if (xof_->read() > stats_.max_point_read) {
      stats_.max_point_read = xof_->read();
    }
    if (xof_->read() > budget_) {
      exhausted_ = true;
    }
  }

  // Whether some challenge point read more than the budget.
  bool exhausted() const { return exhausted_; }

  // Test hook: the stream budget of challenge points opened from now on.
  void set_stream_budget_for_testing(size_t budget) { budget_ = budget; }

  // Snapshot the hash of the transcript so far. While a challenge point is
  // open this is the point's key: the write-back is absorbed only when the
  // point closes.
  void get(uint8_t key[/*Hash::kDigestSize*/]) {

    // fork the state because we will finalize it
    Hash tmp_hash;
    tmp_hash.CopyState(sha_);
    tmp_hash.DigestData(key);
  }

  // Typed write operations.  We tag byte-array(n), field-element, and
  // array-of-field-element(n).
  //
  // We make a few arbitrary choices that make no real difference.
  // All lengths are 64-bit.  We distinguish a field element from
  // an array of one field element, which is kind of arbitrary.

  // byte string
  void write(const uint8_t data[/*n*/], size_t n) {
    tag(TAG_BSTR);
    length(n);

    write_untyped(data, n);
    count_write(1 + 8 + n);
  }

  // N zero bytes
  void write0(size_t n) {
    tag(TAG_BSTR);
    length(n);

    count_write(1 + 8 + n);
    uint8_t data[32] = {};
    for (; n > 32; n -= 32) {
      write_untyped(data, 32);
    }
    write_untyped(data, n);
  }

  // one field element
  template <class Field>
  void write(const typename Field::Elt &e, const Field &F) {
    tag(TAG_FIELD_ELEM);

    write_untyped(e, F);
    count_write(1 + Field::kBytes);
  }

  // array of field elements
  template <class Field>
  void write(const typename Field::Elt e[/*n*/], size_t ince, size_t n,
             const Field &F) {
    tag(TAG_ARRAY);
    length(n);

    for (size_t i = 0; i < n; ++i) {
      write_untyped(e[i * ince], F);
    }
    count_write(1 + 8 + n * Field::kBytes);
  }

private:
  explicit BasicTranscript(const Hash &sha, const Seed &seed, size_t budget,
                           bool exhausted, size_t version,
                           const TranscriptStats &stats)
      : sha_(), seed_(seed), budget_(budget), exhausted_(exhausted),
        version_(version), stats_(stats) {
    sha_.CopyState(sha);
  }

  void count_write(size_t n) {
    ++stats_.writes;
    stats_.write_bytes += n;
    if (n > stats_.max_write_bytes) {
      stats_.max_write_bytes = n;
    }
  }

  // Output a 1-byte tag
  void tag(size_t t) {
    uint8_t d = static_cast<uint8_t>(t);
    write_untyped(&d, 1);
  }

  // Output a 8-byte length.  We pass the length
  // as size_t, but we always write it as uint64_t
  void length(size_t x) {
    uint8_t a[8];
    u64_to_le(a, x);
    write_untyped(a, 8);
  }

  // Close the open challenge point, if any: absorb its write-back
  //     TAG_CHALLENGE || u64le(k) || the first k bytes of its stream.
  void close_point() {
    if (!xof_) {
      return;
    }
    uint8_t hdr[9];
    hdr[0] = static_cast<uint8_t>(TAG_CHALLENGE);
    u64_to_le(hdr + 1, kDigestSize);
    sha_.Update(hdr, sizeof(hdr));
    sha_.Update(xof_->head(), kDigestSize);
    stats_.writeback_bytes += sizeof(hdr) + kDigestSize;
    xof_.reset();
  }

  void write_untyped(const uint8_t data[/*n*/], size_t n) {
    close_point();
    sha_.Update(data, n);
  }

  template <class Field>
  void write_untyped(const typename Field::Elt &e, const Field &F) {
    uint8_t buf[Field::kBytes];
    F.to_bytes_field(buf, e);
    write_untyped(buf, sizeof(buf));
  }

  Hash sha_;
  std::unique_ptr<FSXOF> xof_;
  Seed seed_;
  size_t budget_;
  bool exhausted_;
  const size_t version_; // version 4+ fixes the TAG_ARRAY typo.
  TranscriptStats stats_;
};

using ProofSeed = BasicProofSeed<>;
using Transcript = BasicTranscript<>;
} // namespace proofs

#endif // PRIVACY_PROOFS_ZK_LIB_RANDOM_TRANSCRIPT_H_
