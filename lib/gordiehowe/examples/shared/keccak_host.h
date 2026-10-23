// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Host Keccak for the tests and the hash comparisons: the FIPS 202 sponge
// parameters, the Keccak-f[1600] round states of a sequence of
// permutations (KeccakTrace, KeccakHost), and the sponge on bytes
// (KeccakSpongeHost), from the reference rounds (sha3_reference.h).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_KECCAK_HOST_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_KECCAK_HOST_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "circuits/tests/sha3/sha3_reference.h"
#include "util/panic.h"

namespace proofs {

// Rate in bytes, domain suffix, and digest length (0 for an XOF).
struct SpongeSpec {
  size_t rate;
  uint8_t suffix;
  size_t digest;
};
inline constexpr SpongeSpec kShake128{168, 0x1f, 0};
inline constexpr SpongeSpec kShake256{136, 0x1f, 0};
inline constexpr SpongeSpec kSha3_256{136, 0x06, 32};

namespace keccak_sponge {
// Padded byte i of absorb block j of an n-byte message, when it is not a
// message byte.
inline uint8_t pad(const SpongeSpec &s, size_t n, size_t j, size_t i) {
  const size_t blocks = n / s.rate + 1;
  uint8_t v = j * s.rate + i == n ? s.suffix : 0;
  if (j + 1 == blocks && i + 1 == s.rate) v ^= 0x80;
  return v;
}
// The lane holding rate byte i, as the state word index 5x + y.
inline size_t lane(size_t i) {
  const size_t l = i / 8;
  return 5 * (l % 5) + l / 5;
}
inline void check_spec(const SpongeSpec &s, size_t outlen) {
  check(s.rate % 8 == 0 && s.rate < 200, "sponge rate");
  check(s.digest == 0 || outlen == s.digest, "fixed-length digest");
}
}  // namespace keccak_sponge

// The round states of a sequence of permutations: state[24 p + r] is the
// output of round r of permutation p, lane (x, y) at index 5 x + y.
struct KeccakTrace {
  using State = std::array<uint64_t, 25>;
  static constexpr size_t kNoStart = ~size_t(0);
  State initial{};
  std::vector<State> state;
  // Inputs: starts[j] is the input of permutation start_perms[j], and every
  // other permutation takes the previous output. An empty start_perms
  // places the starts at permutations 0..starts.size()-1.
  std::vector<State> starts;
  std::vector<size_t> start_perms;
  // Index into starts of permutation p's committed input, or kNoStart.
  size_t start_of(size_t p) const {
    if (start_perms.empty())
      return p < starts.size() ? p : kNoStart;
    auto it = std::lower_bound(start_perms.begin(), start_perms.end(), p);
    return it != start_perms.end() && *it == p ? size_t(it - start_perms.begin())
                                               : kNoStart;
  }
  static void load(const State &s, uint64_t a[5][5]) {
    for (size_t x = 0; x < 5; ++x)
      for (size_t y = 0; y < 5; ++y)
        a[x][y] = s[5 * x + y];
  }
  static State save(const uint64_t a[5][5]) {
    State s;
    for (size_t x = 0; x < 5; ++x)
      for (size_t y = 0; y < 5; ++y)
        s[5 * x + y] = a[x][y];
    return s;
  }
  // Keccak-f[1600] on a, appending the output of every round to rounds when
  // it is given.
  static void permute(uint64_t a[5][5], std::vector<State> *rounds = nullptr) {
    for (size_t r = 0; r < 24; ++r) {
      Sha3Reference::theta(a);
      Sha3Reference::rho(a);
      uint64_t b[5][5];
      Sha3Reference::pi(a, b);
      Sha3Reference::chi(b, a);
      Sha3Reference::iota(a, r);
      if (rounds)
        rounds->push_back(save(a));
    }
  }
  void generate(size_t permutations) {
    check(start_perms.empty() || start_perms.size() == starts.size(),
          "permutation inputs");
    check(start_perms.empty() ? starts.size() <= permutations
                              : start_perms.back() < permutations,
          "permutation inputs");
    state.clear();
    uint64_t a[5][5];
    load(initial, a);
    for (size_t p = 0; p < permutations; ++p) {
      const size_t j = start_of(p);
      if (j != kNoStart)
        load(starts[j], a);
      permute(a, &state);
    }
  }
};

// A sequence of Keccak-f[1600] permutations on concrete states: each
// starts from a given state or chains from the previous output.
struct KeccakHost {
  using State = KeccakTrace::State;
  std::vector<size_t> start_perms;
  std::vector<State> starts;
  std::vector<State> outputs;

  // A permutation of input s; returns its index.
  size_t start(const State &s) {
    start_perms.push_back(outputs.size());
    starts.push_back(s);
    return run(s);
  }
  // A permutation of the previous output; returns its index.
  size_t chain() {
    check(!outputs.empty(), "chain() needs a previous permutation");
    return run(outputs.back());
  }
  const State &output(size_t p) const { return outputs.at(p); }
  // The round states of every permutation so far.
  KeccakTrace trace() const {
    check(!starts.empty(), "no permutations");
    KeccakTrace t;
    t.initial = starts[0];
    t.starts = starts;
    t.start_perms = start_perms;
    t.generate(outputs.size());
    return t;
  }

 private:
  size_t run(const State &s) {
    uint64_t a[5][5];
    KeccakTrace::load(s, a);
    KeccakTrace::permute(a);
    outputs.push_back(KeccakTrace::save(a));
    return outputs.size() - 1;
  }
};

// The FIPS 202 sponge on bytes, recording its permutations in a KeccakHost.
class KeccakSpongeHost {
 public:
  using State = KeccakHost::State;
  explicit KeccakSpongeHost(KeccakHost &host) : host_(host) {}

  std::vector<uint8_t> hash(const SpongeSpec &s,
                            const std::vector<uint8_t> &in, size_t outlen) {
    keccak_sponge::check_spec(s, outlen);
    const size_t blocks = in.size() / s.rate + 1;
    State state{};
    size_t p = 0;
    for (size_t j = 0; j < blocks; ++j) {
      for (size_t i = 0; i < s.rate; ++i) {
        const size_t at = j * s.rate + i;
        const uint8_t byte =
            at < in.size() ? in[at] : keccak_sponge::pad(s, in.size(), j, i);
        state[keccak_sponge::lane(i)] ^= uint64_t(byte) << (8 * (i % 8));
      }
      p = host_.start(state);
      state = host_.output(p);
    }
    std::vector<uint8_t> out;
    out.reserve(outlen);
    while (out.size() < outlen) {
      if (!out.empty()) p = host_.chain();
      const State &o = host_.output(p);
      const size_t take = std::min(s.rate, outlen - out.size());
      for (size_t i = 0; i < take; ++i)
        out.push_back(uint8_t(o[keccak_sponge::lane(i)] >> (8 * (i % 8))));
    }
    return out;
  }

 private:
  KeccakHost &host_;
};

}  // namespace proofs

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_SHARED_KECCAK_HOST_H_
