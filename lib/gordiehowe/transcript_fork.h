// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The transcript forks and joins of the GordieHowe prover and verifier
// (research branch parallel-domains): a series-parallel Fiat-Shamir
// schedule. Every byte they add is in this file and in
// BasicTranscript::fork (random/transcript.h).
//
// A write is a typed byte string: TAG_BSTR (the byte 0x00), u64le(length),
// payload. A challenge point's write-back is TAG_CHALLENGE (0x03), u64le(k),
// the first k bytes of its stream, k the hash's digest size; it is absorbed
// when the point closes (the next write, or a fork).
//
// Fork of a parent transcript P into branches b = 0, 1, ...:
//   1. P closes its open challenge point, if any: P absorbs its write-back.
//      No point is then open (checked).
//   2. Branch b starts as a copy of P's state: the running hash, the proof
//      seed sigma, the stream budget, the exhaustion flag and the version,
//      with no point open.
//   3. Its first item is one write of
//        "gordiehowe.branch" || u64le(domain) || u64le(b) || field name
//      (17 + 8 + 8 + |name| bytes; the name is DomainProfile::field_name).
//   4. It then absorbs its own items.
//
// Domain fork: P is the main transcript after the last phase; domain d's
// branch has domain = d (its index in compiled order) and b = 0. Nothing
// follows the domains, so there is no join.
//
// Nested fork: P is domain d's transcript before its reductions; the
// branches are the batches in compiled order (b = 0 .. nb - 1), then GKR
// (b = nb), each with domain = d.
//
// Join of a nested fork, before the packing stages and Ligero: P's state is
// still the fork point's (P is not written between the fork and the join).
// For each branch b in order:
//   1. the branch closes its open point, if any (its write-back absorbed);
//   2. its digest D_b = get(): k bytes, the digest of its running hash;
//   3. P absorbs one write of
//        "gordiehowe.join" || u64le(domain) || u64le(b) || D_b
//      (15 + 8 + 8 + k bytes);
//   4. P ORs in the branch's exhaustion.
// P then continues as before: its next challenge point's key is the digest
// of its running hash.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TRANSCRIPT_FORK_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TRANSCRIPT_FORK_H_

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#include "random/transcript.h"
#include "util/serialization.h"

namespace proofs::gordiehowe::fork {

constexpr char kBranchLabel[] = "gordiehowe.branch";
constexpr char kJoinLabel[] = "gordiehowe.join";

// TAG || u64le(domain) || u64le(branch) || TAIL.
inline std::vector<uint8_t> payload(const char *tag, uint64_t domain,
                                    uint64_t branch, const uint8_t *tail,
                                    size_t n) {
  std::vector<uint8_t> out(tag, tag + std::strlen(tag));
  uint8_t u[8];
  u64_to_le(u, domain);
  out.insert(out.end(), u, u + 8);
  u64_to_le(u, branch);
  out.insert(out.end(), u, u + 8);
  out.insert(out.end(), tail, tail + n);
  return out;
}

// The payload of a branch's label write.
inline std::vector<uint8_t> label(uint64_t domain, uint64_t branch,
                                  const std::string &field_name) {
  return payload(kBranchLabel, domain, branch,
                 reinterpret_cast<const uint8_t *>(field_name.data()),
                 field_name.size());
}

// The payload of a branch's join write, DIGEST its K-byte digest.
inline std::vector<uint8_t> join_item(uint64_t domain, uint64_t branch,
                                      const uint8_t *digest, size_t k) {
  return payload(kJoinLabel, domain, branch, digest, k);
}

// Branch (DOMAIN, B) of P: fork steps 1-3.
template <class Hash>
std::unique_ptr<BasicTranscript<Hash>> branch(BasicTranscript<Hash> &p,
                                              uint64_t domain, uint64_t b,
                                              const std::string &field_name) {
  p.close_open_point();
  if (p.point_open())
    throw std::logic_error("transcript fork: a challenge point is open");
  const auto l = label(domain, b, field_name);
  return p.fork(l.data(), l.size());
}

// The domain fork of the main transcript T: domain d's branch is (d, 0).
template <class Hash>
std::vector<std::unique_ptr<BasicTranscript<Hash>>> domains(
    BasicTranscript<Hash> &t, const std::vector<std::string> &field_names) {
  std::vector<std::unique_ptr<BasicTranscript<Hash>>> out;
  for (size_t d = 0; d < field_names.size(); ++d)
    out.push_back(branch(t, d, 0, field_names[d]));
  return out;
}

// The nested fork of domain DOMAIN's transcript D into N branches.
template <class Hash>
std::vector<std::unique_ptr<BasicTranscript<Hash>>> split(
    BasicTranscript<Hash> &d, uint64_t domain, const std::string &field_name,
    size_t n) {
  std::vector<std::unique_ptr<BasicTranscript<Hash>>> out;
  for (size_t b = 0; b < n; ++b) out.push_back(branch(d, domain, b, field_name));
  return out;
}

// The join of BRANCHES of domain DOMAIN into its transcript D.
template <class Hash>
void join(BasicTranscript<Hash> &d,
          const std::vector<std::unique_ptr<BasicTranscript<Hash>>> &branches,
          uint64_t domain) {
  if (d.point_open())
    throw std::logic_error("transcript join: a challenge point is open");
  for (size_t b = 0; b < branches.size(); ++b) {
    branches[b]->close_open_point();
    uint8_t digest[Hash::kDigestSize];
    branches[b]->get(digest);
    const auto item = join_item(domain, b, digest, sizeof(digest));
    d.write(item.data(), item.size());
    d.absorb_exhausted(branches[b]->exhausted());
  }
}

}  // namespace proofs::gordiehowe::fork

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_TRANSCRIPT_FORK_H_
