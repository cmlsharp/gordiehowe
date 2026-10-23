// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: SHA-256 (FIPS 180-4) as a library function over the core. A
// target that uses it links flatsha (lib/circuits/sha), the host witness of the
// GKR mode.
//
//   sha256(s, H, name, msg[, mode])         -> the digest, Bit [256]
//   sha256_batch(s[H], name[, mode])        -> a scope for calls;
//                                              sha256(batch, name, msg)
//                                              adds a call to it
//   sha256_varlen(batch, name, buf, in_message[, min_blocks])
//                                           -> the digest of a message of
//                                              private length in BUF
//
// The message is a SpongeInput, as shake256 takes (keccak.h): Bit values of
// H (committed, statement values or public computations) and constant
// bytes, in order; message bit 8 m + i is bit i of byte m. The gadget pads
// the message and runs as many blocks as its length needs (public). The
// digest's bit 8 m + i is bit i of digest byte m.
//
// Two modes (Sha256Mode):
//   kBatched (the default)  every 32-bit sum, Ch and Maj of every block
//                           committed, and the step relations as
//                           assert_zero predicates of degree 2, which
//                           placement merges, with every other call's in
//                           the domain, into one batch;
//   kGkr                    Longfellow's FlatSHA256Circuit checks as
//                           predicates in GKR, over Bit advice of its
//                           block witnesses (FlatSHA256Witness): 184 words
//                           of 32 bits per block, the rounds recomputed in
//                           GKR, the additions checked by arith.h's
//                           assert_sum_mod (BitAdder's characteristic-2
//                           form) with ch, maj and xor3.
//
// The batched mode states FIPS 180-4's compression as written, a loop over
// rounds on named working variables (words [32], bit 0 least significant),
// every block of a call at once (a working variable is a word of each
// block, [nb, 32]):
//   schedule  W_t = sigma1(W_{t-2}) + W_{t-7} + sigma0(W_{t-15}) + W_{t-16}
//             for t = 16..63, W_0..W_15 views of the padded message (its
//             constant bits constants);
//   round t   ch = Ch(e, f, g), maj = Maj(a, b, c),
//             t1 = h + Sigma1(e) + ch + W_t + K_t, t2 = Sigma0(a) + maj,
//             (a, ..., h) <- (t1 + t2, a, b, c, d + t1, e, f, g);
//   chain     H' = H + (a, ..., h) after round 63, H the IV for the first
//             block and the previous block's H' for the others.
// A call commits its values as named families (W_16..W_63, every round's
// ch, maj, t1, t2, a and e, the partial sums, H', each of every block),
// each a Bit value of its own shape that a host closure computes from the
// message words. Round t reads row t of each family. A sum of k words is
// arith.h's assert_sum over k - 2 committed partial sums, each step one
// assert_add_majority (one product per bit); Ch and Maj are stated in
// their one-product forms e & (f ^ g) ^ g and (a ^ c) & (b ^ c) ^ c. Every
// predicate has degree 2 and Keccak's chi shape a b + c (a one-block
// call's first Ch and Maj of the IV, affine, join the same shape), so
// placement merges them, with every other call's and Keccak's in the
// domain, into one batch. Rotations, shifts and XOR (the sigmas, the
// carries) are views and commit nothing. Per block: 48 x 3 schedule words,
// 64 x 9 round words (ch, maj, three partial sums and t1, t2, a, e) and H',
// 728 words of 32 bits. The digest is the last block's H' in digest order.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_SHA256_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_SHA256_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <map>
#include <memory>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "circuits/sha/flatsha256_witness.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/lib/arith.h"
#include "gordiehowe/lib/keccak.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::sha256 {

// How sha256 proves a call: one batched relation over every call of the
// batch, or Longfellow's flat SHA-256 checks as predicates in GKR.
enum class Sha256Mode : uint8_t { kBatched = 0, kGkr = 1 };

namespace sha256_internal {

constexpr uint32_t kIV[8] = {0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u,
                             0xa54ff53au, 0x510e527fu, 0x9b05688cu,
                             0x1f83d9abu, 0x5be0cd19u};
constexpr uint32_t kK[64] = {
    0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u, 0x3956c25bu,
    0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u, 0xd807aa98u, 0x12835b01u,
    0x243185beu, 0x550c7dc3u, 0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u,
    0xc19bf174u, 0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu,
    0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau, 0x983e5152u,
    0xa831c66du, 0xb00327c8u, 0xbf597fc7u, 0xc6e00bf3u, 0xd5a79147u,
    0x06ca6351u, 0x14292967u, 0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu,
    0x53380d13u, 0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u,
    0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u, 0xd192e819u,
    0xd6990624u, 0xf40e3585u, 0x106aa070u, 0x19a4c116u, 0x1e376c08u,
    0x2748774cu, 0x34b0bcb5u, 0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu,
    0x682e6ff3u, 0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
    0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u};

// The padded message of MSG_BYTES bytes: for each padded byte, the message
// byte it holds (its index) or, past the message, the constant byte. Public.
struct PaddedByte {
  long msg;  // the message byte, or -1
  uint8_t constant;
};
inline size_t blocks_of(size_t msg_bytes) { return (msg_bytes + 9 + 63) / 64; }
inline std::vector<PaddedByte> padding(size_t msg_bytes) {
  const size_t n = 64 * blocks_of(msg_bytes);
  std::vector<PaddedByte> out(n, PaddedByte{-1, 0});
  for (size_t i = 0; i < msg_bytes; ++i) out[i].msg = long(i);
  out[msg_bytes].constant = 0x80;
  const uint64_t bits = uint64_t(msg_bytes) * 8;
  for (size_t i = 0; i < 8; ++i)
    out[n - 1 - i].constant = uint8_t(bits >> (8 * i));
  return out;
}

// The layout of a message of MSG_BYTES bytes (a multiple of 64) that the
// caller padded: every byte is a message byte.
inline std::vector<PaddedByte> unpadded(size_t msg_bytes) {
  check(msg_bytes % 64 == 0, "SHA-256: an unpadded message of whole blocks");
  std::vector<PaddedByte> out(msg_bytes, PaddedByte{-1, 0});
  for (size_t i = 0; i < msg_bytes; ++i) out[i].msg = long(i);
  return out;
}

// The bytes of message bits BITS (bit 8 m + i is bit i of byte m), by
// shifts and masks.
template <class F>
std::vector<uint8_t> message_bytes(const F &f,
                                   const std::vector<typename F::Elt> &bits) {
  std::vector<uint8_t> m(bits.size() / 8, 0);
  for (size_t k = 0; k < bits.size(); ++k)
    m[k / 8] |= uint8_t(ct::bit_of(f, bits[k]) << (k % 8));
  return m;
}

// The message words of the padded blocks, [nb, 16, 32]: word t of block j
// is big-endian bytes 64 j + 4 t .. + 3, bit p of the word (least
// significant first) bit p mod 8 of byte 64 j + 4 t + 3 - p / 8. BITS are
// the message bits, PAD the padding's constant bytes after them.
template <class F>
Expr<F, Bit> padded_words(const Domain<F> &H, const Expr<F, Bit> &bits,
                          const std::vector<PaddedByte> &pad) {
  const size_t msg_bits = bits.size(), n = pad.size(), nb = n / 64;
  std::vector<uint64_t> tail;
  for (size_t m = msg_bits / 8; m < n; ++m)
    for (size_t i = 0; i < 8; ++i) tail.push_back((pad[m].constant >> i) & 1);
  const Expr<F, Bit> all =
      tail.empty() ? bits : Expr<F, Bit>(bits.concat(H.constant(Bit{}, tail)));
  std::vector<size_t> idx;
  idx.reserve(8 * n);
  for (size_t j = 0; j < nb; ++j)
    for (size_t t = 0; t < 16; ++t)
      for (size_t p = 0; p < 32; ++p)
        idx.push_back(8 * (64 * j + 4 * t + (3 - p / 8)) + p % 8);
  return all.reindex(idx).reshape({nb, 16, 32});
}

// SHA-256's bit functions on words [..., 32] (least significant bit
// first): rotr(x, r) is x.rotate(-r) along the last axis; shr fills zeros.
template <class F>
Expr<F, Bit> rotr(const Expr<F, Bit> &x, long r) {
  return x.rotate(-r, x.dims().size() - 1);
}
template <class F>
Expr<F, Bit> shr(const Domain<F> &H, const Expr<F, Bit> &x, size_t s) {
  const auto d = x.dims();
  const size_t m = x.size() / 32;
  const auto z = H.constant(Bit{}, std::vector<uint64_t>(m * s, 0),
                            Shape{m, s});
  return x.reshape({m, 32}).slice(s, 32, 1).concat(z, 1).reshape(Shape(d));
}
template <class F>
Expr<F, Bit> big_sigma0(const Expr<F, Bit> &x) {
  return lib::arith::xor3(rotr(x, 2), rotr(x, 13), rotr(x, 22));
}
template <class F>
Expr<F, Bit> big_sigma1(const Expr<F, Bit> &x) {
  return lib::arith::xor3(rotr(x, 6), rotr(x, 11), rotr(x, 25));
}
template <class F>
Expr<F, Bit> small_sigma0(const Domain<F> &H, const Expr<F, Bit> &x) {
  return lib::arith::xor3(rotr(x, 7), rotr(x, 18), shr(H, x, 3));
}
template <class F>
Expr<F, Bit> small_sigma1(const Domain<F> &H, const Expr<F, Bit> &x) {
  return lib::arith::xor3(rotr(x, 17), rotr(x, 19), shr(H, x, 10));
}
// Constant words W ([m]) as Bit words [m, 32].
template <class F>
Expr<F, Bit> constant_words(const Domain<F> &H,
                            const std::vector<uint32_t> &w) {
  std::vector<uint64_t> b;
  for (uint32_t x : w)
    for (size_t p = 0; p < 32; ++p) b.push_back((x >> p) & 1);
  return H.constant(Bit{}, b, Shape{w.size(), 32});
}

}  // namespace sha256_internal

// A batch of SHA-256 calls in domain H: a scope for their names, and their
// mode. In the batched mode placement merges the calls' step predicates
// (of one shape, and Keccak's) into one batch; in the GKR mode each call
// has its own circuit predicates.
template <class F>
class Sha256Batch {
 public:
  Sha256Batch(Domain<F> &d, std::string name, Sha256Mode mode,
              std::function<std::string(const std::string &)> scoped)
      : d_(&d), name_(std::move(name)), mode_(mode),
        scoped_(std::move(scoped)) {
    static_assert(F::kCharacteristicTwo && F::kSubFieldBits == 16,
                  "sha256: a binary field with its GF(2^16) subfield");
  }
  Domain<F> &domain() const { return *d_; }
  const std::string &name() const { return name_; }
  Sha256Mode mode() const { return mode_; }
  // A call's name in the batch's scope.
  std::string scoped(const std::string &nm) const { return scoped_(nm); }

 private:
  Domain<F> *d_;
  std::string name_;
  Sha256Mode mode_;
  std::function<std::string(const std::string &)> scoped_;
};

// A SHA-256 batch in H named NAME, in MODE.
template <class F>
Sha256Batch<F> sha256_batch(Domain<F> &H, const std::string &name,
                            Sha256Mode mode = Sha256Mode::kBatched) {
  return Sha256Batch<F>(H, name, mode,
                        [](const std::string &nm) { return nm; });
}
// The same through a scope: the batch's and its calls' names carry its
// prefix.
template <class F>
Sha256Batch<F> sha256_batch(const ScopedDomain<F> &H, const std::string &name,
                            Sha256Mode mode = Sha256Mode::kBatched) {
  return Sha256Batch<F>(H.domain(), H.scoped(name), mode,
                        [H](const std::string &nm) { return H.scoped(nm); });
}

namespace sha256_internal {

// Words of 32 bits in FlatSHA256Circuit's block witness (outw, oute, outa,
// h1), the GKR mode's advice.
constexpr size_t kWitnessWords = 48 + 64 + 64 + 8;

// ------------------------------------------------------------ batched --

// The working variables a..h before a round, each a word [32].
template <class F>
struct State {
  Expr<F, Bit> a, b, c, d, e, f, g, h;
};

// The values X, each of one shape, stacked along a new first axis.
template <class F>
Expr<F, Bit> stack(const std::vector<Expr<F, Bit>> &x) {
  std::vector<size_t> d = x.at(0).dims();
  d.insert(d.begin(), 1);
  Expr<F, Bit> out = x[0].reshape(Shape(d));
  for (size_t k = 1; k < x.size(); ++k)
    out = out.concat(x[k].reshape(Shape(d)));
  return out;
}

// The words a call of NB blocks commits, by family (bit 0 of a word least
// significant), each row a step of every block, but the chaining values,
// by block:
//   w    [48, nb, 32]      W_16..W_63
//   w.p  [48, 2, nb, 32]   their partial sums sigma1(W_{t-2}) + W_{t-7} and
//                          that + sigma0(W_{t-15})
//   ch, maj, t1, t2, a, e  [64, nb, 32]  each round's Ch, Maj, t1, t2 and
//                          new a and e
//   t1.p [64, 3, nb, 32]   t1's partial sums h + Sigma1(e), + ch, + W_t
//   h    [nb - 1, 8, 32]   the chaining value after each block but the
//                          last (none for one block)
//   h.last [8, 32]         the chaining value after the last block, which
//                          the digest reads (its own value: a circuit that
//                          reads the digest reads its words only)
enum class Family : uint8_t { kW, kWp, kCh, kMaj, kT1p, kT1, kT2, kA, kE, kH };
constexpr size_t kNumTraceFamilies = size_t(Family::kH) + 1;
// The blocks of a committed family: every block row-major ([rows, (parts,)
// nb, 32]), or the blocks before the last or the last block, block-major
// ([nb - 1, rows, 32], [rows, 32]).
enum class Blocks : uint8_t { kAll, kButLast, kLast };
struct FamilyInfo {
  // The trace family whose words it holds
  Family f;
  const char *name;
  // ROWS rows of PARTS words per block
  size_t rows, parts;
  Blocks blocks;
};
inline constexpr FamilyInfo kFamilies[] = {
    {Family::kW, "w", 48, 1, Blocks::kAll},
    {Family::kWp, "w.p", 48, 2, Blocks::kAll},
    {Family::kCh, "ch", 64, 1, Blocks::kAll},
    {Family::kMaj, "maj", 64, 1, Blocks::kAll},
    {Family::kT1p, "t1.p", 64, 3, Blocks::kAll},
    {Family::kT1, "t1", 64, 1, Blocks::kAll},
    {Family::kT2, "t2", 64, 1, Blocks::kAll},
    {Family::kA, "a", 64, 1, Blocks::kAll},
    {Family::kE, "e", 64, 1, Blocks::kAll},
    {Family::kH, "h", 8, 1, Blocks::kButLast},
    {Family::kH, "h.last", 8, 1, Blocks::kLast}};

// The host computation of blocks: every family's words, row-major, the
// blocks one after another. Branch-free in the message.
struct HostTrace {
  std::vector<uint32_t> fam[kNumTraceFamilies];
};
inline uint32_t rotr32(uint32_t x, unsigned r) {
  return (x >> r) | (x << (32 - r));
}
// One block's compression of the chaining value H (updated in place) with
// the 64 bytes BLOCK, appended to T.
inline void host_block(uint32_t H[8], const uint8_t *block, HostTrace &T) {
  auto put = [&T](Family f, uint32_t v) { T.fam[size_t(f)].push_back(v); };
  uint32_t W[64];
  for (size_t t = 0; t < 16; ++t) {
    const uint8_t *p = &block[4 * t];
    W[t] = (uint32_t(p[0]) << 24) | (uint32_t(p[1]) << 16) |
           (uint32_t(p[2]) << 8) | uint32_t(p[3]);
  }
  for (size_t t = 16; t < 64; ++t) {
    const uint32_t x = W[t - 2], y = W[t - 15];
    const uint32_t s1 = rotr32(x, 17) ^ rotr32(x, 19) ^ (x >> 10);
    const uint32_t s0 = rotr32(y, 7) ^ rotr32(y, 18) ^ (y >> 3);
    const uint32_t p2 = s1 + W[t - 7];
    const uint32_t p3 = p2 + s0;
    W[t] = p3 + W[t - 16];
    put(Family::kWp, p2);
    put(Family::kWp, p3);
    put(Family::kW, W[t]);
  }
  uint32_t a = H[0], b = H[1], c = H[2], d = H[3];
  uint32_t e = H[4], f = H[5], g = H[6], h = H[7];
  for (size_t t = 0; t < 64; ++t) {
    const uint32_t vch = (e & f) ^ (~e & g);
    const uint32_t vmaj = (a & b) ^ (a & c) ^ (b & c);
    const uint32_t S1 = rotr32(e, 6) ^ rotr32(e, 11) ^ rotr32(e, 25);
    const uint32_t S0 = rotr32(a, 2) ^ rotr32(a, 13) ^ rotr32(a, 22);
    const uint32_t p2 = h + S1;
    const uint32_t p3 = p2 + vch;
    const uint32_t p4 = p3 + W[t];
    const uint32_t t1 = p4 + kK[t];
    const uint32_t t2 = S0 + vmaj;
    put(Family::kCh, vch);
    put(Family::kMaj, vmaj);
    put(Family::kT1p, p2);
    put(Family::kT1p, p3);
    put(Family::kT1p, p4);
    put(Family::kT1, t1);
    put(Family::kT2, t2);
    h = g;
    g = f;
    f = e;
    e = d + t1;
    d = c;
    c = b;
    b = a;
    a = t1 + t2;
    put(Family::kA, a);
    put(Family::kE, e);
  }
  const uint32_t X[8] = {a, b, c, d, e, f, g, h};
  for (size_t k = 0; k < 8; ++k) {
    H[k] += X[k];
    put(Family::kH, H[k]);
  }
}
// Every block of the padded message PADDED, from the IV.
inline HostTrace host_trace(const std::vector<uint8_t> &padded) {
  HostTrace T;
  uint32_t H[8];
  for (size_t k = 0; k < 8; ++k) H[k] = kIV[k];
  for (size_t j = 0; j < padded.size() / 64; ++j)
    host_block(H, &padded[64 * j], T);
  return T;
}

// A call's committed families (above), each a Bit value named
// NAME.<family> of its shape, which the honest prover computes from the
// message words M ([nb, 16, 32]): one host closure per family, each
// compressing every block from the IV and returning the family's bits
// packed (PackedBits), two words of 32 bits to a uint64_t. The families'
// closures share one trace per witness run (WitnessRun): the first
// computes it, the others find it under the run, the message's address
// and size and NB. H is every block's chaining value, [nb, 8, 32] (a view
// of h and h.last).
template <class F>
struct Families {
  Expr<F, Bit> fam[kNumTraceFamilies];
  Expr<F, Bit> h;
  Ref<F, Bit, Committed> last;
  const Expr<F, Bit> &operator[](Family f) const { return fam[size_t(f)]; }
};
template <class F>
Families<F> families(Domain<F> &H, const std::string &name,
                     const Expr<F, Bit> &m) {
  using Elt = typename F::Elt;
  const F *pf = &H.field();
  const size_t nb = m.dims().at(0);
  Families<F> out;
  Expr<F, Bit> before;
  for (const FamilyInfo &fi : kFamilies) {
    // Its blocks j0 .. j1 - 1.
    const size_t j0 = fi.blocks == Blocks::kLast ? nb - 1 : 0;
    const size_t j1 = fi.blocks == Blocks::kButLast ? nb - 1 : nb;
    if (j1 == j0) continue;
    const bool all = fi.blocks == Blocks::kAll;
    const Shape shape = !all ? (fi.blocks == Blocks::kLast
                                    ? Shape{fi.rows, 32}
                                    : Shape{j1 - j0, fi.rows, 32})
                        : fi.parts == 1 ? Shape{fi.rows, nb, 32}
                                        : Shape{fi.rows, fi.parts, nb, 32};
    const size_t k = size_t(fi.f), per = fi.rows * fi.parts;
    const auto v = H.priv(
        Bit{}, name + "." + fi.name, shape, depends_on(m),
        [pf, k, per, nb, j0, j1, all](const std::vector<Elt> &mv) {
          struct Memo {
            uint64_t run = 0;
            const void *at = nullptr;
            size_t n = 0, nb = 0;
            HostTrace trace;
          };
          static thread_local Memo memo;
          if (witness_run == 0 || memo.run != witness_run ||
              memo.at != mv.data() || memo.n != mv.size() || memo.nb != nb) {
            // The blocks' bytes: word t of block j big-endian at 64 j + 4 t.
            // In chunks of words under a runner (util/parallel.h).
            std::vector<uint8_t> padded(64 * nb);
            uint8_t *const pd = padded.data();
            const Elt *const mp = mv.data();
            parallel::for_chunks(
                16 * nb, parallel::grain_for(16 * nb, parallel::kChunks),
                [pd, mp, pf](size_t q0, size_t q1) {
                  for (size_t q = q0; q < q1; ++q) {
                    uint32_t w = 0;
                    for (size_t p = 0; p < 32; ++p)
                      w |= uint32_t(ct::bit_of(*pf, mp[32 * q + p])) << p;
                    for (size_t b = 0; b < 4; ++b)
                      pd[4 * q + b] = uint8_t(w >> (24 - 8 * b));
                  }
                });
            memo.trace = host_trace(padded);
            memo.run = witness_run;
            memo.at = mv.data();
            memo.n = mv.size();
            memo.nb = nb;
          }
          const HostTrace &T = memo.trace;
          // Word q of block j (the trace's entry per j + q) at row-major
          // position q nb + j, or block-major (j - j0) per + q; position at
          // is bits 32 (at % 2) .. of packed word at / 2.
          const std::vector<uint32_t> &w = T.fam[k];
          const size_t slots = per * (j1 - j0), nw = (slots + 1) / 2;
          // The packed words in chunks under a runner (util/parallel.h),
          // each chunk writing its own words. Raw pointers: a store may
          // alias the vectors' own members.
          PackedBits bits{std::vector<uint64_t>(nw)};
          uint64_t *const out = bits.w.data();
          const uint32_t *const in = w.data();
          parallel::for_chunks(
              nw, parallel::grain_for(nw, parallel::kChunks),
              [out, in, per, nb, j0, all, slots](size_t u0, size_t u1) {
                // The block and word of position 2 u0, then of each next
                // position (no division per position).
                const size_t span = all ? nb : per;
                size_t at = 2 * u0, hi = at / span, lo = at % span;
                auto next = [&]() -> uint64_t {
                  if (at >= slots) return 0;
                  const size_t j = all ? lo : j0 + hi;
                  const size_t q = all ? hi : lo;
                  const uint64_t x = in[per * j + q];
                  ++at;
                  if (++lo == span) {
                    lo = 0;
                    ++hi;
                  }
                  return x;
                };
                for (size_t u = u0; u < u1; ++u) {
                  const uint64_t a = next();
                  out[u] = a | (next() << 32);
                }
              });
          return bits;
        });
    if (all) out.fam[k] = v;
    if (fi.blocks == Blocks::kButLast) before = v;
    if (fi.blocks == Blocks::kLast) out.last = v;
  }
  const Expr<F, Bit> last = Expr<F, Bit>(out.last).reshape({1, 8, 32});
  out.h = nb == 1 ? last : Expr<F, Bit>(before.concat(last));
  return out;
}

// The word X ([32]) in every one of NB blocks, [nb, 32].
template <class F>
Expr<F, Bit> every_block(const Expr<F, Bit> &x, size_t nb) {
  std::vector<size_t> idx(32 * nb);
  for (size_t i = 0; i < idx.size(); ++i) idx[i] = i % 32;
  return x.reindex(idx).reshape({nb, 32});
}

// The compression of every block of call NAME, the message words M ([nb,
// 16, 32]) and the round constants K ([64, 32]), from the IV: its families
// (families()) and its predicates, named NAME.*, each over every block (a
// working variable is a word [nb, 32]):
//   schedule  W_t = sigma1(W_{t-2}) + W_{t-7} + sigma0(W_{t-15}) +
//             W_{t-16} for t >= 16 (W_0..W_15 are M's words, views);
//   round t   ch = Ch(e, f, g), maj = Maj(a, b, c) in their one-product
//             forms e & (f ^ g) ^ g and (a ^ c) & (b ^ c) ^ c,
//             t1 = h + Sigma1(e) + ch + W_t + K_t, t2 = Sigma0(a) + maj,
//             and the next state (t1 + t2, a, b, c, d + t1, e, f, g);
//   chain     H' = HIN + (a, ..., h) after round 63, HIN the IV for block 0
//             and block j - 1's H' for block j (a view of the family h).
// Returns the families; H' is their h ([nb, 8, 32]).
template <class F>
Families<F> compress(Domain<F> &H, const std::string &name,
                                const Expr<F, Bit> &m,
                                const Expr<F, Bit> &K) {
  using lib::arith::assert_sum;
  const size_t nb = m.dims().at(0);
  const Families<F> C = families(H, name, m);
  const Expr<F, Bit> iv =
      constant_words(H, std::vector<uint32_t>(std::begin(kIV), std::end(kIV)))
          .reshape({8, 1, 32});
  // The chaining values by word, [8, nb, 32] (a view of h).
  std::vector<size_t> by_word;
  for (size_t q = 0; q < 8; ++q)
    for (size_t j = 0; j < nb; ++j)
      for (size_t b = 0; b < 32; ++b) by_word.push_back(32 * (8 * j + q) + b);
  const Expr<F, Bit> hw = C.h.reindex(by_word).reshape({8, nb, 32});
  const Expr<F, Bit> hin =
      nb == 1 ? iv : Expr<F, Bit>(iv.concat(hw.slice(0, nb - 1, 1), 1));
  std::vector<Expr<F, Bit>> W;
  for (size_t t = 0; t < 16; ++t) W.push_back(m.at(1, t));
  for (size_t t = 16; t < 64; ++t) {
    W.push_back(C[Family::kW][t - 16]);
    assert_sum(W[t],
               {small_sigma1(H, W[t - 2]), W[t - 7], small_sigma0(H, W[t - 15]),
                W[t - 16]},
               C[Family::kWp][t - 16], Name(name + ".w" + std::to_string(t)));
  }
  State<F> s{hin[0], hin[1], hin[2], hin[3], hin[4], hin[5], hin[6], hin[7]};
  for (size_t t = 0; t < 64; ++t) {
    const std::string rn = name + ".r" + std::to_string(t);
    const Expr<F, Bit> ch = C[Family::kCh][t];
    const Expr<F, Bit> maj = C[Family::kMaj][t];
    const Expr<F, Bit> t1 = C[Family::kT1][t];
    const Expr<F, Bit> t2 = C[Family::kT2][t];
    const Expr<F, Bit> a = C[Family::kA][t];
    const Expr<F, Bit> e = C[Family::kE][t];
    assert_equal(ch, (s.e & (s.f ^ s.g)) ^ s.g, Name(rn + ".ch"));
    assert_equal(maj, ((s.a ^ s.c) & (s.b ^ s.c)) ^ s.c, Name(rn + ".maj"));
    assert_sum(t1, {s.h, big_sigma1(s.e), ch, W[t], every_block(K[t], nb)},
               C[Family::kT1p][t], Name(rn + ".t1"));
    assert_sum(t2, {big_sigma0(s.a), maj}, Name(rn + ".t2"));
    assert_sum(a, {t1, t2}, Name(rn + ".a"));
    assert_sum(e, {s.d, t1}, Name(rn + ".e"));
    s = State<F>{a, s.a, s.b, s.c, e, s.e, s.f, s.g};
  }
  assert_sum(hw, {hin, stack<F>({s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h})},
             Name(name + ".h"));
  return C;
}

// A batched call NAME in domain H on message bits BITS, padded by PAD:
// every block's compression from the IV. Returns the families, the
// chaining values after the blocks their h ([nb, 8, 32]).
template <class F>
Families<F> chain(Domain<F> &H, const std::string &name,
                             const Expr<F, Bit> &bits,
                             const std::vector<PaddedByte> &pad) {
  const Expr<F, Bit> K = constant_words(
      H, std::vector<uint32_t>(std::begin(kK), std::end(kK)));
  return compress(H, name, padded_words(H, bits, pad), K);
}

// The digest order of block J's chaining value among the chaining values
// of NB blocks ([nb, 8, 32] flat): digest bit 8 m + i is bit 8 (3 - m mod
// 4) + i of the block's word m / 4.
inline std::vector<size_t> digest_order(size_t nb, size_t j) {
  std::vector<size_t> order;
  for (size_t m = 0; m < 32; ++m)
    for (size_t i = 0; i < 8; ++i)
      order.push_back(32 * (8 * j + m / 4) + 8 * (3 - m % 4) + i);
  return order;
}

// A batched call NAME in domain H on message bits BITS: the digest, the
// last chaining value in digest order.
template <class F>
Ref<F, Bit, Committed> batched_call(Domain<F> &H, const std::string &name,
                                    const Expr<F, Bit> &bits) {
  const auto C = chain(H, name, bits, padding(bits.size() / 8));
  return C.last.reindex(digest_order(1, 0)).named(name + ".out");
}
// A GKR call NAME on message bits BITS: Bit advice of FlatSHA256Witness's
// block witnesses (per block outw, oute, outa, h1, each word's bits low
// first) and, per block, FlatSHA256Circuit::assert_transform_block's checks
// as predicates over the words, every round at once:
//   schedule  W_t = sigma1(W_{t-2}) + W_{t-7} + sigma0(W_{t-15}) +
//             W_{t-16} mod 2^32 (t >= 16; four words);
//   E         E_t = d + T1 (six words), T1 = h + Sigma1(e) + Ch(e, f, g) +
//             K_t + W_t;
//   A         A_t = T1 + Sigma0(a) + Maj(a, b, c) (seven words);
//   chain     H1_k = H0_k + X_k (two words),
// each by arith.h's assert_sum_mod (BitAdder's characteristic-2 form), the
// state words read from the committed A and E words (a = A_{t-1}, b =
// A_{t-2}, ..., the chaining value before round 4) and T1's encoded sum
// shared by E and A. The padded message's constant bits are constants. The
// digest is the last block's h1 words in digest order.
template <class F>
Ref<F, Bit, Committed> gkr_call(Domain<F> &H, const std::string &name,
                                const Expr<F, Bit> &message) {
  using Elt = typename F::Elt;
  namespace ar = lib::arith;
  const size_t msg_bytes = message.size() / 8, nb = blocks_of(msg_bytes);
  const F *pf = &H.field();
  const auto wit = H.priv(
      Bit{}, name + ".witness", Shape(nb * kWitnessWords * 32),
      depends_on(message), [pf, nb](const std::vector<Elt> &bits) {
        const auto m = message_bytes(*pf, bits);
        uint8_t numb = 0;
        std::vector<uint8_t> padded(64 * nb);
        std::vector<FlatSHA256Witness::BlockWitness> bw(nb);
        FlatSHA256Witness::transform_and_witness_message(
            m.size(), m.data(), nb, numb, padded.data(), bw.data());
        std::vector<Elt> out;
        out.reserve(nb * kWitnessWords * 32);
        auto push = [&](const uint32_t *w, size_t count) {
          for (size_t i = 0; i < count; ++i)
            for (size_t p = 0; p < 32; ++p)
              out.push_back(ct::bit_elt(*pf, w[i] >> p));
        };
        for (const auto &x : bw) {
          push(x.outw, 48);
          push(x.oute, 64);
          push(x.outa, 64);
          push(x.h1, 8);
        }
        return out;
      });
  const Expr<F, Bit> in = padded_words(H, message, padding(msg_bytes));
  const Expr<F, Bit> w = Expr<F, Bit>(wit).reshape({nb, kWitnessWords, 32});
  const Expr<F, Bit> K = constant_words(
      H, std::vector<uint32_t>(std::begin(kK), std::end(kK)));
  Expr<F, Bit> h0 = constant_words(
      H, std::vector<uint32_t>(std::begin(kIV), std::end(kIV)));
  auto value = [&H](const Expr<F, Bit> &x) {
    return ar::word_value(H, x, 7);
  };
  for (size_t j = 0; j < nb; ++j) {
    const std::string bn = name + ".block" + std::to_string(j);
    const Expr<F, Bit> wj = w.at(j);
    const Expr<F, Bit> outw = wj.slice(0, 48);
    const Expr<F, Bit> oute = wj.slice(48, 112);
    const Expr<F, Bit> outa = wj.slice(112, 176);
    const Expr<F, Bit> h1 = wj.slice(176, 184);
    // The schedule W_0..W_63.
    const Expr<F, Bit> W = in.at(j).concat(outw);
    ar::assert_sum_mod(H, outw,
                       {small_sigma1(H, W.slice(14, 62)), W.slice(9, 57),
                        small_sigma0(H, W.slice(1, 49)), W.slice(0, 48)},
                       Name(bn + ".schedule"))
        .pin(Placement::kCircuit);
    // The state before round t: a = A[t + 3], b = A[t + 2], c = A[t + 1],
    // d = A[t]; e = E[t + 3], f = E[t + 2], g = E[t + 1], h = E[t].
    std::vector<size_t> ra = {3, 2, 1, 0}, re = {7, 6, 5, 4};
    const Expr<F, Bit> A = h0.reindex(ra, 0).concat(outa);
    const Expr<F, Bit> E = h0.reindex(re, 0).concat(oute);
    const Expr<F, Bit> a = A.slice(3, 67), bb = A.slice(2, 66),
                       c = A.slice(1, 65);
    const Expr<F, Bit> e = E.slice(3, 67), f = E.slice(2, 66),
                       g = E.slice(1, 65);
    const Expr<F> vE = value(E), vA = value(A);
    const Expr<F> t1 = ar::add_values(
        ar::add_values(ar::add_values(vE.slice(0, 64),
                                      value(big_sigma1(e))),
                       ar::add_values(value(ar::ch(e, f, g)), value(K))),
        value(W));
    ar::assert_sum_mod(H, oute, ar::add_values(t1, vA.slice(0, 64)), 6,
                       Name(bn + ".e"))
        .pin(Placement::kCircuit);
    ar::assert_sum_mod(
        H, outa,
        ar::add_values(t1, ar::add_values(value(big_sigma0(a)),
                                          value(ar::maj(a, bb, c)))),
        7, Name(bn + ".a"))
        .pin(Placement::kCircuit);
    // H1_k = H0_k + X_k, X = (a, b, c, d, e, f, g, h) after round 63.
    std::vector<size_t> rx = {67, 66, 65, 64};
    const Expr<F, Bit> X = A.reindex(rx, 0).concat(E.reindex(rx, 0));
    ar::assert_sum_mod(H, h1, {h0, X}, Name(bn + ".chain"))
        .pin(Placement::kCircuit);
    h0 = h1;
  }
  // The digest: bit 8 m + i is bit 8 (3 - m mod 4) + i of the last block's
  // h1 word m / 4.
  std::vector<size_t> order;
  for (size_t m = 0; m < 32; ++m)
    for (size_t i = 0; i < 8; ++i)
      order.push_back(((nb - 1) * kWitnessWords + 176 + m / 4) * 32 +
                      8 * (3 - m % 4) + i);
  return wit.reindex(order).named(name + ".out");
}

}  // namespace sha256_internal

// Adds SHA-256(MSG) to batch B as the call NM. Returns the digest, Bit
// [256]: bit 8 m + i is bit i of digest byte m.
template <class F>
Ref<F, Bit, Committed> sha256(const Sha256Batch<F> &b, const std::string &nm,
                              const lib::keccak::SpongeInput<F> &msg) {
  const std::string name = b.scoped(nm);
  const Expr<F, Bit> bits = lib::keccak::message_bits(b.domain(), msg);
  check(bits.size() % 8 == 0, "SHA-256 message bits");
  return b.mode() == Sha256Mode::kBatched
             ? sha256_internal::batched_call(b.domain(), name, bits)
             : sha256_internal::gkr_call(b.domain(), name, bits);
}
// A message of one Bit value.
template <class F, class T, class P>
Ref<F, Bit, Committed> sha256(const Sha256Batch<F> &b, const std::string &nm,
                              Ref<F, T, P> msg) {
  return sha256(b, nm, lib::keccak::sponge_input(msg));
}

// SHA-256(MSG) in scope S of domain H (its names under NAME.chi in the
// batched mode), in MODE. Returns the digest, Bit [256].
template <class F, class M>
Ref<F, Bit, Committed> sha256(const Scope &s, Domain<F> &H,
                              const std::string &name, const M &msg,
                              Sha256Mode mode = Sha256Mode::kBatched) {
  return sha256(sha256_batch(s[H], name + ".chi", mode), name, msg);
}

// ------------------------------------------------------ private length --

namespace sha256_internal {

// Byte O (0..7) of the length field of a J-byte message: byte O of the
// 64-bit big-endian bit length 8 J.
inline uint8_t length_byte(size_t j, size_t o) {
  return uint8_t((uint64_t(j) * 8) >> (8 * (7 - o)));
}

}  // namespace sha256_internal

// SHA-256 of a message of private length L in a buffer of N blocks. BUF holds
// 64 N bytes: the message, its padding, and zeros after them. IN_MESSAGE is a
// Bit per buffer byte, f_i = [i < L]. Every block's compression is stated as in
// sha256 (the caller's padding, sha256_internal::chain), and predicates
// NAME.padding.* in GKR check, with f_{-1} = 1 and B_i the GF(2^16) value of
// buffer byte i:
//   monotone   f_i (1 + f_{i-1}) = 0 for i >= 1, and f_{64 N - 9} = 0; so
//              f_i = [i < L] for one L <= 64 N - 9, and g_i = f_{i-1} + f_i
//              = [i = L] is one-hot;
//   blocks     G_0 = 1, G_b = f_{64 b - 9} = [L + 9 > 64 b] (0 < b < N),
//              G_N = 0, and sigma_b = G_b + G_{b+1} = [b = nb - 1] for
//              nb = ceil((L + 9) / 64), one-hot over b < N;
//   0x80       g_i (B_i + 0x80) = 0;
//   zeros      (1 + f_{i-1}) B_i = 0 at offsets 0..55 of every block: each
//              byte past the 0x80 byte is zero there;
//   length     (1 + f_{i-1}) (B_i + sigma_b LB_o) = 0 at offset 56 + o of
//              block b, with LB_o = sum_j g_j byte_o(8 j) the length
//              field's byte o, linear in f: block nb - 1 ends with 8 L
//              (big-endian), and the other bytes past the message are zero;
//   digest     sigma_b (digest + H'_b) = 0 for every block b, H'_b the
//              chaining value after block b in digest order: the digest
//              is H'_(nb - 1), as Longfellow's selection
//              (FlatSHA256Circuit::assert_hash) states it; these are
//              degree-2 predicates on committed bits, placed by cost (the
//              others in GKR).
// Soundness: the constraints hold exactly when bytes 0..64 nb - 1 of BUF
// are the FIPS 180-4 padding of M = B_0..B_{L-1}, every later byte is zero,
// and the digest is the chaining value after block nb - 1, which the
// batched relation makes SHA-256(M). Characteristic 2 has no integer sums,
// so the length is a one-hot selection of public constants (LB_o) and the
// block count a difference of monotone flags. MIN_BLOCKS adds
// G_{MIN_BLOCKS - 1} = 1, nb >= MIN_BLOCKS (Longfellow's attribute items
// fix nb = 2). The digest is advice: the committed chaining value at block
// nb - 1, read by a masked scan over the blocks. Returns the digest, Bit
// [256], bit 8 m + i of byte m as sha256 returns it.
template <class F, class PF>
Ref<F, Bit, Committed> sha256_varlen(const Sha256Batch<F> &b,
                                     const std::string &nm,
                                     const lib::keccak::SpongeInput<F> &buf,
                                     Ref<F, Bit, PF> in_message,
                                     size_t min_blocks = 1) {
  namespace si = sha256_internal;
  using Elt = typename F::Elt;
  const std::string name = b.scoped(nm);
  const std::string what = "sha256_varlen '" + name + "'";
  Domain<F> &H = b.domain();
  if (b.mode() != Sha256Mode::kBatched) fail(what + ": batched mode only");
  const Expr<F, Bit> bits = lib::keccak::message_bits(H, buf);
  if (bits.size() == 0 || bits.size() % 512 != 0)
    fail(what + ": the buffer is not a whole number of blocks");
  const size_t n = bits.size() / 8, N = n / 64;
  if (in_message.n != n)
    fail(what + ": " + std::to_string(in_message.n) + " flags for " +
         std::to_string(n) + " bytes");
  if (min_blocks < 1 || min_blocks > N)
    fail(what + ": min_blocks outside 1.." + std::to_string(N));
  // The chaining values after every block, [N, 8, 32].
  const Expr<F, Bit> h = si::chain(H, name, bits, si::unpadded(n)).h;
  const F *pf = &H.field();

  const auto digest = H.priv(
      Bit{}, name + ".out", Shape(256), depends_on(h, in_message),
      [pf, n, N](const std::vector<Elt> &hv, const std::vector<Elt> &flags) {
        const F &f = *pf;
        // No branch on the chaining values or the flags: a count, then a
        // masked scan over the blocks.
        uint64_t len = 0;
        for (size_t i = 0; i < n; ++i) len += ct::bit_of(f, flags[i]);
        const uint64_t last = (len + 9 + 63) / 64 - 1;
        std::vector<Elt> out(256, f.zero());
        for (size_t j = 0; j < N; ++j) {
          const uint64_t mk = ct::mask(ct::eq(j, last));
          const auto order = si::digest_order(N, j);
          for (size_t q = 0; q < 256; ++q)
            out[q] = ct::select(mk, hv[order[q]], out[q]);
        }
        return out;
      });

  // The padding's predicates (above), over the buffer's byte values and the
  // flags, each pinned to the GKR circuit but the digest's.
  const Expr<F, Bit> fw = in_message;
  const auto one = H.constant(Bit{}, std::vector<uint64_t>{1});
  const auto zero = H.constant(Bit{}, std::vector<uint64_t>{0});
  std::vector<Elt> beta8(8);
  for (size_t c = 0; c < 8; ++c) beta8[c] = pf->beta(c);
  // Byte values: sum_t beta_t bit_t.
  const Expr<F> B =
      (Expr<F>(bits.reshape({n, 8})) *
       H.constant(beta8))
          .sum(1);
  const Expr<F, Bit> fprev = one.concat(fw.slice(0, n - 1));
  // Monotone, and room for the 0x80 byte and the length.
  assert_zero(fw.slice(1, n) & (fw.slice(0, n - 1) ^ 1),
              Name(name + ".padding.monotone"))
      .pin(Placement::kCircuit);
  assert_zero(fw.slice(n - 9, n - 8), Name(name + ".padding.room"))
      .pin(Placement::kCircuit);
  const Expr<F, Bit> g = fprev ^ fw;
  // The 0x80 byte at L.
  assert_zero(g * (B + pf->of_scalar(0x80)), Name(name + ".padding.end"))
      .pin(Placement::kCircuit);
  // The block flags and the selector.
  std::vector<size_t> gi;
  for (size_t bk = 1; bk < N; ++bk) gi.push_back(64 * bk - 9);
  const Expr<F, Bit> G =
      N > 1 ? Expr<F, Bit>(one.concat(fw.reindex(gi)).concat(zero))
            : Expr<F, Bit>(one.concat(zero));
  if (min_blocks >= 2)
    assert_zero(G.slice(min_blocks - 1, min_blocks) ^ 1,
                Name(name + ".padding.min_blocks"))
        .pin(Placement::kCircuit);
  const Expr<F, Bit> sigma = G.slice(0, N) ^ G.slice(1, N + 1);
  // The length field's bytes, linear in g: LB_o = sum_j byte_o(8 j) g_j.
  std::vector<Elt> lc(8 * (n - 8));
  for (size_t o = 0; o < 8; ++o)
    for (size_t j = 0; j + 9 <= n; ++j)
      lc[o * (n - 8) + j] = pf->of_scalar(si::length_byte(j, o));
  const Expr<F> LB = (Expr<F>(g.slice(0, n - 8).reshape({1, n - 8})) *
                      H.constant(lc, Shape{8, n - 8}))
                         .sum(1);
  // Zeros past the 0x80 byte; the length in block nb - 1: byte i of block
  // bk at offset o >= 56 is sigma_bk LB_(o - 56).
  const Expr<F> P =
      (Expr<F>(sigma.reshape({N, 1})) * LB.reshape({1, 8})).flat();
  std::vector<size_t> ti(n);
  for (size_t i = 0; i < n; ++i)
    ti[i] = i % 64 < 56 ? 8 * N : 8 * (i / 64) + (i % 64 - 56);
  const Expr<F> T = P.concat(H.constant(std::vector<Elt>{pf->zero()})).reindex(ti);
  assert_zero((fprev ^ 1) * (B + T), Name(name + ".padding.zeros"))
      .pin(Placement::kCircuit);
  // The digest is the chaining value after block nb - 1: for every block b,
  // sigma_b (digest + H'_b) = 0 bit by bit, H'_b in digest order (sigma is
  // one-hot), one degree-2 predicate over the committed bits of every
  // block, [N, 256], which placement batches with the blocks' relations.
  std::vector<size_t> at, row, bit;
  for (size_t bk = 0; bk < N; ++bk) {
    const auto order = si::digest_order(N, bk);
    for (size_t q = 0; q < 256; ++q) {
      at.push_back(order[q]);
      row.push_back(bk);
      bit.push_back(q);
    }
  }
  assert_zero(sigma.reindex(row) &
                  (Expr<F, Bit>(digest).reindex(bit) ^ h.reindex(at)),
              Name(name + ".padding.digest"));
  // The plan export: the buffer's blocks and bytes, the least block count
  // and the length field's bits (FIPS 180-4's 64-bit big-endian 8 L).
  internal::predicate_scope(internal::operand_graph(digest), Name(),
                            "sha256_varlen")
      .note("sha256-varlen", name,
            NoteValues{{"maxBlocks", __int128(N)},
                       {"minBlocks", __int128(min_blocks)},
                       {"bufferBytes", __int128(n)},
                       {"lengthBits", 64}},
            H);
  return digest;
}

}  // namespace proofs::gordiehowe::lib::sha256

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_SHA256_H_
