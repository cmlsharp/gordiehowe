// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: Keccak-f[1600], the SHAKE XOFs and SHA3-256 as functions over
// the core.
//
// The state has shape [5][5][64] (y, x, z): coordinate 64 (5 y + x) + z is
// bit z of lane (x, y), so its flat order is FIPS 202's byte order (state
// byte i is bits 8 i .. 8 i + 7), and a block of the rate is the state's
// first 8 rate bits. keccak_round is one round as an expression: theta, rho
// and pi are XORs, rotations and one index map (affine views), chi has
// degree 2 and iota adds a constant.
//
// keccak_f commits the state after every K-th round as H.priv(e) (D.priv,
// the compiler computes it), each an assert_equal of the rounds between: at
// K = 1 (what the sponges use) every equality has degree 2 and one shape,
// and placement merges every round of every call in the domain into one
// batch; at K = 6 (Longfellow's sliced form) an equality has degree 64, no
// batch admits it, and the rounds between are circuit wires. A committed
// state is a Bit value; the compiler stores its bits as the packing tree's
// words.
//
// A sponge absorbs a block into the first round's operands (the previous
// output plus the block), so no input state is committed and no circuit
// packs the message; its output is a view of the squeezing permutations'
// states.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_KECCAK_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_KECCAK_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::keccak {

// ------------------------------------------------------------ tables --

// rho's rotation of lane (x, y), FIPS 202.
inline constexpr unsigned kRho[5][5] = {{0, 36, 3, 41, 18},
                                         {1, 44, 10, 45, 2},
                                         {62, 6, 43, 15, 61},
                                         {28, 55, 25, 21, 56},
                                         {27, 20, 39, 8, 14}};
// iota's round constants RC[i], FIPS 202.
inline constexpr uint64_t kRoundConstants[24] = {
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008};
// The flat coordinate of bit (y, x, z).
constexpr size_t state_at(size_t y, size_t x, size_t z) {
  return (5 * y + x) * 64 + z;
}
// rho then pi as one index map of the state's shape: entry (y, x, z) of
// a[rho_pi()] is a.flat()[rho_pi()[y][x][z]], since pi's output lane (x, y)
// is rho's lane (x + 3 y, x).
using StateIndex = std::array<std::array<std::array<uint32_t, 64>, 5>, 5>;
inline const StateIndex &rho_pi() {
  static const StateIndex m = [] {
    StateIndex r{};
    for (size_t y = 0; y < 5; ++y)
      for (size_t x = 0; x < 5; ++x)
        for (size_t z = 0; z < 64; ++z) {
          const size_t xs = (x + 3 * y) % 5, ys = x;
          r[y][x][z] =
              uint32_t(state_at(ys, xs, (z + 64 - kRho[xs][ys]) % 64));
        }
    return r;
  }();
  return m;
}
// iota's constant of round I as bits of the state, nonzero in lane (0, 0).
using StateBits = std::array<std::array<std::array<uint8_t, 64>, 5>, 5>;
inline const StateBits &round_constant(size_t i) {
  static const std::array<StateBits, 24> rc = [] {
    std::array<StateBits, 24> r{};
    for (size_t t = 0; t < 24; ++t)
      for (size_t z = 0; z < 64; ++z)
        r[t][0][0][z] = uint8_t((kRoundConstants[t] >> z) & 1);
    return r;
  }();
  return rc.at(i % 24);
}

// Round I of Keccak-f on the state A, of shape [5][5][64].
template <class F>
Expr<F, Bit> keccak_round(Expr<F, Bit> a, size_t i) {
  // theta
  auto c = a.sum(0);
  a = a + c.rotate(1, 0) + c.rotate(-1, 0).rotate(1, 1);
  // rho, pi
  a = a[rho_pi()];
  // chi
  a = a + (~a.rotate(-1, 1) & a.rotate(-2, 1));
  // iota
  return a + round_constant(i);
}

// Round I of Keccak-f on the 25 lanes A (lane (x, y) at A[x + 5 y], bit z
// of the lane its bit z: the state's flat order in 64-bit words), FIPS 202
// section 3.2: the host function of the committed states (keccak_f), the
// same values as keccak_round's expression. No branch reads a lane.
inline void keccak_round_lanes(uint64_t *a, size_t i) {
  auto rotl = [](uint64_t v, unsigned r) {
    return r == 0 ? v : (v << r) | (v >> (64 - r));
  };
  // theta
  uint64_t c[5], d[5];
  for (size_t x = 0; x < 5; ++x)
    c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
  for (size_t x = 0; x < 5; ++x)
    d[x] = c[(x + 4) % 5] ^ rotl(c[(x + 1) % 5], 1);
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x) a[x + 5 * y] ^= d[x];
  // rho, pi: lane (x, y) rotated by kRho[x][y] to lane (y, 2 x + 3 y)
  uint64_t b[25];
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(a[x + 5 * y], kRho[x][y]);
  // chi
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      a[x + 5 * y] = b[x + 5 * y] ^
                     (~b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
  // iota
  a[0] ^= kRoundConstants[i % 24];
}

// Keccak-f of the state IN in domain H, the state after every K-th round
// committed (K divides 24) as H.priv(NAME.r<FIRST + j>, ...) for the j-th
// committed state. Returns the committed states. Each committed state's honest
// witness is computed on lanes (keccak_round_lanes, a HostStep) from the state
// before its rounds; its predicate is the rounds' expression.
template <class F>
std::vector<Ref<F, Bit, Committed>> keccak_f(Domain<F> &H,
                                             const std::string &name,
                                             Expr<F, Bit> in, size_t k = 1,
                                             size_t first = 0) {
  if (k == 0 || 24 % k != 0)
    fail("keccak_f '" + name + "': the period " + std::to_string(k) +
         " does not divide 24");
  std::vector<Ref<F, Bit, Committed>> states;
  Expr<F, Bit> x = in;
  for (size_t j = 0; j < 24 / k; ++j) {
    const Expr<F, Bit> before = x;
    for (size_t r = 0; r < k; ++r) x = keccak_round(x, j * k + r);
    HostStep<F> step;
    step.base = before.node;
    step.fn = [j, k](const uint64_t *in_lanes, uint64_t *out) {
      std::copy(in_lanes, in_lanes + 25, out);
      for (size_t r = 0; r < k; ++r) keccak_round_lanes(out, j * k + r);
    };
    states.push_back(
        H.priv(name + ".r" + std::to_string(first + j), x, step));
    x = states.back();
  }
  return states;
}

// ------------------------------------------------------------ messages --

// An XOF: its rate in bytes and its domain suffix (FIPS 202).
struct SpongeSpec {
  size_t rate;
  uint8_t suffix;
};
inline constexpr SpongeSpec kShake128{168, 0x1f};
inline constexpr SpongeSpec kShake256{136, 0x1f};
// SHA3-256 (FIPS 202 section 6.1): rate 136, suffix 01, a 32-byte digest.
inline constexpr SpongeSpec kSha3_256{136, 0x06};
inline constexpr size_t kSha3_256DigestBytes = 32;

// A sponge message over field F: Bit values of the hashing domain and
// constants, concatenated; bit 8 m + i is bit i of byte m.
template <class F>
using SpongeInput = Expr<F, Bit>;
// The number of bits of message MSG (0 for the empty message, a
// default-constructed SpongeInput).
template <class F>
size_t input_bits(const SpongeInput<F> &msg) {
  return msg.node ? msg.size() : 0;
}

// Constant bytes of a message (a domain separator, a length byte):
// constants of the first round's operands, so they cost no input.
struct ConstantBytes {
  std::vector<uint8_t> bytes;
};
inline ConstantBytes constant_bytes(std::vector<uint8_t> bytes) {
  return ConstantBytes{std::move(bytes)};
}
// The bits of constant bytes C in domain H, of shape SHAPE (flat by
// default; Shape{n, 8} gives a row per byte).
template <class F>
Expr<F, Bit> constant_input(const Domain<F> &H, const ConstantBytes &c,
                            Shape shape = Shape()) {
  std::vector<uint64_t> b;
  for (uint8_t byte : c.bytes)
    for (size_t i = 0; i < 8; ++i) b.push_back((byte >> i) & 1);
  return H.constant(Bit{}, b, std::move(shape));
}

namespace keccak_internal {
// The field of the first value among X...
template <class... X>
struct InputField {
  using type = void;
};
template <class F, class T, class P, class... X>
struct InputField<Ref<F, T, P>, X...> {
  using type = F;
};
template <class F, class T, class... X>
struct InputField<Expr<F, T>, X...> {
  using type = F;
};
template <class X, class... Rest>
struct InputField<X, Rest...> : InputField<Rest...> {};
// Part X of a message as flat bits (a constant's in domain H).
template <class F, class T, class P>
Expr<F, Bit> part_bits(const Domain<F> &, const Ref<F, T, P> &r) {
  static_assert(is_bit_v<T> || is_any_type_v<T>,
                "sponge_input: a value part is a Bit value");
  if constexpr (is_bit_v<T>) return Expr<F, Bit>(r).flat();
  return Expr<F, Bit>(Expr<F>(r).node).flat();
}
template <class F, class T>
Expr<F, Bit> part_bits(const Domain<F> &, const Expr<F, T> &e) {
  static_assert(is_bit_v<T>, "sponge_input: a value part is a Bit value");
  return e.node ? Expr<F, Bit>(e.flat()) : e;
}
template <class F>
Expr<F, Bit> part_bits(const Domain<F> &H, const ConstantBytes &c) {
  return constant_input(H, c);
}
// The domain of field F of the system of the first value among X... that
// reads one (null when none does).
template <class F>
Domain<F> *domain_of() {
  return nullptr;
}
template <class F, class X, class... R>
Domain<F> *domain_of(const X &x, const R &...r) {
  if constexpr (std::is_same_v<X, ConstantBytes>) {
    return domain_of<F>(r...);
  } else {
    const ExprPtr<F> e = expr_node(x);
    Graph *g = e ? graph_of(e) : nullptr;
    if (g == nullptr) return domain_of<F>(r...);
    return g->system->template domain_of<F>();
  }
}
}  // namespace keccak_internal

// The message PARTS... in order: Bit values of one field, messages (an
// empty one adds nothing) and constant_bytes(...), at least one of them a
// value that is not empty.
template <class... X>
auto sponge_input(const X &...parts) {
  using F = typename keccak_internal::InputField<X...>::type;
  static_assert(!std::is_void_v<F>,
                "sponge_input: the parts are Bit values and "
                "constant_bytes(...), at least one of them a value");
  const Domain<F> *H = keccak_internal::domain_of<F>(parts...);
  if (H == nullptr) fail("sponge_input: no part is a value of a domain");
  std::optional<Expr<F, Bit>> out;
  for (const Expr<F, Bit> &x : {keccak_internal::part_bits(*H, parts)...}) {
    if (!x.node) continue;
    out = out ? Expr<F, Bit>(out->concat(x)) : x;
  }
  return *out;
}
// The bits of message MSG, flat (sha256.h reads its messages this way).
template <class F>
Expr<F, Bit> message_bits(const Domain<F> &, const SpongeInput<F> &msg) {
  return msg.flat();
}

// ------------------------------------------------------------ sponges --

// A batch of sponge calls in domain H: a scope for their names. Placement
// merges the calls' round predicates (of one shape) into one batch.
template <class F>
class SpongeBatch {
 public:
  SpongeBatch(Domain<F> &d, std::string name,
              std::function<std::string(const std::string &)> scoped)
      : d_(&d), name_(std::move(name)), scoped_(std::move(scoped)) {}
  Domain<F> &domain() const { return *d_; }
  const std::string &name() const { return name_; }
  // A call's name in the batch's scope.
  std::string scoped(const std::string &nm) const { return scoped_(nm); }
  // The same batch whose calls take their names in the scope of H (a
  // ScopedDomain of the batch's domain).
  template <class SD>
  SpongeBatch rescoped(const SD &H) const {
    if (&H.domain() != d_)
      fail("Keccak batch '" + name_ + "': rescoped to another domain");
    SpongeBatch c = *this;
    c.scoped_ = [H](const std::string &nm) { return H.scoped(nm); };
    return c;
  }

 private:
  Domain<F> *d_;
  std::string name_;
  std::function<std::string(const std::string &)> scoped_;
};

// A Keccak batch in H named NAME.
template <class F>
SpongeBatch<F> keccak_batch(Domain<F> &H, const std::string &name) {
  return SpongeBatch<F>(H, name, [](const std::string &nm) { return nm; });
}
// The same through a scope: the batch's and its calls' names carry its
// prefix.
template <class F>
SpongeBatch<F> keccak_batch(const ScopedDomain<F> &H, const std::string &name) {
  return SpongeBatch<F>(H.domain(), H.scoped(name),
                        [H](const std::string &nm) { return H.scoped(nm); });
}

// One sponge call inside domain H: every permutation's round states, and
// the squeezed output, a view of them.
template <class F>
struct SpongeCall {
  // Round r of permutation p is states[24 p + r], NAME.r<24 p + r>.
  std::vector<Ref<F, Bit, Committed>> states;
  Ref<F, Bit, Committed> out;
  size_t msg_bytes = 0, out_bytes = 0, blocks = 0, perms = 0;
  size_t rate = kShake256.rate;
  // Permutation P's output state.
  const Ref<F, Bit, Committed> &after(size_t p) const {
    return states.at(24 * p + 23);
  }
};
template <class F>
using Shake256 = SpongeCall<F>;

// Adds SPEC(MSG) squeezed to OUT_BYTES to batch B as the call NM. RAW: the
// message is whole padded blocks, one permutation each, no squeeze. WHAT
// names the gadget in errors.
template <class F>
SpongeCall<F> sponge(const SpongeBatch<F> &b, const std::string &nm,
                     const SpongeSpec &spec, const SpongeInput<F> &msg,
                     size_t out_bytes, const std::string &what,
                     bool raw = false) {
  Domain<F> &H = b.domain();
  const std::string name = b.scoped(nm);
  const size_t rate = spec.rate;
  if (rate % 8 != 0 || rate >= 200)
    fail(what + " '" + name + "': the rate is not whole lanes");
  if (msg.size() % 8 != 0 || (raw ? out_bytes != 0 : out_bytes == 0))
    fail(what + " '" + name + "': the message is not whole bytes");
  SpongeCall<F> sh;
  sh.rate = rate;
  sh.msg_bytes = msg.size() / 8;
  sh.out_bytes = out_bytes;
  if (raw && (sh.msg_bytes == 0 || sh.msg_bytes % rate != 0))
    fail(what + " '" + name + "': the blocks are not whole");
  sh.blocks = raw ? sh.msg_bytes / rate : sh.msg_bytes / rate + 1;
  sh.perms = raw ? sh.blocks : sh.blocks + (out_bytes + rate - 1) / rate - 1;
  // The padded message (pad10*1 after the suffix), and its blocks.
  std::vector<uint8_t> pad(sh.blocks * rate - sh.msg_bytes, 0);
  if (!raw) {
    pad.front() = spec.suffix;
    pad.back() ^= 0x80;
  }
  const Expr<F, Bit> padded =
      pad.empty() ? msg.flat()
                  : Expr<F, Bit>(msg.flat().concat(
                        constant_input(H, constant_bytes(pad))));
  const Expr<F, Bit> capacity =
      constant_input(H, constant_bytes(std::vector<uint8_t>(200 - rate, 0)));
  // Each permutation: absorb a block into the previous output, then the
  // rounds.
  std::optional<Expr<F, Bit>> state;
  for (size_t p = 0; p < sh.perms; ++p) {
    std::optional<Expr<F, Bit>> in = state;
    if (p < sh.blocks) {
      const Expr<F, Bit> block =
          padded.slice(8 * rate * p, 8 * rate * (p + 1)).concat(capacity);
      in = state ? Expr<F, Bit>(*state + block) : block;
    }
    const auto s = keccak_f(H, name, in->reshape(Shape{5, 5, 64}), 1, 24 * p);
    sh.states.insert(sh.states.end(), s.begin(), s.end());
    state = Expr<F, Bit>(s.back()).flat();
  }
  if (raw) return sh;
  // Output byte o: byte o mod rate of permutation blocks - 1 + o / rate. A
  // permutation's output bytes are a bit view of its state's first words
  // alone (when the state is stored as words), so a circuit that reads the
  // output reads those words.
  const bool one = out_bytes <= rate && out_bytes % 2 == 0;
  std::vector<Ref<F, Bit, Committed>> outs;
  std::vector<Coord> at;
  for (size_t p = sh.blocks - 1, o = 0; o < out_bytes; ++p) {
    const size_t take = std::min(rate, out_bytes - o);
    Ref<F, Bit, Committed> part = sh.after(p);
    if (const auto words = H.words_of(part)) {
      std::vector<size_t> select((8 * take + 15) / 16);
      for (size_t q = 0; q < select.size(); ++q) select[q] = q;
      part = H.bits(one ? name + ".out" : name + ".out.p" + std::to_string(p),
                    *words, std::move(select));
    }
    for (size_t i = 0; i < 8 * take; ++i) at.push_back({outs.size(), i});
    outs.push_back(part);
    o += take;
  }
  sh.out = one && outs[0].n == at.size()
               ? outs[0]
               : gather(outs, at).named(name + ".out");
  return sh;
}
// SHAKE256(MSG) and SHAKE128(MSG) squeezed to OUT_BYTES, added to batch B.
template <class F>
SpongeCall<F> shake256(const SpongeBatch<F> &b, const std::string &nm,
                       const SpongeInput<F> &msg, size_t out_bytes) {
  return sponge(b, nm, kShake256, msg, out_bytes, "shake256");
}
template <class F>
SpongeCall<F> shake128(const SpongeBatch<F> &b, const std::string &nm,
                       const SpongeInput<F> &msg, size_t out_bytes) {
  return sponge(b, nm, kShake128, msg, out_bytes, "shake128");
}
// SHA3-256(MSG), added to batch B: its out is the 32-byte digest.
template <class F>
SpongeCall<F> sha3_256(const SpongeBatch<F> &b, const std::string &nm,
                       const SpongeInput<F> &msg) {
  return sponge(b, nm, kSha3_256, msg, kSha3_256DigestBytes, "sha3_256");
}
// A message of one Bit value.
template <class F, class T, class P>
SpongeCall<F> shake256(const SpongeBatch<F> &b, const std::string &nm,
                       Ref<F, T, P> msg, size_t out_bytes) {
  return shake256(b, nm, sponge_input(msg), out_bytes);
}

// SHAKE256(MSG) squeezed to OUT_BYTES in a batch of its own, named
// NAME.keccak. MSG holds the message bits, bit i of byte k at index 8k + i:
// a Bit value of H or a message.
template <class F, class M>
SpongeCall<F> shake256(Domain<F> &H, const std::string &name, const M &msg,
                       size_t out_bytes) {
  static_assert(IsRef<M>::value || std::is_same_v<M, SpongeInput<F>>,
                "shake256: the message is a Bit value or a message");
  if constexpr (IsRef<M>::value) {
    return shake256(H, name, sponge_input(msg), out_bytes);
  } else {
    return shake256(keccak_batch(H, name + ".keccak"), name, msg, out_bytes);
  }
}
// The same through a scope: the names carry its prefix.
template <class F, class M>
SpongeCall<F> shake256(const ScopedDomain<F> &H, const std::string &name,
                       const M &msg, size_t out_bytes) {
  return shake256(H.domain(), H.scoped(name), msg, out_bytes);
}

// ------------------------------------------------------ private length --

// SPEC(M) squeezed to OUT_BYTES, for a message M of private length L in a
// buffer BUF of N = |BUF| / rate whole blocks, added to batch B: the sponge
// counterpart of sha256_varlen (sha256.h). BUF holds the message,
// its pad10*1 padding with SPEC's suffix, and zeros after them; IN_MESSAGE
// is a Bit per buffer byte, f_i = [i < L]. All N blocks are absorbed (one
// permutation each, sponge's raw mode) and predicates NAME.padding.* in GKR
// check, with f_{-1} = 1, B_i the GF(2^16) value of buffer
// byte i, g_i = f_{i-1} + f_i and z_i = 1 + f_{i-1} = [i > L]:
//   monotone   f_i (1 + f_{i-1}) = 0 for i >= 1, f_{MAX_BYTES} = 0 (L <=
//              MAX_BYTES < n, n - 1 by default) and f_{MIN_BYTES - 1} = 1
//              (L >= MIN_BYTES); g is one-hot at L;
//   blocks     G_0 = 1, G_b = f_{rate b - 1} = [L >= rate b] (0 < b < N),
//              G_N = 0, and sigma_b = G_b + G_{b+1} = [b = floor(L / rate)],
//              one-hot: the padded message has nb = floor(L / rate) + 1
//              blocks;
//   padding    at offset o < rate - 1 of a block: g_i (B_i + suffix) = 0 and
//              z_i B_i = 0; at offset rate - 1 of block b: g_i (B_i + suffix
//              + 0x80) = 0 and z_i (B_i + sigma_b 0x80) = 0;
//   output     sigma_b (out + O_b) = 0 bit by bit for every block b, O_b the
//              first OUT_BYTES bytes of the output of permutation b (the
//              absorb of blocks 0..b): one degree-2 predicate over every
//              block, which placement batches with the rounds.
// An output longer than the rate (Falcon's HashToPoint) selects the whole
// state the same way: NAME.state, Bit [1600], with sigma_b (state + S_b) =
// 0 for S_b the state after permutation b. The squeeze's
// ceil(OUT_BYTES / rate) - 1 permutations start from it (keccak_f, every
// round committed as NAME.squeeze.r<j>), and the output is its first rate
// bytes, then each squeeze permutation's.
// Soundness: the constraints hold exactly when blocks 0..nb - 1 of BUF are
// FIPS 202's padding of M = B_0..B_{L-1} (pad10*1 after the suffix, the
// suffix and 0x80 sharing the last byte when L = rate nb - 1) and every
// later byte is zero, and the output is the state after block nb - 1,
// which the Keccak relation makes the sponge's first squeezed block of
// SPEC(M). Every block is permuted whether or not it is used, as
// sha256_varlen hashes every block. The output (or the selected state) is
// advice: permutation nb - 1's output bytes (state), read by a masked scan
// over the blocks' states. The plan export notes the buffer's blocks, the
// length bounds, the rate and the output length (gadget record
// "sponge-varlen"). Returns the output, Bit [8 OUT_BYTES], bit 8 k + i of
// byte k.
template <class F, class PF>
Ref<F, Bit, Committed> sponge_varlen(const SpongeBatch<F> &b,
                                     const std::string &nm,
                                     const SpongeSpec &spec,
                                     const SpongeInput<F> &buf,
                                     Ref<F, Bit, PF> in_message,
                                     size_t out_bytes, size_t min_bytes = 1,
                                     size_t max_bytes = 0) {
  using Elt = typename F::Elt;
  const std::string name = b.scoped(nm);
  const std::string what = "sponge_varlen '" + name + "'";
  Domain<F> &H = b.domain();
  const size_t rate = spec.rate;
  const size_t nbits = buf.size();
  if (nbits == 0 || nbits % (8 * rate) != 0)
    fail(what + ": the buffer is not a whole number of blocks");
  const size_t n = nbits / 8, N = n / rate;
  if (in_message.n != n)
    fail(what + ": " + std::to_string(in_message.n) + " flags for " +
         std::to_string(n) + " bytes");
  if (out_bytes == 0) fail(what + ": an empty output");
  // An output past the rate squeezes from the selected state.
  const bool squeeze = out_bytes > rate;
  if (max_bytes == 0) max_bytes = n - 1;
  if (max_bytes >= n)
    fail(what + ": max_bytes outside 1.." + std::to_string(n - 1));
  if (min_bytes < 1 || min_bytes > max_bytes)
    fail(what + ": min_bytes outside 1.." + std::to_string(max_bytes));
  const SpongeCall<F> call =
      sponge(b, nm + ".blocks", spec, buf, 0, what, /*raw=*/true);
  const F *pf = &H.field();

  // The first OUT_BYTES bytes of each permutation's output, or its whole
  // state when the output squeezes on, [N, 8 sel_bytes].
  const size_t sel_bytes = squeeze ? 200 : out_bytes;
  std::vector<Ref<F, Bit, Committed>> afters;
  for (size_t bk = 0; bk < N; ++bk) afters.push_back(call.after(bk));
  std::vector<Coord> at;
  for (size_t bk = 0; bk < N; ++bk)
    for (size_t i = 0; i < 8 * sel_bytes; ++i) at.push_back({bk, i});
  const auto outs = gather(afters, at, Shape{N, 8 * sel_bytes})
                        .named(name + ".outputs");

  const size_t ob = 8 * sel_bytes;
  const auto out = H.priv(
      Bit{}, name + (squeeze ? ".state" : ".out"), Shape(ob),
      depends_on(outs, in_message),
      [pf, n, N, ob, rate](const std::vector<Elt> &o,
                           const std::vector<Elt> &flags) {
        const F &f = *pf;
        // No branch on the states or the flags: a count, then a masked scan
        // over the blocks' outputs.
        uint64_t len = 0;
        for (size_t i = 0; i < n; ++i) len += ct::bit_of(f, flags[i]);
        const uint64_t last = len / rate;
        std::vector<Elt> r(ob, f.zero());
        for (size_t j = 0; j < N; ++j) {
          const uint64_t mk = ct::mask(ct::eq(j, last));
          for (size_t q = 0; q < ob; ++q)
            r[q] = ct::select(mk, o[ob * j + q], r[q]);
        }
        return r;
      });

  // The padding's predicates (above), over the buffer's byte values and the
  // flags, each pinned to the GKR circuit.
  const Expr<F, Bit> bbits = buf.flat();
  const Expr<F, Bit> fw = in_message;
  const auto one = H.constant(Bit{}, std::vector<uint64_t>{1});
  const auto zero = H.constant(Bit{}, std::vector<uint64_t>{0});
  std::vector<Elt> beta8(8);
  for (size_t c = 0; c < 8; ++c) beta8[c] = pf->beta(c);
  // Byte values: sum_t beta_t bit_t.
  const Expr<F> B = (Expr<F>(bbits.reshape({n, 8})) * H.constant(beta8)).sum(1);
  const Expr<F, Bit> fprev = one.concat(fw.slice(0, n - 1));
  assert_zero(fw.slice(1, n) & (fw.slice(0, n - 1) ^ 1),
              Name(name + ".padding.monotone"))
      .pin(Placement::kCircuit);
  assert_zero(fw.slice(max_bytes, max_bytes + 1), Name(name + ".padding.max"))
      .pin(Placement::kCircuit);
  assert_zero(fw.slice(min_bytes - 1, min_bytes) ^ 1,
              Name(name + ".padding.min"))
      .pin(Placement::kCircuit);
  std::vector<size_t> gi;
  for (size_t bk = 1; bk < N; ++bk) gi.push_back(rate * bk - 1);
  const Expr<F, Bit> G =
      N > 1 ? Expr<F, Bit>(one.concat(fw.reindex(gi)).concat(zero))
            : Expr<F, Bit>(one.concat(zero));
  const Expr<F, Bit> sigma = G.slice(0, N) ^ G.slice(1, N + 1);
  const Expr<F, Bit> g = fprev ^ fw;
  // At offset o < rate - 1: g (B + suffix) = 0 and z B = 0; at offset rate
  // - 1 of block b: g (B + suffix + 0x80) = 0 and z (B + sigma_b 0x80) = 0.
  std::vector<Elt> want(n), last(n);
  std::vector<size_t> bi(n);
  for (size_t i = 0; i < n; ++i) {
    const bool end = i % rate == rate - 1;
    want[i] = pf->of_scalar(end ? spec.suffix ^ 0x80 : spec.suffix);
    last[i] = end ? pf->of_scalar(0x80) : pf->zero();
    bi[i] = i / rate;
  }
  assert_zero(g * (B + H.constant(want)), Name(name + ".padding.suffix"))
      .pin(Placement::kCircuit);
  assert_zero(
      (fprev ^ 1) * (B + Expr<F>(sigma.reindex(bi)) * H.constant(last)),
      Name(name + ".padding.zeros"))
      .pin(Placement::kCircuit);
  // The output: sigma_b (out + O_b) = 0 for every block b and output bit.
  std::vector<size_t> row, col;
  for (size_t bk = 0; bk < N; ++bk)
    for (size_t q = 0; q < ob; ++q) {
      row.push_back(bk);
      col.push_back(q);
    }
  assert_zero(sigma.reindex(row) &
                  (Expr<F, Bit>(out).reindex(col) ^ Expr<F, Bit>(outs).flat()),
              Name(name + ".padding.output"));
  internal::predicate_scope(internal::operand_graph(out), Name(),
                            "sponge_varlen")
      .note("sponge-varlen", name,
            NoteValues{{"maxBlocks", __int128(N)},
                       {"bufferBytes", __int128(n)},
                       {"minBytes", __int128(min_bytes)},
                       {"maxBytes", __int128(max_bytes)},
                       {"rate", __int128(rate)},
                       {"outBytes", __int128(out_bytes)}},
            H);
  if (!squeeze) return out;
  // The squeeze from the selected state: squeeze permutation p's output
  // bytes (NAME.out.p<p + 1>, a bit view of its state's first words, as
  // sponge's) follow the state's first rate bytes.
  const size_t perms = (out_bytes + rate - 1) / rate - 1;
  std::vector<Ref<F, Bit, Committed>> parts = {out};
  std::vector<Coord> oat;
  for (size_t i = 0; i < 8 * rate; ++i) oat.push_back({0, i});
  Expr<F, Bit> x = Expr<F, Bit>(out).reshape(Shape{5, 5, 64});
  for (size_t p = 0, o = rate; p < perms; ++p) {
    const auto st = keccak_f(H, name + ".squeeze", x, 1, 24 * p);
    x = st.back();
    const size_t take = std::min(rate, out_bytes - o);
    Ref<F, Bit, Committed> part = st.back();
    if (const auto words = H.words_of(part)) {
      std::vector<size_t> select((8 * take + 15) / 16);
      for (size_t q = 0; q < select.size(); ++q) select[q] = q;
      part = H.bits(name + ".out.p" + std::to_string(p + 1), *words,
                    std::move(select));
    }
    for (size_t i = 0; i < 8 * take; ++i) oat.push_back({parts.size(), i});
    parts.push_back(part);
    o += take;
  }
  return gather(parts, oat).named(name + ".out");
}
// SHAKE256 of a message of private length (sponge_varlen).
template <class F, class PF>
Ref<F, Bit, Committed> shake256_varlen(const SpongeBatch<F> &b,
                                       const std::string &nm,
                                       const SpongeInput<F> &buf,
                                       Ref<F, Bit, PF> in_message,
                                       size_t out_bytes, size_t min_bytes = 1,
                                       size_t max_bytes = 0) {
  return sponge_varlen(b, nm, kShake256, buf, in_message, out_bytes,
                       min_bytes, max_bytes);
}

}  // namespace proofs::gordiehowe::lib::keccak

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_KECCAK_H_
