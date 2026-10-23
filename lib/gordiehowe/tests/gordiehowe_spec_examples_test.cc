// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: worked example programs of the relation language as tests.
//
// Each example is the text of a marked region of this file, between the
// comments "spec listing <name>" and "end of spec listing <name>". An
// example split over several regions of one name (declarations at
// namespace scope, then lines of a function body) is their text joined by
// a blank line, each region without its common indentation.
//
// Around each example the test supplies the context the example leaves
// out (the profiles, the inputs' values) and checks claims about the
// compiled system and a proof.
//
// The domains: H over GF(2^128) with
// evaluation subfield GF(2^16), A over F_q^11 with q = 8380417, at the
// protocol hash SHA-384 (ConstraintSystem<SHA384, Fields...>).

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

#include "algebra/fp_native_wide.h"
#include "algebra/reed_solomon_extension_n.h"
#include "gordiehowe/examples/shared/keccak_host.h"
#include "circuits/tests/pq/ml_dsa/ml_dsa_shared.h"
#include "params/param_sets.h"
#include "gf2k/gf2_128.h"
#include "gf2k/lch14_reed_solomon.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/gordiehowe.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/lib/windows.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/operators.h"
#include "random/secure_random_engine.h"
#include "gtest/gtest.h"

namespace proofs::gordiehowe {
namespace {

// The listings name the operators (PolyMatVec, NegacyclicConv, Form)
// unqualified, as an example that uses gh::ops would.
using namespace ::proofs::gordiehowe::ops;

// ------------------------------------------------------------- fields --

using HF = GF2_128<>;
using AF = MlDsaField11;
using HElt = HF::Elt;
using AElt = AF::Elt;
using RSH = LCH14ReedSolomonFactory<HF>;
using RSA = ReedSolomonExtensionNFactory<AF>;
using Sys = ConstraintSystem<SHA384, HF, AF>;
using Assignment = Sys::Assignment;
using MacShape = param_sets::ROMParams::Mac;

constexpr uint64_t kQ = 8380417;

// The fields and their Reed-Solomon factories, shared by every system.
struct Env {
  HF hf;
  AF af{ml_dsa::Fq(), AF::beta_};
  RSH rsh{hf};
  RSA rsa{ml_dsa::Fq(), OptimizationOptions::optimized()};
};
const Env &env() {
  static const Env *e = new Env;
  return *e;
}

// The binary domain: GF(2^128), its prime field GF(2), with the measured
// placement rates of its field.
DomainProfile<HF, RSH, SHA384> spec_binary_profile() {
  DomainProfile<HF, RSH, SHA384> p;
  p.f = &env().hf;
  p.rsf = &env().rsh;
  p.field_name = "GF(2^128)";
  p.rate = 4;
  p.nreq = 64;
  p.has_subfield = true;
  p.prime = Space::kPrime;
  p.rates = param_sets::placement_rates<HF>();
  return p;
}
// The odd domain: F_q^11, its prime field the evaluation subfield F_q.
DomainProfile<AF, RSA, SHA384> spec_odd_profile() {
  DomainProfile<AF, RSA, SHA384> p;
  p.f = &env().af;
  p.rsf = &env().rsa;
  p.field_name = "F_q^11";
  p.rate = 4;
  p.nreq = 64;
  p.has_subfield = true;
  p.prime = Space::kSubfield;
  p.rates = param_sets::placement_rates<AF>();
  return p;
}
// The compile profile: the MAC basis of GF(2^128).
CompileProfile spec_compile_profile() {
  CompileProfile c;
  c.name = "spec-examples";
  MacBasis b;
  b.w = MacShape::kBits;
  for (auto t : MacShape::kTaps) b.taps.push_back(unsigned(t));
  c.mac_bases = {b};
  return c;
}

// The profiles the listings name.
const DomainProfile<HF, RSH, SHA384> binary_profile = spec_binary_profile();
const DomainProfile<AF, RSA, SHA384> odd_profile = spec_odd_profile();

// ------------------------------------------------------ report helpers --

bool has(const std::string &report, const std::string &s) {
  return report.find(s) != std::string::npos;
}
// The number of report lines that start with PREFIX after their indent.
size_t count_lines(const std::string &report, const std::string &prefix) {
  size_t k = 0;
  size_t at = 0;
  while (at < report.size()) {
    size_t end = report.find('\n', at);
    if (end == std::string::npos) end = report.size();
    const std::string line = report.substr(at, end - at);
    const size_t text = line.find_first_not_of(' ');
    k += text != std::string::npos &&
         line.compare(text, prefix.size(), prefix) == 0;
    at = end + 1;
  }
  return k;
}
// The placement target of predicate NAME ("affine rows", "circuit", "field
// batch", "quadratic triples"), from its line
// "assert_zero 'NAME' n=<n>: <target> (<why>)" in the section of domain
// DOMAIN (the k-th domain is domain<k>; predicates are numbered per
// domain).
std::string placement_of(const std::string &report, const std::string &name,
                         const std::string &domain = "domain0") {
  const size_t section = report.find("domain " + domain + " (");
  if (section == std::string::npos) return "";
  const std::string key = "'" + name + "' n=";
  const size_t at = report.find(key, section);
  if (at == std::string::npos) return "";
  const size_t colon = report.find(": ", at);
  const size_t open = report.find(" (", colon);
  return report.substr(colon + 2, open - colon - 2);
}
// The phase of the one challenge whose name contains PART.
template <class C>
size_t challenge_phase(const C &c, const std::string &part) {
  size_t found = SIZE_MAX;
  size_t count = 0;
  for (size_t id = 0; id < c.nodes().size(); ++id) {
    const Node &nd = c.nodes()[id];
    const bool hit = nd.kind == Kind::kChallenge &&
                     nd.name.find(part) != std::string::npos;
    count += hit;
    found = hit ? id : found;
  }
  EXPECT_EQ(count, 1u) << "challenges named *" << part << "*";
  return found == SIZE_MAX ? SIZE_MAX : c.phase(found);
}
// The degree bound recorded for the challenge node ID, 0 when none is.
template <class C>
Bound charge_of(const C &c, size_t id) {
  const std::string &name = c.nodes().at(id).name;
  Bound d = 0;
  for (const auto &ch : c.records().charges)
    d = ch.label == name ? ch.degree : d;
  return d;
}
// The one node of the compiled system C that PRED accepts (WHAT names it
// in the failure).
template <class C, class P>
size_t node_where(const C &c, P pred, const std::string &what) {
  size_t found = SIZE_MAX;
  size_t count = 0;
  for (size_t id = 0; id < c.nodes().size(); ++id) {
    const bool hit = pred(c.nodes()[id]);
    count += hit;
    found = hit ? id : found;
  }
  EXPECT_EQ(count, 1u) << "nodes " << what;
  return found;
}
// The node named NAME.
template <class C>
size_t node_named(const C &c, const std::string &name) {
  return node_where(
      c, [&](const Node &n) { return n.name == name; }, "named " + name);
}
// The one node whose automatic name is PREFIX and a number (a value the
// listing does not name: "priv", "challenge.") and which has N
// coordinates.
template <class C>
size_t node_auto(const C &c, const std::string &prefix, size_t n) {
  return node_where(
      c,
      [&](const Node &nd) {
        const std::string &m = nd.name;
        return nd.n == n && m.size() > prefix.size() &&
               m.compare(0, prefix.size(), prefix) == 0 &&
               m.find_first_not_of("0123456789", prefix.size()) ==
                   std::string::npos;
      },
      prefix + "* of " + std::to_string(n));
}

// The field object of F.
template <class F>
const F &field_of() {
  if constexpr (std::is_same_v<F, HF>)
    return env().hf;
  else
    return env().af;
}
// A tamper of the advice values: adds 1 to coordinate K of node ID.
using Tamper = std::function<void(size_t, Sys::Value &)>;
template <class F>
Tamper bump(size_t id, size_t k) {
  return [id, k](size_t at, Sys::Value &v) {
    // The node is public data of the test, not a witness value.
    if (at != id) return;
    const F &f = field_of<F>();
    auto &x = Sys::Set::template get<F>(v);
    f.add(x.at(k), f.one());
  };
}
// The node that commits node ID's values: its words (NAME.words) when the
// compiler stores a computed Bit value as words, ID itself otherwise.
size_t stored_node(const std::vector<Node> &N, size_t id) {
  const std::string w = N.at(id).name + ".words";
  for (size_t k = 0; k < N.size(); ++k)
    if (N[k].name == w) return k;
  return id;
}
template <class R>
size_t stored(const R &r) {
  return stored_node(r.g->nodes, r.id);
}
// V with 1 added to coordinate K: a wrong private input.
template <class F>
std::vector<typename F::Elt> bumped(std::vector<typename F::Elt> v, size_t k) {
  field_of<F>().add(v.at(k), field_of<F>().one());
  return v;
}
// Proves W against the prepared statement ST and verifies. A cheating
// prover (a TAMPER of its advice, or CHEATING: a wrong private input)
// proves without the satisfaction check; a refused proof is a rejection.
template <class C, class A>
bool proves(const C &c, const A &st, const A &w, Tamper tamper = nullptr,
            bool cheating = false) {
  auto prep = c.prepare(st);
  typename C::ProveOptions opt;
  opt.require_satisfied = tamper == nullptr && !cheating;
  opt.tamper = tamper;
  SecureRandomEngine rng;
  try {
    return prep.verify(prep.prove(w, rng, opt));
  } catch (const std::runtime_error &) {
    return false;
  }
}

// ---------------------------------------------------------- host Keccak --
// Keccak-f[1600] (FIPS 202) on 25 lanes, lane (x, y) at index x + 5 y, and
// the index maps of the relation. A state's bit (y, x, z) is coordinate
// (5 y + x) 64 + z of a value of shape [5][5][64]: bit z of lane (x, y).

constexpr std::array<uint64_t, 24> kRc = {
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808Aull,
    0x8000000080008000ull, 0x000000000000808Bull, 0x0000000080000001ull,
    0x8000000080008081ull, 0x8000000000008009ull, 0x000000000000008Aull,
    0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000Aull,
    0x000000008000808Bull, 0x800000000000008Bull, 0x8000000000008089ull,
    0x8000000000008003ull, 0x8000000000008002ull, 0x8000000000000080ull,
    0x000000000000800Aull, 0x800000008000000Aull, 0x8000000080008081ull,
    0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull};
// rho's rotation of lane (x, y): kRot[x][y].
constexpr int kRot[5][5] = {{0, 36, 3, 41, 18},
                            {1, 44, 10, 45, 2},
                            {62, 6, 43, 15, 61},
                            {28, 55, 25, 21, 56},
                            {27, 20, 39, 8, 14}};

using Lanes = std::array<uint64_t, 25>;

uint64_t rotl(uint64_t v, int r) {
  return r == 0 ? v : (v << r) | (v >> (64 - r));
}
// Round I of Keccak-f on A.
Lanes keccak_round_host(const Lanes &a, size_t i) {
  std::array<uint64_t, 5> c{};
  for (size_t x = 0; x < 5; ++x)
    c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
  Lanes t{};
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      t[x + 5 * y] = a[x + 5 * y] ^ c[(x + 4) % 5] ^ rotl(c[(x + 1) % 5], 1);
  Lanes b{};
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      b[y + 5 * ((2 * x + 3 * y) % 5)] = rotl(t[x + 5 * y], kRot[x][y]);
  Lanes out{};
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      out[x + 5 * y] =
          b[x + 5 * y] ^ (~b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
  out[0] ^= kRc[i];
  return out;
}

// The flat coordinate of bit (y, x, z).
constexpr size_t at3(size_t y, size_t x, size_t z) {
  return (5 * y + x) * 64 + z;
}

// A state of shape [5][5][64] as C++ nested arrays (a lifted constant).
using StateBits = std::array<std::array<std::array<uint8_t, 64>, 5>, 5>;
// The map of rho and pi as one index array of shape [5][5][64]: coordinate
// (y, x, z) of pi(rho(a)) is a.flat()[kRhoPi[y][x][z]], since pi's output
// lane (x, y) is rho's lane (x + 3 y, x), rotated by its offset.
//
// A flat index array std::array<uint32_t, 1600> would give a[kRhoPi] the
// shape [1600], on which chi's rotate(-1, 1) has no axis 1. An index array
// of shape [5][5][64] keeps a[kRhoPi] a state.
using StateIndex = std::array<std::array<std::array<uint32_t, 64>, 5>, 5>;
StateIndex make_rho_pi() {
  StateIndex m{};
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      for (size_t z = 0; z < 64; ++z) {
        const size_t xs = (x + 3 * y) % 5;
        const size_t ys = x;
        m[y][x][z] =
            uint32_t(at3(ys, xs, (z + 64 - size_t(kRot[xs][ys])) % 64));
      }
  return m;
}
const StateIndex kRhoPi = make_rho_pi();
// iota's constant of round i as a state: lane (0, 0) holds RC_i.
struct RoundConstants {
  uint8_t c[24][5][5][64];
};
const RoundConstants &round_constants() {
  static const RoundConstants *rc = [] {
    auto *r = new RoundConstants{};
    for (size_t i = 0; i < 24; ++i)
      for (size_t z = 0; z < 64; ++z)
        r->c[i][0][0][z] = uint8_t((kRc[i] >> z) & 1);
    return r;
  }();
  return *rc;
}
// round i's constant RC[i] as bits of the state, nonzero only in lane (0, 0)
const uint8_t (&kRoundConstant)[24][5][5][64] = round_constants().c;

// A state's bits as elements of F, and back.
template <class F>
std::vector<typename F::Elt> lanes_bits(const F &f, const Lanes &a) {
  std::vector<typename F::Elt> v(1600);
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      for (size_t z = 0; z < 64; ++z)
        v[at3(y, x, z)] = ct::bit_elt(f, a[x + 5 * y] >> z);
  return v;
}
template <class F>
Lanes bits_lanes(const F &f, const typename F::Elt *v) {
  Lanes a{};
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      for (size_t z = 0; z < 64; ++z)
        a[x + 5 * y] |= ct::bit_of(f, v[at3(y, x, z)]) << z;
  return a;
}
// Bytes as bits, bit 8 k + i the bit i of byte k.
template <class F>
std::vector<typename F::Elt> bytes_bits(const F &f,
                                        const std::vector<uint8_t> &b) {
  std::vector<typename F::Elt> v(8 * b.size());
  for (size_t k = 0; k < b.size(); ++k)
    for (size_t i = 0; i < 8; ++i) v[8 * k + i] = ct::bit_elt(f, b[k] >> i);
  return v;
}

// ------------------------------------------------------- host F_q arith --

uint64_t mulq(uint64_t a, uint64_t b) {
  return uint64_t((unsigned __int128)a * b % kQ);
}
uint64_t powq(uint64_t a, uint64_t e) {
  return ops::ntt_detail::powmod(a, e, kQ);
}
// The integer v in [-q/2, q/2) as an element of F_q.
uint64_t modq(int64_t v) {
  return uint64_t((v % int64_t(kQ) + int64_t(kQ)) % int64_t(kQ));
}
// a b in Z_q[X]/(X^n + 1), schoolbook.
std::vector<uint64_t> negacyclic_host(const std::vector<uint64_t> &a,
                                      const std::vector<uint64_t> &b) {
  const size_t n = a.size();
  std::vector<uint64_t> c(n, 0);
  for (size_t i = 0; i < n; ++i)
    for (size_t j = 0; j < n; ++j) {
      const uint64_t p = mulq(a[i], b[j]);
      const size_t k = (i + j) % n;
      c[k] = i + j < n ? (c[k] + p) % kQ : (c[k] + kQ - p) % kQ;
    }
  return c;
}
// FIPS 204's NTT order: entry k is a(zeta^(2 brv(k) + 1)), zeta = 1753,
// brv the reversal of 8 bits.
std::vector<uint64_t> ntt_host(const std::vector<uint64_t> &a) {
  std::vector<uint64_t> out(256);
  for (size_t k = 0; k < 256; ++k) {
    size_t brv = 0;
    for (size_t t = 0; t < 8; ++t) brv |= ((k >> t) & 1) << (7 - t);
    const uint64_t r = powq(1753, 2 * brv + 1);
    uint64_t acc = 0;
    uint64_t rp = 1;
    for (size_t i = 0; i < 256; ++i) {
      acc = (acc + mulq(a[i], rp)) % kQ;
      rp = mulq(rp, r);
    }
    out[k] = acc;
  }
  return out;
}
std::vector<AElt> to_af(const std::vector<uint64_t> &v) {
  std::vector<AElt> out;
  for (uint64_t x : v) out.push_back(env().af.of_scalar(x));
  return out;
}

// --------------------------------------------------- byte windows (host) --

// g, a generator of GF(2^16)^*, and X = g^257, a generator of GF(2^8).
HElt gen16() {
  return lib::select::subfield_generator(env().hf);
}
HElt gen8() {
  return lib::windows::windows_internal::power(env().hf, gen16(), 257);
}
std::vector<HElt> powers(const HElt &g, size_t n) {
  std::vector<HElt> p(n);
  HElt a = env().hf.one();
  for (auto &x : p) {
    x = a;
    a = env().hf.mulf(a, g);
  }
  return p;
}
// The least offset at which the document's bytes DOC (Bit [n, 8]) hold
// the window WIN (Bit [L, 8]), found with no branch on the bytes.
uint64_t match_offset(const std::vector<HElt> &doc,
                      const std::vector<HElt> &win) {
  const HF &f = env().hf;
  const size_t n = doc.size() / 8;
  const size_t L = win.size() / 8;
  uint64_t offset = 0;
  uint64_t found = 0;
  for (size_t o = 0; o + L <= n; ++o) {
    uint64_t m = 1;
    for (size_t k = 0; k < 8 * L; ++k)
      m &= ct::eq(ct::bit_of(f, doc[8 * o + k]), ct::bit_of(f, win[k]));
    const uint64_t take = m & (found ^ 1);
    offset |= ct::mask(take) & o;
    found |= m;
  }
  return offset;
}

// ------------------------------------------------------- honest prover --
// The honest prover's host code (namespace prover): closures that fill
// priv values. None is part of a relation.
namespace prover {

// Keccak-f's states after rounds k, 2k, ..., 24 from the state IN.
inline auto keccak_states(size_t k) {
  return [k](const std::vector<HElt> &in) {
    const HF &f = env().hf;
    Lanes a = bits_lanes(f, in.data());
    std::vector<HElt> out;
    for (size_t r = 0; r < 24; ++r) {
      a = keccak_round_host(a, r);
      const auto bits = lanes_bits(f, a);
      const bool checkpoint = (r + 1) % k == 0;
      out.insert(out.end(), checkpoint ? bits.begin() : bits.end(),
                 bits.end());
    }
    return out;
  };
}
// g^offset, the window's offset in the document.
inline std::vector<HElt> g_to_offset(const std::vector<HElt> &doc,
                                     const std::vector<HElt> &win) {
  return {lib::windows::windows_internal::power(env().hf, gen16(),
                                                match_offset(doc, win))};
}
// One flag per document byte: 1 on the window's bytes.
inline std::vector<HElt> window_mask(const std::vector<HElt> &doc,
                                     const std::vector<HElt> &win) {
  const uint64_t o = match_offset(doc, win);
  const uint64_t L = win.size() / 8;
  std::vector<HElt> keep(doc.size() / 8);
  for (size_t i = 0; i < keep.size(); ++i)
    keep[i] = ct::bit_elt(env().hf, ct::lt(i, o + L) & (ct::lt(i, o) ^ 1));
  return keep;
}

}  // namespace prover

// ---------------------------------------------------------- statements --

// Deterministic test data.
struct Data {
  std::mt19937_64 g{20261006};
  uint64_t below(uint64_t n) { return g() % n; }
  std::vector<uint8_t> bytes(size_t n) {
    std::vector<uint8_t> b(n);
    for (auto &x : b) x = uint8_t(g());
    return b;
  }
};

// The lattice key: K = L = 4, eta = 2, s1 and s2 short, A
// public in NTT form, t = A s1 + s2, and h = SHAKE256(enc(s1)), enc 4 bits
// per coefficient of s1 + eta.
struct LatticeKey {
  static constexpr size_t K = 4, L = 4, kN = 256;
  static constexpr int64_t eta = 2;
  std::vector<std::vector<int64_t>> s1, s2;
  std::vector<uint64_t> a_hat, t;
  std::vector<uint8_t> enc, h;
  LatticeKey() {
    Data d;
    s1.assign(L, std::vector<int64_t>(kN));
    s2.assign(K, std::vector<int64_t>(kN));
    for (auto &p : s1)
      for (auto &c : p) c = int64_t(d.below(2 * eta + 1)) - eta;
    for (auto &p : s2)
      for (auto &c : p) c = int64_t(d.below(2 * eta + 1)) - eta;
    t.assign(K * kN, 0);
    a_hat.assign(K * L * kN, 0);
    for (size_t i = 0; i < K; ++i)
      for (size_t j = 0; j < L; ++j) {
        std::vector<uint64_t> aij(kN);
        for (auto &c : aij) c = d.below(kQ);
        const auto ah = ntt_host(aij);
        std::copy(ah.begin(), ah.end(),
                  a_hat.begin() + long((i * L + j) * kN));
        std::vector<uint64_t> sj(kN);
        for (size_t k = 0; k < kN; ++k) sj[k] = modq(s1[j][k]);
        const auto prod = negacyclic_host(aij, sj);
        for (size_t k = 0; k < kN; ++k)
          t[i * kN + k] = (t[i * kN + k] + prod[k]) % kQ;
      }
    for (size_t i = 0; i < K; ++i)
      for (size_t k = 0; k < kN; ++k)
        t[i * kN + k] = (t[i * kN + k] + modq(s2[i][k])) % kQ;
    enc.assign(L * kN / 2, 0);
    for (size_t j = 0; j < L; ++j)
      for (size_t k = 0; k < kN; ++k) {
        const size_t c = j * kN + k;
        enc[c / 2] |= uint8_t(uint64_t(s1[j][k] + eta) << (4 * (c % 2)));
      }
    KeccakHost host;
    KeccakSpongeHost sponge(host);
    h = sponge.hash(kShake256, enc, 32);
  }
  std::vector<uint64_t> s2_shifted() const {
    std::vector<uint64_t> v;
    for (const auto &p : s2)
      for (auto c : p) v.push_back(modq(c));
    return v;
  }
};

// ------------------------------------------------------------ host test --

// The host Keccak and its index maps agree with the reference permutation,
// and with the gather of rho and pi on one state.
TEST(SpecHost, KeccakTables) {
  Data d;
  Lanes a{};
  for (auto &x : a) x = d.g();
  Lanes mine = a;
  for (size_t r = 0; r < 24; ++r) mine = keccak_round_host(mine, r);
  uint64_t ref[5][5];
  for (size_t x = 0; x < 5; ++x)
    for (size_t y = 0; y < 5; ++y) ref[x][y] = a[x + 5 * y];
  KeccakTrace::permute(ref);
  for (size_t x = 0; x < 5; ++x)
    for (size_t y = 0; y < 5; ++y) EXPECT_EQ(mine[x + 5 * y], ref[x][y]);
  // rho and pi as kRhoPi: B[y][(2 x + 3 y) % 5] = rot(A[x][y]).
  const HF &f = env().hf;
  const auto bits = lanes_bits(f, a);
  std::vector<HElt> b(1600);
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      for (size_t z = 0; z < 64; ++z) b[at3(y, x, z)] = bits[kRhoPi[y][x][z]];
  const Lanes bl = bits_lanes(f, b.data());
  for (size_t y = 0; y < 5; ++y)
    for (size_t x = 0; x < 5; ++x)
      EXPECT_EQ(bl[y + 5 * ((2 * x + 3 * y) % 5)],
                rotl(a[x + 5 * y], kRot[x][y]));
}

// -------------------------------------------------------------- records --

namespace records {

// clang-format off
// spec listing records
template <template <class> class F>
struct Attributes {
  F<std::vector<std::array<uint8_t, 32>>> id;
  F<std::vector<uint8_t>> id_len;
};
template <template <class> class F>
struct Statement {
  F<std::array<uint8_t, 20>> now;
  Attributes<F> attr;
};
template <template <class> class F>
struct Witness {
  F<std::vector<std::array<uint8_t, 32>>> ids;
};
// end of spec listing records
// clang-format on

TEST(Spec, Records) {
  constexpr size_t n = 2;
  Statement<Value> st_shape{};
  st_shape.attr.id.resize(n);
  st_shape.attr.id_len.resize(n);
  Witness<Value> w_shape{};
  w_shape.ids.resize(n);
  std::vector<std::string> names;
  auto rel = compile<Statement, Witness>(
      spec_compile_profile(),
      [&names](Sys &cs, Statement<In> st, Witness<In> w) {
        auto &H = cs.domain(binary_profile);
        names = {st.now.name(), st.attr.id.name(), st.attr.id_len.name()};
        // clang-format off
        // spec listing records
        // In the relation:
        st.attr.id_len.check(computes("at_most", {32}), [](const std::vector<uint8_t> &len) {
          return std::ranges::all_of(len, [](uint8_t l) { return l <= 32; });
        });
        auto ids = H.priv(w.ids);
        assert_equal(ids, st.attr.id.bits(H));
        // end of spec listing records
        // clang-format on
      },
      "spec-records", st_shape, w_shape);
  EXPECT_EQ(names, (std::vector<std::string>{"now", "attr.id", "attr.id_len"}));
  Statement<Value> statement = st_shape;
  Witness<Value> witness = w_shape;
  for (size_t a = 0; a < n; ++a) {
    for (size_t k = 0; k < 32; ++k)
      statement.attr.id[a][k] = uint8_t(k < 10 + a ? 'a' + k : 0);
    statement.attr.id_len[a] = uint8_t(10 + a);
  }
  witness.ids = statement.attr.id;
  SecureRandomEngine rng;
  const auto proof = rel.prove(statement, witness, rng);
  EXPECT_TRUE(rel.verify(statement, proof));
  // Another identifier byte, and a length the check refuses.
  Statement<Value> other = statement;
  other.attr.id[1][3] ^= 1;
  EXPECT_FALSE(rel.verify(other, proof));
  other = statement;
  other.attr.id_len[0] = 33;
  EXPECT_FALSE(rel.verify(other, proof));
}

}  // namespace records

// ----------------------------------------------------- linear operators --

// A cyclic transform of length n over F, by its definition (O(n^2)): the
// helper CyclicConvOp names.
template <class F>
class CyclicNtt {
 public:
  using Elt = typename F::Elt;
  CyclicNtt(const F &f, size_t n)
      : f_(f), w_(*ops::FieldNtt<F>::root(f, n)), winv_(f.invertf(w_)),
        ninv_(f.invertf(f.of_scalar(uint64_t(n)))), n_(n) {}
  std::vector<Elt> spectrum(const std::vector<Elt> &c) const {
    std::vector<Elt> v = c;
    forward(v);
    return v;
  }
  void forward(std::vector<Elt> &v) const { v = dft(v, w_); }
  void inverse(std::vector<Elt> &v) const {
    v = dft(v, winv_);
    for (auto &x : v) f_.mul(x, ninv_);
  }

 private:
  std::vector<Elt> dft(const std::vector<Elt> &v, const Elt &w) const {
    std::vector<Elt> out(n_, f_.zero());
    Elt wk = f_.one();
    for (size_t k = 0; k < n_; ++k) {
      Elt wkj = f_.one();
      for (size_t j = 0; j < n_; ++j) {
        f_.add(out[k], f_.mulf(v[j], wkj));
        f_.mul(wkj, wk);
      }
      f_.mul(wk, w);
    }
    return out;
  }
  const F &f_;
  Elt w_, winv_, ninv_;
  size_t n_;
};
// c[-i mod n].
template <class Elt>
std::vector<Elt> index_negated(const std::vector<Elt> &c) {
  std::vector<Elt> r(c.size());
  for (size_t i = 0; i < c.size(); ++i) r[(c.size() - i) % c.size()] = c[i];
  return r;
}

// clang-format off
// spec listing cyclic-conv
// y = c ⊛ x, indices mod n
template <class F>
struct CyclicConvOp : LinearOperator<F> {
  using Elt = typename F::Elt;

  CyclicConvOp(const F &f, const std::vector<Elt> &c)
      : f_(f), ntt_(f, c.size()), c_hat_(ntt_.spectrum(c)),
        c_rev_hat_(ntt_.spectrum(index_negated(c))) {}

  size_t rows() const override { return c_hat_.size(); }
  size_t cols() const override { return c_hat_.size(); }

  // y = C x
  void apply(const Elt *x, Elt *y) const override {
    convolve(c_hat_, x, y);
  }

  // x = Cᵀ y. The transpose of a circulant is the circulant of c[−i mod n].
  void transpose_apply(const Elt *y, Elt *x) const override {
    convolve(c_rev_hat_, y, x);
  }

 private:
  void convolve(const std::vector<Elt> &k_hat, const Elt *in, Elt *out) const {
    std::vector<Elt> v(in, in + rows());
    ntt_.forward(v);
    for (size_t i = 0; i < v.size(); ++i)
      f_.mul(v[i], k_hat[i]);
    ntt_.inverse(v);
    std::copy(v.begin(), v.end(), out);
  }

  const F &f_;
  // length n; needs an n-th root of unity in F
  CyclicNtt<F> ntt_;
  std::vector<Elt> c_hat_;
  std::vector<Elt> c_rev_hat_;
};

// P must be pub
template <class F, class T, class P>
Op<F> CyclicConv(Ref<F, T, P> c) {
  return linear_operator<F>({
      .name = "cyclic_conv",
      .rows = c.n,
      .cols = c.n,
      .deps = depends_on(c),
      .make = [](const F &f, const auto &cv) { return std::make_shared<CyclicConvOp<F>>(f, cv); },
  });
}
// end of spec listing cyclic-conv
// clang-format on

// The cyclic convolution t = c ⊛ v in A, n = 16. Its predicate reads an
// operator with no circuit expansion, so it is placed in affine rows.
TEST(Spec, CyclicConv) {
  constexpr size_t n = 16;
  Sys cs;
  auto &A = cs.domain(odd_profile);
  auto c = A.pub(Subfield<Fq>{}, Shape{n});
  auto t = A.pub(Subfield<Fq>{}, Shape{n});
  auto v = A.priv(Subfield<Fq>{}, Shape{n});
  // clang-format off
  // spec listing cyclic-conv
  assert_zero(CyclicConv(c)(v) - t);
  // end of spec listing cyclic-conv
  // clang-format on
  const auto comp = compile(cs, spec_compile_profile());
  const std::string r = comp->report();
  // No circuit expansion: affine rows, combined by the operator's transpose.
  EXPECT_EQ(placement_of(r, "assert_zero.0"), "affine rows") << r;
  // A has no circuit constraint, so it runs no GKR: its circuit has no
  // layers and the plan lists no circuit.
  EXPECT_TRUE(has(r, "circuit: none (no circuit constraint, no GKR)")) << r;
  const DomainPlan plan = comp->compiled_domain(0).plan();
  EXPECT_FALSE(plan.gkr);
  EXPECT_EQ(plan.layers, 0u);
  EXPECT_EQ(plan.quad_terms, 0u);
  Data d;
  std::vector<uint64_t> cv(n), vv(n), tv(n, 0);
  for (auto &x : cv) x = d.below(kQ);
  for (auto &x : vv) x = d.below(kQ);
  for (size_t i = 0; i < n; ++i)
    for (size_t j = 0; j < n; ++j)
      tv[(i + j) % n] = (tv[(i + j) % n] + mulq(cv[i], vv[j])) % kQ;
  Assignment st;
  st.set(c, to_af(cv)).set(t, to_af(tv));
  const AF &af = env().af;
  Assignment w;
  w.set(v, to_af(vv));
  EXPECT_TRUE(proves(*comp, st, w));
  Assignment wrong = w;
  wrong.set(v, bumped<AF>(to_af(vv), 3));
  EXPECT_FALSE(proves(*comp, st, wrong, nullptr, true));
  // An honest proof against a tampered relation: the verifier's t differs
  // in one coordinate.
  {
    SecureRandomEngine rng;
    const auto proof = comp->prepare(st).prove(w, rng);
    EXPECT_TRUE(comp->prepare(st).verify(proof));
    std::vector<uint64_t> tv2 = tv;
    tv2[5] = (tv2[5] + 1) % kQ;
    Assignment st2;
    st2.set(c, to_af(cv)).set(t, to_af(tv2));
    EXPECT_FALSE(comp->prepare(st2).verify(proof));
  }
  // The transpose: <y, C x> = <C^T y, x>.
  const CyclicConvOp<AF> op(af, to_af(cv));
  const auto x = to_af(vv);
  const auto y = to_af(tv);
  std::vector<AElt> cx(n), cty(n);
  op.apply(x.data(), cx.data());
  op.transpose_apply(y.data(), cty.data());
  AElt l = af.zero();
  AElt rr = af.zero();
  for (size_t i = 0; i < n; ++i) {
    af.add(l, af.mulf(y[i], cx[i]));
    af.add(rr, af.mulf(cty[i], x[i]));
  }
  EXPECT_EQ(l, rr);
}

// Two domains, one without a circuit constraint: H proves z = x y on Bit
// cells in its circuit, A the cyclic convolution in affine rows only. Both
// share one transcript; A runs no GKR. A wrong value in either domain is
// rejected.
TEST(Spec, CircuitFreeDomainBesideACircuit) {
  constexpr size_t n = 16;
  Sys cs;
  auto &H = cs.domain(binary_profile);
  auto &A = cs.domain(odd_profile);
  auto x = H.priv(Bit{}, Shape{64});
  auto y = H.priv(Bit{}, Shape{64});
  auto z = H.priv(Bit{}, Shape{64});
  assert_zero(x * y - z).pin(Placement::kCircuit);
  auto c = A.pub(Subfield<Fq>{}, Shape{n});
  auto t = A.pub(Subfield<Fq>{}, Shape{n});
  auto v = A.priv(Subfield<Fq>{}, Shape{n});
  assert_zero(CyclicConv(c)(v) - t);
  const auto comp = compile(cs, spec_compile_profile());
  EXPECT_TRUE(comp->compiled_domain(0).plan().gkr);
  EXPECT_FALSE(comp->compiled_domain(1).plan().gkr);
  const HF &hf = env().hf;
  Data d;
  std::vector<HElt> xv(64), yv(64), zv(64);
  for (size_t i = 0; i < 64; ++i) {
    const uint64_t a = d.below(2), b = d.below(2);
    xv[i] = ct::bit_elt(hf, a);
    yv[i] = ct::bit_elt(hf, b);
    zv[i] = ct::bit_elt(hf, a & b);
  }
  std::vector<uint64_t> cv(n), vv(n), tv(n, 0);
  for (auto &e : cv) e = d.below(kQ);
  for (auto &e : vv) e = d.below(kQ);
  for (size_t i = 0; i < n; ++i)
    for (size_t j = 0; j < n; ++j)
      tv[(i + j) % n] = (tv[(i + j) % n] + mulq(cv[i], vv[j])) % kQ;
  Assignment st;
  st.set(c, to_af(cv)).set(t, to_af(tv));
  Assignment w;
  w.set(x, xv).set(y, yv).set(z, zv).set(v, to_af(vv));
  EXPECT_TRUE(proves(*comp, st, w));
  Assignment wrong_v = w;
  wrong_v.set(v, bumped<AF>(to_af(vv), 7));
  EXPECT_FALSE(proves(*comp, st, wrong_v, nullptr, true));
  size_t one = 0;
  while (xv[one] != hf.one() || yv[one] != hf.one()) ++one;
  Assignment wrong_z = w;
  wrong_z.set(z, bumped<HF>(zv, one));
  EXPECT_FALSE(proves(*comp, st, wrong_z, nullptr, true));
}

// A domain whose only predicate is a quadratic triple: no GKR and no
// linear row, so Ligero checks the triple alone. A wrong product aborts
// the prover (the Ligero prover checks its quadratic rows itself, as in
// GordieHowe.CheatingQuadraticTripleAbortsProver).
TEST(Spec, TriplesOnlyDomain) {
  constexpr size_t n = 8;
  Sys cs;
  auto &A = cs.domain(odd_profile);
  auto a = A.priv(Field{}, Shape{n});
  auto b = A.priv(Field{}, Shape{n});
  auto p = A.priv(Field{}, Shape{n});
  assert_zero(a * b - p).pin(Placement::kQuadratic);
  const auto comp = compile(cs, spec_compile_profile());
  EXPECT_FALSE(comp->compiled_domain(0).plan().gkr);
  const AF &af = env().af;
  std::vector<AElt> av(n), bv(n), pv(n);
  for (size_t i = 0; i < n; ++i) {
    av[i] = af.of_scalar(3 + i);
    bv[i] = af.of_scalar(11 + 2 * i);
    pv[i] = af.mulf(av[i], bv[i]);
  }
  Assignment w;
  w.set(a, av).set(b, bv).set(p, pv);
  EXPECT_TRUE(proves(*comp, Assignment{}, w));
  Assignment wrong = w;
  wrong.set(p, bumped<AF>(pv, 2));
  EXPECT_DEATH((void)proves(*comp, Assignment{}, wrong, nullptr, true),
               "invalid quadratic constraints");
}

// The cost of a domain without a circuit constraint: the cyclic
// convolution of Spec.CyclicConv at n = GH_NOGKR_N (default 256), proved
// GH_NOGKR_REPS times (default 15). Prints the domain's proof bytes and the
// medians of its prover time (commit + prove) and verifier time.
TEST(SpecMeasure, DISABLED_CircuitFreeDomain) {
  const char *en = std::getenv("GH_NOGKR_N");
  const char *er = std::getenv("GH_NOGKR_REPS");
  const size_t n = en != nullptr ? size_t(std::atoi(en)) : 256;
  const size_t reps = er != nullptr ? size_t(std::atoi(er)) : 15;
  Sys cs;
  auto &A = cs.domain(odd_profile);
  auto c = A.pub(Subfield<Fq>{}, Shape{n});
  auto t = A.pub(Subfield<Fq>{}, Shape{n});
  auto v = A.priv(Subfield<Fq>{}, Shape{n});
  assert_zero(CyclicConv(c)(v) - t);
  const auto comp = compile(cs, spec_compile_profile());
  Data d;
  std::vector<uint64_t> cv(n), vv(n), tv(n, 0);
  for (auto &x : cv) x = d.below(kQ);
  for (auto &x : vv) x = d.below(kQ);
  for (size_t i = 0; i < n; ++i)
    for (size_t j = 0; j < n; ++j)
      tv[(i + j) % n] = (tv[(i + j) % n] + mulq(cv[i], vv[j])) % kQ;
  Assignment st;
  st.set(c, to_af(cv)).set(t, to_af(tv));
  Assignment w;
  w.set(v, to_af(vv));
  const auto prep = comp->prepare(st);
  std::vector<double> prove_ms, verify_ms;
  size_t bytes = 0;
  for (size_t k = 0; k < reps; ++k) {
    SecureRandomEngine rng;
    ProveTimes times;
    std::vector<size_t> dbytes;
    Sys::ProveOptions opt;
    opt.times = &times;
    opt.domain_bytes = &dbytes;
    const auto proof = prep.prove(w, rng, opt);
    VerifyTimes vt;
    ASSERT_TRUE(prep.verify(proof, &vt));
    prove_ms.push_back(times.domain_commit.at(0) + times.domain_prove.at(0));
    verify_ms.push_back(vt.domain.at(0));
    bytes = dbytes.at(0);
  }
  std::sort(prove_ms.begin(), prove_ms.end());
  std::sort(verify_ms.begin(), verify_ms.end());
  std::printf("NOGKR_MEASURE n=%zu reps=%zu domain_bytes=%zu "
              "prove_ms_median=%.3f verify_ms_median=%.3f\n",
              n, reps, bytes, prove_ms[reps / 2], verify_ms[reps / 2]);
}

// clang-format off
// spec listing ch
template <class E>
auto ch(const E &x, const E &y, const E &z) {
  return (x & y) ^ (~x & z);
}
// end of spec listing ch
// clang-format on

// out = ch(x, y, z) on 64 bits of H: a Bit expression of degree 2.
TEST(Spec, CompositeOperator) {
  constexpr size_t n = 64;
  Sys cs;
  auto &H = cs.domain(binary_profile);
  auto x = H.priv(Bit{}, Shape{n});
  auto y = H.priv(Bit{}, Shape{n});
  auto z = H.priv(Bit{}, Shape{n});
  auto out = H.priv(Bit{}, Shape{n});
  assert_equal(out, ch(x, y, z));
  const auto comp = compile(cs, spec_compile_profile());
  const std::string r = comp->report();
  // Degree 2 in Bit cells: not affine.
  EXPECT_NE(placement_of(r, "assert_zero.0"), "affine rows") << r;
  const HF &hf = env().hf;
  Data d;
  std::vector<HElt> xv(n), yv(n), zv(n), ov(n);
  for (size_t i = 0; i < n; ++i) {
    const uint64_t a = d.below(2), b = d.below(2), e = d.below(2);
    xv[i] = ct::bit_elt(hf, a);
    yv[i] = ct::bit_elt(hf, b);
    zv[i] = ct::bit_elt(hf, e);
    ov[i] = ct::bit_elt(hf, (a & b) ^ ((a ^ 1) & e));
  }
  Assignment w;
  w.set(x, xv).set(y, yv).set(z, zv).set(out, ov);
  EXPECT_TRUE(proves(*comp, Assignment{}, w));
  Assignment wrong = w;
  wrong.set(out, bumped<HF>(ov, 5));
  EXPECT_FALSE(proves(*comp, Assignment{}, wrong, nullptr, true));
}

// ------------------------------------------------------ compiler output --

namespace compiler_output {

// clang-format off
// spec listing compiler-output
constexpr size_t R = 24;
constexpr size_t N = 256;
constexpr size_t L = 8;
constexpr size_t W = N * L;
constexpr uint64_t eta = 2;

template <template <class> class F>
struct Statement {
  F<std::array<int32_t, N>> a;
  F<std::array<int32_t, N>> t;
  F<std::array<int32_t, N>> p;
};
template <template <class> class F>
struct Witness {
  F<std::array<std::array<bool, W>, R + 1>> x;
  F<std::array<std::array<bool, W>, R>> u;
  F<std::array<int32_t, N>> v;
};

void relation(ConstraintSystem<SHA384, GF2_128<>, MlDsaField11> &cs,
              Statement<In> st, Witness<In> w) {
  // F_{2^128}, evaluation subfield GF(2^16)
  auto &H = cs.domain(binary_profile);
  // F_{q^k}, evaluation subfield F_q
  auto &A = cs.domain(odd_profile);
  auto a = st.a.values(A);
  auto t = st.t.values(A);
  auto p = st.p.values(A);

  // Bits in H, one degree-2 relation over all rounds
  auto x = H.priv(w.x);
  auto u = H.priv(w.u);
  auto next = x.slice(1, R + 1);
  auto prev = x.slice(0, R);
  assert_zero(next - prev - u * prev);

  // F_q values in A: an affine relation and a range
  auto v = A.priv(Subfield<Fq>{}, w.v);
  assert_zero(NegacyclicConv(a)(v) - t);
  assert_range(v + eta, 2 * eta + 1);

  // A challenge: v is a permutation of the public p
  auto delta = A.challenge();
  assert_equal((delta - v).prod(), (delta - p).prod());

  // The same data in both fields
  auto b = x[R].to(A).reshape(Shape{N, L});
  assert_zero(v - b.from_bits());
}
// end of spec listing compiler-output
// clang-format on

// The instance: v in [0, eta], x[r] its bits for every round r, u set
// only on zero bits (so x[r + 1] = x[r]), p a rotation of v, and t = a v
// negacyclic.
struct Instance {
  Statement<Value> st;
  Witness<Value> w;
  Instance() {
    Data d;
    std::vector<uint64_t> v(N), a(N);
    for (auto &e : v) e = d.below(eta + 1);
    for (auto &e : a) e = d.below(kQ);
    std::vector<uint64_t> p = v;
    std::rotate(p.begin(), p.begin() + 5, p.end());
    const std::vector<uint64_t> t = negacyclic_host(a, v);
    for (size_t i = 0; i < N; ++i) {
      st.a[i] = int32_t(a[i]);
      st.t[i] = int32_t(t[i]);
      st.p[i] = int32_t(p[i]);
      w.v[i] = int32_t(v[i]);
    }
    for (size_t r = 0; r <= R; ++r)
      for (size_t i = 0; i < N; ++i)
        for (size_t j = 0; j < L; ++j) w.x[r][i * L + j] = (v[i] >> j) & 1;
    for (size_t r = 0; r < R; ++r)
      for (size_t i = 0; i < N; ++i)
        for (size_t j = 0; j < L; ++j)
          w.u[r][i * L + j] = !((v[i] >> j) & 1) && (r + i) % 2 == 1;
  }
};

// Section 12's table and phases on the compiled system C. b (x[R] in A)
// and delta are the listing's unnamed values: the Bit copy of W
// coordinates and the one challenge it draws.
void check_compiler_output(const Sys::Compiled &c) {
  const std::string r = c.report();
  const size_t x = node_named(c, "x");
  const size_t u = node_named(c, "u");
  const size_t v = node_named(c, "v");
  const size_t b = node_auto(c, "priv", W);
  const size_t delta = node_auto(c, "challenge.", 1);
  // round relation: one batched zerocheck, bit-sliced evaluator.
  EXPECT_EQ(placement_of(r, "assert_zero.0"), "field batch") << r;
  // NegacyclicConv(a)(v) - t: affine rows.
  EXPECT_EQ(placement_of(r, "assert_zero.0", "domain1"), "affine rows") << r;
  // prod equality: A's circuit, delta a public input, degree bound N.
  EXPECT_EQ(placement_of(r, "assert_zero.1", "domain1"), "circuit") << r;
  EXPECT_EQ(charge_of(c, delta), Bound(N));
  // b (Bit in A): Booleanity checks, placed by cost.
  EXPECT_TRUE(has(r, "Boolean checks n=")) << r;
  // Phases: x, u, v, b in phase 0; delta and kappa in phase 1; alpha in 2.
  EXPECT_EQ(c.phase(x), 0u);
  EXPECT_EQ(c.phase(u), 0u);
  EXPECT_EQ(c.phase(v), 0u);
  EXPECT_EQ(c.phase(b), 0u);
  EXPECT_EQ(c.phase(delta), 1u);
  EXPECT_EQ(challenge_phase(c, ".beta"), 1u);
  EXPECT_EQ(challenge_phase(c, "alpha:"), 2u);
  EXPECT_EQ(c.phases(), 2u);
  // The MAC's late values are sent masked.
  EXPECT_FALSE(c.messages().empty());
}

TEST(Spec, CompilerOutput) {
  const CompileProfile profile = spec_compile_profile();
  const auto inst = std::make_unique<Instance>();
  const Statement<Value> &statement = inst->st;
  const Witness<Value> &witness = inst->w;
  SecureRandomEngine rng;

  // clang-format off
  // spec listing compiler-output
  auto rel = compile<Statement, Witness>(profile, relation);
  auto proof = rel.prove(statement, witness, rng);
  bool ok = rel.verify(statement, proof);
  // end of spec listing compiler-output
  // clang-format on

  EXPECT_TRUE(ok);
  const auto &typed = rel.typed<Sys>();
  const auto st = typed.statement(statement);
  // u set at a one bit of x clears it in the next round.
  size_t one = 0;
  while (!witness.x[0][one]) ++one;
  auto wrong = std::make_unique<Witness<Value>>(witness);
  wrong->u[0][one] = true;
  EXPECT_FALSE(
      proves(typed.compiled(), st, typed.witness(*wrong), nullptr, true));
  auto wrong_v = std::make_unique<Witness<Value>>(witness);
  wrong_v->v[2] += 1;
  EXPECT_FALSE(
      proves(typed.compiled(), st, typed.witness(*wrong_v), nullptr, true));
  check_compiler_output(typed.compiled());
}

}  // namespace compiler_output

// ------------------------------------------------- sorted rearrangement --

namespace sorted_rearrangement {

// clang-format off
// spec listing sorted
constexpr size_t n = 1024;
// The entries of p are below B, and 2B ≤ q
constexpr uint64_t B = 1 << 16;
template <template <class> class F>
struct Statement {
  F<std::array<uint32_t, n>> p;
};
template <template <class> class F>
struct Witness {};
// end of spec listing sorted
// clang-format on

// The sorted rearrangement at n = 1024 and B = 2^16.
TEST(Spec, SortedRearrangement) {
  auto rel = compile<Statement, Witness>(
      spec_compile_profile(),
      [](Sys &cs, Statement<In> st, Witness<In> w) {
        auto &A = cs.domain(odd_profile);
        // clang-format off
        // spec listing sorted
        // In the relation:
        auto p = st.p.values(A);
        // The honest prover sorts the public p; the predicates below are what prove v
        auto v = A.priv(Subfield<Fq>{}, Shape{n}, depends_on(p),
                        [](std::vector<uint64_t> p) {
                          std::sort(p.begin(), p.end());
                          return p;
                        });
        auto delta = A.challenge();
        assert_equal((delta - v).prod(), (delta - p).prod());
        assert_range(v.slice(1, n) - v.slice(0, n - 1), B);
        // end of spec listing sorted
        // clang-format on
      });
  const auto &typed = rel.typed<Sys>();
  const auto &c = typed.compiled();
  const std::string r = c.report();
  Data d;
  Statement<Value> statement;
  for (auto &e : statement.p) e = uint32_t(d.below(B));
  const Witness<Value> witness{};
  SecureRandomEngine rng;
  EXPECT_TRUE(rel.verify(statement, rel.prove(statement, witness, rng)));
  const auto st = typed.statement(statement);
  const size_t v = node_auto(c, "priv", n);
  const size_t delta = node_auto(c, "challenge.", 1);
  EXPECT_FALSE(proves(c, st, Assignment{}, bump<AF>(v, 9)));
  // v is packed 11 values of F_q per committed element.
  EXPECT_TRUE(has(r, "words of degree 11")) << r;
  // delta: A's circuit, the products in the circuit; degree bound n.
  EXPECT_EQ(placement_of(r, "assert_zero.0"), "circuit") << r;
  EXPECT_EQ(charge_of(c, delta), Bound(n));
  // The range: LogUp-GKR under its own challenge alpha, B split into two
  // digits looked up in a 256-row table.
  EXPECT_TRUE(has(r, "r0: digits T=256 k=2")) << r;
  // A single challenge phase: delta and alpha test only phase-0 values.
  EXPECT_EQ(c.phase(delta), 1u);
  EXPECT_EQ(challenge_phase(c, "alpha:"), 1u);
  EXPECT_EQ(c.phases(), 1u);
}

}  // namespace sorted_rearrangement

// ------------------------------------------------------------- Keccak-f --

// clang-format off
// spec listing keccak-round
template <class F>
auto keccak_round(Expr<F, Bit> a, size_t i) {
  // θ
  auto c = a.sum(0);
  a = a + c.rotate(1, 0) + c.rotate(-1, 0).rotate(1, 1);
  // ρ, π
  a = a[kRhoPi];
  // χ
  a = a + (~a.rotate(-1, 1) & a.rotate(-2, 1));
  // ι
  return a + kRoundConstant[i];
}
// end of spec listing keccak-round

// spec listing keccak-f
template <class F>
auto keccak_f(Domain<F> &H, Expr<F, Bit> in, size_t k) {
  auto S = H.priv(Bit{}, Shape{24 / k, 5, 5, 64}, depends_on(in), prover::keccak_states(k));
  auto x = in;
  for (size_t j = 0; j < 24 / k; ++j) {
    for (size_t r = 0; r < k; ++r)
      x = keccak_round(x, j * k + r);
    assert_equal(S[j], x);
    x = S[j];
  }
  return x;
}
// end of spec listing keccak-f
// clang-format on

// Every round state committed by D.priv(e): the batched form without a
// closure. 24 committed states, one batched zerocheck, no GKR layers.
TEST(Spec, CommittedExpression) {
  Sys cs;
  auto &H = cs.domain(binary_profile);
  using F = HF;
  auto in_handle = H.pub(Bit{}, Shape{5, 5, 64});
  Expr<F, Bit> in = in_handle;

  // clang-format off
  // spec listing priv-expr
  Expr<F, Bit> a = in;
  for (size_t i = 0; i < 24; ++i)
    a = H.priv(keccak_round(a, i));
  // end of spec listing priv-expr
  // clang-format on

  const auto c = compile(cs, spec_compile_profile());
  const std::string r = c->report();
  Data d;
  Lanes lanes{};
  for (auto &e : lanes) e = d.g();
  Assignment st;
  st.set(in_handle, lanes_bits(env().hf, lanes));
  // The compiler computes every state: no witness is supplied.
  EXPECT_TRUE(proves(*c, st, Assignment{}));
  // 24 committed states, each the value of one D.priv(e); a wrong
  // coordinate of the first is rejected.
  std::vector<size_t> states;
  for (size_t id = 0; id < c->nodes().size(); ++id) {
    const std::string &m = c->nodes()[id].name;
    if (m.size() > 6 && m.compare(m.size() - 6, 6, ".value") == 0)
      states.push_back(id);
  }
  ASSERT_EQ(states.size(), 24u) << r;
  for (size_t id : states) EXPECT_EQ(c->phase(id), 0u);
  EXPECT_FALSE(proves(*c, st, Assignment{},
                      bump<HF>(stored_node(c->nodes(), states[0]), 7)));
  EXPECT_EQ(count_lines(r, "batch "), 1u) << r;
  EXPECT_FALSE(has(r, ": circuit (")) << r;
}

// The batched form (keccak_f's body at k = 1).
TEST(Spec, KeccakBatched) {
  Sys cs;
  auto &H = cs.domain(binary_profile);
  // The input state of shape [5][5][64].
  auto in_handle = H.pub(Bit{}, Shape{5, 5, 64});
  Expr<GF2_128<>, Bit> in = in_handle;

  // clang-format off
  // spec listing keccak-batched
  auto S = H.priv(Bit{}, Shape{24, 5, 5, 64},
                  depends_on(in), prover::keccak_states(1));
  auto x = in;
  for (size_t i = 0; i < 24; ++i) {
    assert_equal(S[i], keccak_round(x, i));
    x = S[i];
  }
  // end of spec listing keccak-batched
  // clang-format on

  const auto c = compile(cs, spec_compile_profile());
  const std::string r = c->report();
  Data d;
  Lanes a{};
  for (auto &e : a) e = d.g();
  Assignment st;
  st.set(in_handle, lanes_bits(env().hf, a));
  EXPECT_TRUE(proves(*c, st, Assignment{}));
  EXPECT_FALSE(proves(*c, st, Assignment{}, bump<HF>(stored(S), 1234 / 16)));
  // 24 committed states, 38,400 bits, committed as 2,400 GF(2^16) words
  // (GF(2^16) -> K); the batch reads their bits, so no wire aliases them.
  EXPECT_EQ(S.n, 38400u);
  EXPECT_EQ(S.g->nodes.at(stored(S)).n, 2400u);
  EXPECT_EQ(c->phase(S), 0u);
  EXPECT_TRUE(has(r, "packed_bits=0 ")) << r;
  EXPECT_TRUE(has(r, "bit_views=0 words")) << r;
  // One batched zerocheck over 38,400 instances, bit-sliced first round.
  EXPECT_EQ(count_lines(r, "batch "), 1u) << r;
  EXPECT_TRUE(has(r, "n=38400: field batch")) << r;
  // No GKR layers.
  EXPECT_FALSE(has(r, ": circuit (")) << r;
}

// Pins on keccak_f: the batched form pinned to the
// circuit commits every round without batching.
TEST(Spec, KeccakBatchedPinnedToCircuit) {
  Sys cs;
  auto &H = cs.domain(binary_profile);
  auto in_handle = H.pub(Bit{}, Shape{5, 5, 64});
  Expr<GF2_128<>, Bit> in = in_handle;
  auto S = H.priv(Bit{}, Shape{24, 5, 5, 64}, depends_on(in),
                  prover::keccak_states(1));
  auto x = in;
  for (size_t i = 0; i < 24; ++i) {
    assert_equal(S[i], keccak_round(x, i)).pin(Placement::kCircuit);
    x = S[i];
  }
  const auto c = compile(cs, spec_compile_profile());
  const std::string r = c->report();
  // The circuit reads the states' bits, as wires aliased onto their words.
  EXPECT_TRUE(has(r, "bit_views=2400 words")) << r;
  EXPECT_EQ(count_lines(r, "batch "), 0u) << r;
  EXPECT_TRUE(has(r, ": circuit (pinned")) << r;
}

// The sliced form (keccak_f's body at k = 6): 4 committed states, 4
// equalities of degree 64 in the circuit.
TEST(Spec, KeccakSliced) {
  Sys cs;
  auto &H = cs.domain(binary_profile);
  auto in_handle = H.pub(Bit{}, Shape{5, 5, 64});
  Expr<GF2_128<>, Bit> in = in_handle;

  // clang-format off
  // spec listing keccak-sliced
  auto S = H.priv(Bit{}, Shape{4, 5, 5, 64},
                  depends_on(in), prover::keccak_states(6));
  auto x = in;
  for (size_t j = 0; j < 4; ++j) {
    for (size_t r = 0; r < 6; ++r)
      x = keccak_round(x, 6 * j + r);
    assert_equal(S[j], x);
    x = S[j];
  }
  // end of spec listing keccak-sliced
  // clang-format on

  const auto c = compile(cs, spec_compile_profile());
  const std::string r = c->report();
  Data d;
  Lanes a{};
  for (auto &e : a) e = d.g();
  Assignment st;
  st.set(in_handle, lanes_bits(env().hf, a));
  EXPECT_TRUE(proves(*c, st, Assignment{}));
  EXPECT_FALSE(proves(*c, st, Assignment{}, bump<HF>(stored(S), 77 / 16)));
  // 4 committed states, 6,400 bits as 400 words, whose bits the circuit
  // reads as aliased wires.
  EXPECT_TRUE(has(r, "bit_views=400 words")) << r;
  // Degree 64: no batch is admissible; the circuit.
  EXPECT_EQ(count_lines(r, "batch "), 0u) << r;
  EXPECT_EQ(placement_of(r, "assert_zero.0"), "circuit") << r;
}

// .pin(Placement::kBatch) on the sliced form: compilation fails, since a
// degree-64 predicate is not admissible for a batch.
TEST(Spec, KeccakSlicedPinnedToBatch) {
  Sys cs;
  auto &H = cs.domain(binary_profile);
  Expr<GF2_128<>, Bit> in = H.pub(Bit{}, Shape{5, 5, 64});
  auto S = H.priv(Bit{}, Shape{4, 5, 5, 64}, depends_on(in),
                  prover::keccak_states(6));
  auto x = in;
  for (size_t j = 0; j < 4; ++j) {
    for (size_t r = 0; r < 6; ++r) x = keccak_round(x, 6 * j + r);
    assert_equal(S[j], x).pin(Placement::kBatch);
    x = S[j];
  }
  EXPECT_THROW((void)compile(cs, spec_compile_profile()), CompileError);
}

// keccak_f at k = 1 and k = 6: 24 states (38,400 bits) and 4 states.
TEST(Spec, KeccakF) {
  for (size_t k : {size_t(1), size_t(6)}) {
    Sys cs;
    auto &H = cs.domain(binary_profile);
    auto in_handle = H.pub(Bit{}, Shape{5, 5, 64});
    Expr<GF2_128<>, Bit> in = in_handle;
    const auto out = keccak_f(H, in, k);
    const auto c = compile(cs, spec_compile_profile());
    const std::string r = c->report();
    const bool batched = k == 1;
    EXPECT_TRUE(has(r, batched ? "bit_views=0 words" : "bit_views=400 words"))
        << r;
    Data d;
    Lanes a{};
    for (auto &e : a) e = d.g();
    Assignment st;
    st.set(in_handle, lanes_bits(env().hf, a));
    EXPECT_TRUE(proves(*c, st, Assignment{})) << "k=" << k;
    (void)out;
    EXPECT_EQ(count_lines(r, "batch "), batched ? 1u : 0u) << r;
  }
}

// -------------------------------------------- the lattice key, SHAKE256 --

// The host constants of the SHAKE256 example that the Keccak tables above do
// not name. SHAKE256's padding of a 512-byte message to 4 blocks of 136 bytes
// (0x1F, zeros, 0x80) as bits, the zero state and the zero capacity.
std::array<uint8_t, 256> make_shake_pad() {
  std::array<uint8_t, 256> p{};
  for (size_t i = 0; i < 5; ++i) p[i] = 1;
  p[255] = 1;
  return p;
}
const std::array<uint8_t, 256> kShakePad = make_shake_pad();
const StateBits kZeroState{};
const std::array<uint8_t, 512> kZeroCapacity{};

namespace lattice_key {

// clang-format off
// spec listing lattice-key
constexpr size_t K = 4;
constexpr size_t L = 4;
constexpr uint64_t eta = 2;
template <template <class> class F>
struct Statement {
  F<std::array<uint8_t, 32>> h;
  F<std::array<std::array<std::array<uint32_t, 256>, L>, K>> a_hat;
  F<std::array<std::array<uint32_t, 256>, K>> t;
};
template <template <class> class F>
struct Witness {
  F<std::array<uint8_t, 512>> enc;
  F<std::array<std::array<int32_t, 256>, K>> s2;
};
// end of spec listing lattice-key
// clang-format on

// Section 13's claims on the compiled lattice key C.
void check_lattice(const Sys::Compiled &c) {
  const std::string r = c.report();
  // H: four permutations' 96 committed states, as words, and the 4,096
  // bits of enc, packed.
  EXPECT_TRUE(has(r, "packed_bits=4096 ")) << r;
  // H: the 96 rounds of the four permutations in one batched zerocheck (A
  // has its Boolean checks' batch).
  EXPECT_EQ(count_lines(r, "batch assert_zero"), 1u) << r;
  // A: the bits get Booleanity checks; s2 packed 11 per element.
  EXPECT_TRUE(has(r, "Boolean checks n=")) << r;
  EXPECT_TRUE(has(r, "of degree 11")) << r;
  // The lattice relation is affine.
  EXPECT_TRUE(has(r, ": affine rows (reads the structured operator "
                     "'poly_mat_vec'"))
      << r;
  // The MAC under kappa, its late values masked; phases.
  EXPECT_FALSE(c.messages().empty());
  EXPECT_EQ(challenge_phase(c, ".beta"), 1u);
  EXPECT_EQ(challenge_phase(c, "alpha:"), 2u);
  EXPECT_EQ(c.phases(), 2u);
}

TEST(Spec, LatticeKey) {
  auto rel = compile<Statement, Witness>(
      spec_compile_profile(), [](Sys &cs, Statement<In> st, Witness<In> w) {
        auto &H = cs.domain(binary_profile);
        auto &A = cs.domain(odd_profile);
        // clang-format off
        // spec listing lattice-key
        // In the relation:
        auto h = st.h.bits(H).flat();
        auto a_hat = st.a_hat.values(A);
        auto t = st.t.values(A);

        // H: the sponge over the 4,096-bit encoding, four blocks of rate 1,088
        auto enc = H.priv(w.enc).flat();
        auto blocks = enc.concat(H.constant(kShakePad)).reshape(Shape{4, 1088});
        Expr<GF2_128<>, Bit> state = H.constant(kZeroState);
        for (size_t b = 0; b < 4; ++b)
          state = keccak_f(H, state + blocks[b].concat(H.constant(kZeroCapacity)).reshape(Shape{5, 5, 64}), 1);
        assert_equal(state.flat().slice(0, 256), h);

        // A: the same bits, read as coefficients
        auto s1 = enc.to(A).reshape(Shape{L, 256, 4}).from_bits() - eta;
        auto s2 = A.priv(Subfield<Fq>{}, w.s2);
        assert_range(s1 + eta, 2 * eta + 1);
        assert_range(s2 + eta, 2 * eta + 1);
        assert_zero(PolyMatVec(a_hat, Form::kNtt)(s1) + s2 - t);
        // end of spec listing lattice-key
        // clang-format on
      });
  const LatticeKey key;
  Statement<Value> statement;
  std::copy(key.h.begin(), key.h.end(), statement.h.begin());
  for (size_t i = 0; i < K; ++i) {
    for (size_t j = 0; j < L; ++j)
      for (size_t k = 0; k < 256; ++k)
        statement.a_hat[i][j][k] = uint32_t(key.a_hat[(i * L + j) * 256 + k]);
    for (size_t k = 0; k < 256; ++k)
      statement.t[i][k] = uint32_t(key.t[i * 256 + k]);
  }
  Witness<Value> witness;
  std::copy(key.enc.begin(), key.enc.end(), witness.enc.begin());
  for (size_t i = 0; i < K; ++i)
    for (size_t k = 0; k < 256; ++k)
      witness.s2[i][k] = int32_t(key.s2[i][k]);
  SecureRandomEngine rng;
  EXPECT_TRUE(rel.verify(statement, rel.prove(statement, witness, rng)));
  const auto &typed = rel.typed<Sys>();
  const auto st = typed.statement(statement);
  Witness<Value> wrong = witness;
  wrong.s2[0][17] += 1;
  EXPECT_FALSE(
      proves(typed.compiled(), st, typed.witness(wrong), nullptr, true));
  Witness<Value> wrong_enc = witness;
  wrong_enc.enc[12] ^= 0x10;
  EXPECT_FALSE(
      proves(typed.compiled(), st, typed.witness(wrong_enc), nullptr, true));
  check_lattice(typed.compiled());
}

}  // namespace lattice_key

// ----------------------------------------- a window at a private offset --

// The host constants of the window listing: g (kG16), X = g^257 (kX8), and
// the packing constant c (kPack, permutation.h's kappa).
const HElt kG16 = gen16();
const HElt kX8 = gen8();
const std::vector<HElt> kPack = {lib::permutation::selection_kappa(env().hf)};

namespace window {

// clang-format off
// spec listing window
constexpr size_t n = 2048;
constexpr size_t L = 64;
template <template <class> class F>
struct Statement {};
template <template <class> class F>
struct Witness {
  F<std::array<uint8_t, n>> doc;
  F<std::array<uint8_t, L>> win;
};
// end of spec listing window
// clang-format on

TEST(Spec, Window) {
  auto rel = compile<Statement, Witness>(
      spec_compile_profile(), [](Sys &cs, Statement<In> st, Witness<In> w) {
        auto &H = cs.domain(binary_profile);
        // clang-format off
        // spec listing window
        // In the relation:
        auto doc = H.priv(w.doc);
        auto win = H.priv(w.win);
        // g^o, for the offset o where win starts in doc
        auto z = H.priv(Subfield<GF2_16>{}, Shape{1}, depends_on(doc, win), prover::g_to_offset);
        // 1 on the window's bytes [o, o + L)
        auto keep = H.priv(Bit{}, Shape{n}, depends_on(doc, win), prover::window_mask);
        auto c = H.constant(kPack);
        auto text = H.constant(powers(kG16, n)) + c * doc.from_digits(kX8);
        auto window = z * H.constant(powers(kG16, L)) + c * win.from_digits(kX8);
        auto delta = H.challenge();
        assert_equal(keep.mux(delta - text, 1).prod(), (delta - window).prod());
        // end of spec listing window
        // clang-format on
      });
  const auto &typed = rel.typed<Sys>();
  const auto &comp = typed.compiled();
  const std::string r = comp.report();
  constexpr size_t offset = 700;
  Data d;
  const auto docb = d.bytes(n);
  const Statement<Value> statement{};
  Witness<Value> witness;
  std::copy(docb.begin(), docb.end(), witness.doc.begin());
  std::copy(docb.begin() + offset, docb.begin() + offset + L,
            witness.win.begin());
  SecureRandomEngine rng;
  EXPECT_TRUE(rel.verify(statement, rel.prove(statement, witness, rng)));
  const auto st = typed.statement(statement);
  const auto w = typed.witness(witness);
  const size_t z = node_auto(comp, "priv", 1);
  const size_t keep = node_auto(comp, "priv", n);
  const size_t delta = node_auto(comp, "challenge.", 1);
  EXPECT_FALSE(proves(comp, st, w, bump<HF>(z, 0)));
  const size_t keep_words = stored_node(comp.nodes(), keep);
  EXPECT_FALSE(proves(comp, st, w, bump<HF>(keep_words, 3)));
  // A window that is not in the document has no proof.
  Witness<Value> bad = witness;
  bad.win[2] ^= 1;
  EXPECT_FALSE(proves(comp, st, typed.witness(bad)));
  // delta enters H's circuit; the filtered product is in the circuit, of
  // degree bound max(n, L).
  EXPECT_EQ(placement_of(r, "assert_zero.0"), "circuit") << r;
  EXPECT_EQ(charge_of(comp, delta), Bound(n));
  EXPECT_EQ(comp.phase(delta), 1u);
  EXPECT_EQ(comp.phases(), 1u);
  // One flag per document byte and one element z.
  EXPECT_EQ(comp.nodes().at(keep).n, n);
  EXPECT_EQ(comp.nodes().at(z).n, 1u);
}

}  // namespace window

}  // namespace
}  // namespace proofs::gordiehowe
