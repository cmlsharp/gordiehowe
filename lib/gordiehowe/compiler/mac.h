// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the MAC equality.
//
// The assert_same_bits calls between one binary domain H and one odd domain A
// whose operands share a phase lower to one MAC: the members' sides are
// concatenated (X_H, X_A, in declaration order), and H hosts the MAC
// whichever order the arguments come in:
//
//   B     pad of H (Field, 1)              phase 0
//   B_A   pad_copy(A, polynomial_bits(B))  phase 0, Bit w
//   beta  challenge in H
//   r     public: r[c] = beta^(c+1)
//   U     late priv value of H masked by B: U = sum_c X_H[c] r[c]; message T
//   bits  public: CoefficientBits{mac_basis} of T in A, Bit
//
// with the H predicate U = sum_c chunk_c(X_H) r_c, chunk_c the field element
// of chunk c's bits in the polynomial basis: an equality, affine in the
// committed bits once beta (and so each r_c) is public, with U read as its
// message minus its pad, which placement realizes on the linear test (its
// coefficients read the challenge). The A side is the tail
// assert_mod(B_A + sum_c MACConv(r_c)(X_A,c), bits(T), 2) (mod.h), whose
// units are the blind (below 2) and the chunks (each below convMax): one
// group (the accumulator acc = B_A + MACConv(r)(X_A) with a balanced
// radix chosen from acc_max) while acc_max fits below p, otherwise groups of
// chunks with parity bits and quotient digits, the blind entering the
// final sum. The accumulators come from popcounts
// (mac_integer_accumulators, grouped).
//
// Between two odd domains A and B no domain hosts the MAC (mac_odd): its
// key, tag and pad are values of the binary field the compile profile
// names (CompileProfile::security: GF(2^128) classical, GF(2^256)
// post-quantum), which the program does not list and no domain commits.
// The pad's polynomial bits are copied into both domains, the prover sends
// the masked tag T, and each odd side is the A side above, so both sides'
// tags equal T.
//
// The per-chunk MAC ablation (CompileProfile::unsound_per_chunk_mac, a
// measurement control) lowers the binary/odd MAC to Longfellow's per-chunk
// MAC instead (per_chunk_mac below).

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_MAC_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_MAC_H_

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <vector>

#include "gf2k/gf2_128.h"
#include "gf2k/gf2_256.h"
#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/compiler/derivation.h"
#include "gordiehowe/compiler/mod.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::compiler {

// The MAC's A accumulators acc[b] = SUMS[b] + BLIND[b] as elements of FA,
// each checked below FA's characteristic P before conversion: of_scalar
// would reduce a larger one modulo P (a native F_q field) and the honest
// accumulator would be wrong. A violation is one std::runtime_error, raised
// after the conversion (ct.h).
template <class FA>
std::vector<typename FA::Elt> mac_accumulator_elements(
    const FA &fa, Bound p, const std::vector<uint64_t> &sums,
    const std::vector<typename FA::Elt> &blind) {
  std::vector<typename FA::Elt> a(sums.size());
  check(blind.size() >= sums.size(), "mac.acc: blind bits");
  uint64_t ok = 1;
  // A p beyond 128 bits (F_p256) exceeds every 64-bit sum (a public
  // choice).
  const bool wide = !p.fits128();
  const NatInt pn = nat_modulus(p);
  for (size_t i = 0; i < sums.size(); ++i) {
    const NatInt v = NatInt(sums[i]) + ct::bit_of(fa, blind[i]);
    const uint64_t below = wide ? 1 : ct::lt128(v, pn);
    ok &= below;
    // A value at or above p converts as 0 (of_scalar may refuse it).
    a[i] = elt_of_nat(fa, v & ct::mask128(below));
  }
  if (!ok)
    throw std::runtime_error("mac.acc: an accumulator is not below the "
                             "characteristic " +
                             bound_str(p) + " of the odd domain");
  return a;
}

// The grouped accumulators: for each chunk range [a, e) of GROUPS, the
// integer sums reduce(sum_{c in [a, e)} X_c * R_c) of 0/1 inputs
// (mac_integer_accumulators over the range), as elements of FA, each
// checked below FA's characteristic P. A violation is one
// std::runtime_error, raised after every group (ct.h).
template <class MF, class FA>
std::vector<typename FA::Elt> mac_grouped_accumulator_elements(
    const FA &fa, Bound p, const std::vector<uint8_t> &x,
    const std::vector<typename MF::Elt> &r, const std::vector<size_t> &taps,
    const std::vector<std::pair<size_t, size_t>> &groups) {
  constexpr size_t w = MF::kBits;
  std::vector<typename FA::Elt> out;
  out.reserve(groups.size() * w);
  uint64_t ok = 1;
  const bool wide = !p.fits128();
  const NatInt pn = nat_modulus(p);
  for (const auto &[a, e] : groups) {
    const std::vector<uint8_t> xg(x.begin() + long(a * w),
                                  x.begin() + long(e * w));
    const std::vector<typename MF::Elt> rg(r.begin() + long(a),
                                           r.begin() + long(e));
    const auto sum = ops::mac_integer_accumulators<MF>(xg, rg, taps);
    for (size_t i = 0; i < w; ++i) {
      const uint64_t below = wide ? 1 : ct::lt128(NatInt(sum[i]), pn);
      ok &= below;
      out.push_back(elt_of_nat(fa, NatInt(sum[i]) & ct::mask128(below)));
    }
  }
  if (!ok)
    throw std::runtime_error("mac.acc: a group's accumulator is not below "
                             "the characteristic " +
                             bound_str(p) + " of the odd domain");
  return out;
}

// The MAC's integer side reads each accumulator coefficient, at most the
// width W, as its centered representative, and the congruence mod 2 holds
// only if that is the coefficient itself: W <= (p - 1)/2, so FA's
// characteristic must exceed 2W. FA is always odd (E1 puts the binary domain
// on H, which takes no integer reading), and a characteristic above 2^128
// (F_p256) exceeds every width. WHAT names the equality, DOMAIN FA's domain.
template <class FA>
void mac_require_centered(const FA &fa, size_t w, const std::string &what,
                          const std::string &domain) {
  if (characteristic_above(fa, Bound(2 * w))) return;
  fail(what + ": the characteristic " + bound_str(field_characteristic(fa)) +
       " of the odd domain " + domain + " is not above 2w = " +
       std::to_string(2 * w) + "; the MAC needs p > 2w so that each "
       "accumulator coefficient (at most w) is its own centered "
       "representative");
}

// The reduction table of Logic::gf2k_mul for the field of width W whose
// x^W is the sum of x^tap over TAPS: entry i lists the coefficients of the
// product polynomial (degree at most 2W - 2) whose sum mod 2 is the
// coefficient of x^i of the reduced product, ascending: i itself and every
// k >= W with x^i in the support of x^k mod phi (ops::mac_reduction).
// Longfellow's Logic::gf2_128_mul table at GF(2^128).
inline std::vector<std::vector<uint16_t>> per_chunk_mac_reduction(
    size_t w, const std::vector<size_t> &taps) {
  const auto red = ops::mac_reduction(w, taps);
  std::vector<std::vector<uint16_t>> m(w);
  for (size_t i = 0; i < w; ++i) m[i].push_back(uint16_t(i));
  for (size_t k = w; k <= 2 * w - 2; ++k)
    for (size_t b : red[k - w]) m[b].push_back(uint16_t(k));
  return m;
}

template <class S>
class EqualityLoweringImpl : Lowering {
 public:
  // MEMBERS: the (x, y) node pairs of the equalities this lowering merges
  // into one MAC (X, Y's own first).
  template <class F1, class F2>
  static void run(ConstraintSystemBuilder<S> &b, Ref<F1> x, Ref<F2> y,
                  const std::vector<std::pair<size_t, size_t>> &members,
                  size_t index) {
    const auto &N = b.system().graph().nodes;
    const Node &nx = N.at(x.id), &ny = N.at(y.id);
    const std::string what =
        "assert_same_bits(" + nx.name + ", " + ny.name + ")";
    if (nx.domain < 0 && ny.domain < 0)
      fail(what + ": both sides are public values");
    if (nx.n != ny.n)
      fail(what + ": lengths " + std::to_string(nx.n) + " and " +
           std::to_string(ny.n) + " differ");
    // One domain (a public side belongs to the other's domain).
    if (nx.domain < 0 || ny.domain < 0 || nx.domain == ny.domain)
      fail(what + ": the two sides lie in different fields of one domain");
    const auto &D = b.system().domains();
    const std::string d1 = D.at(nx.domain)->name, d2 = D.at(ny.domain)->name;
    // E1: orientation. H is the binary domain, A the odd one.
    if constexpr (!F1::kCharacteristicTwo && !F2::kCharacteristicTwo) {
      // Two odd domains: the MAC over the profile's binary field, which no
      // domain hosts (mac_odd).
      std::vector<Ref<F1>> xs;
      std::vector<Ref<F2>> ys;
      std::vector<std::string> names;
      auto &d1t = typed<F1>(b, nx.domain);
      auto &d2t = typed<F2>(b, ny.domain);
      for (const auto &[u, v] : members) {
        const bool fwd = N.at(u).domain == nx.domain;
        const size_t a = fwd ? u : v, c = fwd ? v : u;
        xs.push_back(ref_of(d1t, a));
        ys.push_back(ref_of(d2t, c));
        names.push_back("assert_same_bits(" + N.at(u).name + ", " +
                        N.at(v).name + ")");
        if (N.at(a).n != N.at(c).n)
          fail(names.back() + ": lengths " + std::to_string(N.at(a).n) +
               " and " + std::to_string(N.at(c).n) + " differ");
      }
      mac_odd(b, xs, ys, names, index);
    } else if constexpr (F1::kCharacteristicTwo && F2::kCharacteristicTwo) {
      fail(what + ": domains " + d1 + " (characteristic 2) and " + d2 +
           " (characteristic 2); the MAC equality needs one binary and one "
           "odd-characteristic domain; binary/binary equality is not "
           "implemented");
    } else {
      // The members' sides, X's domain first.
      std::vector<Ref<F1>> xs;
      std::vector<Ref<F2>> ys;
      std::vector<std::string> names;
      auto &d1t = typed<F1>(b, nx.domain);
      auto &d2t = typed<F2>(b, ny.domain);
      for (const auto &[u, v] : members) {
        const bool fwd = N.at(u).domain == nx.domain;
        const size_t a = fwd ? u : v, c = fwd ? v : u;
        xs.push_back(ref_of(d1t, a));
        ys.push_back(ref_of(d2t, c));
        names.push_back("assert_same_bits(" + N.at(u).name + ", " +
                        N.at(v).name + ")");
        if (N.at(a).n != N.at(c).n)
          fail(names.back() + ": lengths " + std::to_string(N.at(a).n) +
               " and " + std::to_string(N.at(c).n) + " differ");
      }
      if constexpr (F1::kCharacteristicTwo)
        mac(b, xs, ys, names, index);
      else
        mac(b, ys, xs, names, index);
    }
  }

 private:
  template <class F>
  static std::string characteristic(const F &f) {
    try {
      return bound_str(field_characteristic(f));
    } catch (const CompileError &) {
      return "p > 2^128";
    }
  }

  template <class F>
  static Domain<F> &typed(ConstraintSystemBuilder<S> &b, int d) {
    auto *t = dynamic_cast<Domain<F> *>(
        b.system().domains().at(d).get());
    if (t == nullptr) fail("assert_same_bits: a domain of another field");
    return *t;
  }

  // Whether an affine row reads node ID of domain D: no value only a
  // circuit reads, directly or through the domain's derived and bound
  // views.
  template <class F>
  static bool affine_readable(const Domain<F> &d, const std::vector<Node> &N,
                              size_t id) {
    if (d.circuit_only(id)) return false;
    const Node &n = N.at(id);
    if (n.domain != d.index) return true;
    const auto b = d.bindings().find(id);
    const Lin<F> *e = b != d.bindings().end() ? &b->second
                      : n.kind == Kind::kDerived ? &d.lin(id)
                                                 : nullptr;
    if (e == nullptr) return true;
    for (const auto &t : e->terms)
      if (!affine_readable(d, N, t.node)) return false;
    return true;
  }

  // ivl (leaf of NODE) 0 1 for a Bit operand of the MAC (its own source,
  // or a joined side's masked parts), the fact the MAC lemma reads.
  static size_t bit_ivl(Deriv &dv, const Graph &g, size_t node,
                        std::map<size_t, size_t> &done) {
    IvlWhy w;
    w.kind = IvlWhy::kBit;
    const std::map<size_t, IvlWhy> why{{node, w}};
    return dv.ivl_expr(ivl_premises(dv, g, {node}, why, done), dx::leaf(node),
                       SignedInt(0), SignedInt(1));
  }

  // The members' sides as one value: the side itself for one member, a
  // concatenation view named NM otherwise.
  template <class F>
  static Ref<F> joined(const std::vector<Ref<F>> &xs, const std::string &nm) {
    if (xs.size() == 1) return xs[0];
    ViewSource src;
    for (const auto &x : xs)
      for (size_t i = 0; i < x.n; ++i) src.push_back({x.id, i});
    return xs[0].view_of(src, {src.size()}).named(nm);
  }

  // The MAC equality, the sides XH in the binary domain H and XA in A, one
  // pair per member equality (WHAT names them).
  template <class FH, class FA>
  static void mac(ConstraintSystemBuilder<S> &b, const std::vector<Ref<FH>> &xhs,
                  const std::vector<Ref<FA>> &xas,
                  const std::vector<std::string> &whats, size_t index) {
    using HE = typename FH::Elt;
    using AE = typename FA::Elt;
    auto &s = b.system();
    const auto &N = s.graph().nodes;
    auto &H = typed<FH>(b, N.at(xhs[0].id).domain);
    auto &A = typed<FA>(b, N.at(xas[0].id).domain);
    const FH &fh = H.field();
    const FA &fa = A.field();
    std::string what = whats[0];
    for (size_t k = 1; k < whats.size(); ++k) what += ", " + whats[k];
    // E2: Bit values; E4: no bit view on the A side.
    for (size_t k = 0; k < xhs.size(); ++k) {
      for (size_t id : {xhs[k].id, xas[k].id})
        if (N.at(id).type.base != Base::kBit)
          fail(whats[k] + ": '" + N.at(id).name + "' has type " +
               type_name(N.at(id).type) + "; the MAC equality compares Bit "
               "values (cells or bit views)");
      if (N.at(xas[k].id).kind == Kind::kBitView)
        fail(whats[k] + ": '" + N.at(xas[k].id).name + "' of the odd domain " +
             A.name + " is a bit view; the MAC's A rows read cells or "
             "derived views");
    }
    // E3: the MAC basis of H's field.
    const size_t w = FH::kBits;
    const MacBasis *basis = nullptr;
    for (const auto &mb : b.profile().mac_bases)
      if (mb.w == w) basis = &mb;
    if (basis == nullptr)
      fail(what + ": the compile profile names no MAC basis of width " +
           std::to_string(w) + " (the bits of domain " + H.name + ")");
    {
      const auto taps = ops::mac_taps(fh);
      std::vector<size_t> want(basis->taps.begin(), basis->taps.end());
      std::sort(want.begin(), want.end());
      if (taps != want)
        fail(what + ": x^" + std::to_string(w) + " in the field of domain " +
             H.name + " differs from the profile's MAC basis");
    }
    const std::string pre = index == 0 ? "mac" : "mac" + std::to_string(index);
    const Ref<FH> xh = joined(xhs, pre + ".xh");
    const Ref<FA> xa = joined(xas, pre + ".xa");
    if (b.profile().unsound_per_chunk_mac) {
      per_chunk_mac(b, H, A, xh, xa, *basis, whats, pre);
      return;
    }
    const size_t len = xh.n;
    const size_t nch = (len + w - 1) / w;
    // The accumulators are checked below p.
    const Bound p = field_characteristic(fa);
    const uint64_t conv_max = ops::mac_conv_max(fh);
    const Bound acc_max = ops::mac_acc_max(fh, nch);
    // p > 2w, so that each accumulator coefficient is its own centered
    // representative (lem:core-mod). acc_max < p and the groups' bounds
    // imply it only through convMax >= 2w, a property of the basis.
    mac_require_centered(fa, w, what, A.name);

    auto B = pad(s, H, Field{}, 1);
    auto B_A = pad_copy(A, pre + ".blind", B,
                        PadMap<FH, FA>::polynomial_bits(fa));
    // Tests X_H, X_A, B and B_A (inferred from the rows below: B as the
    // pad of U).
    auto beta = s[H].challenge(pre + ".beta");
    realization(H, beta);
    const FH *ph = &fh;
    const FA *pa = &fa;
    auto r = s[H].pub(Field{}, pre + ".powers", nch, depends_on(beta),
                              computes("chunk_powers", {nch}),
                              [ph, nch](const std::vector<HE> &bb) {
                                std::vector<HE> r(nch);
                                HE a = bb[0];
                                for (auto &v : r) {
                                  v = a;
                                  a = ph->mulf(a, bb[0]);
                                }
                                return r;
                              });
    // x^i in the polynomial basis.
    std::vector<HE> xp(w);
    xp[0] = fh.one();
    for (size_t i = 1; i < w; ++i) xp[i] = fh.mulf(xp[i - 1], fh.of_scalar_field(0b10));
    // X_H as chunks: [nch][w], the last chunk zero-extended.
    const Ref<FH> X =
        (len == nch * w ? xh : xh.zero_extend(nch * w)).reshape({nch, w});
    auto U = priv(H, Field{}, pre + ".value", 1, depends_on(X, r),
                      [ph, xp](const Tensor<HE> &chunks,
                               const Tensor<HE> &r) {
                        HE u = ph->zero();
                        for (size_t c = 0; c < r.size(); ++c) {
                          const auto bits = chunks.row(c);
                          HE chunk = ph->zero();
                          for (size_t i = 0; i < bits.size(); ++i)
                            ph->add(chunk,
                                    ct::select(ct::mask(ct::bit_of(*ph, bits[i])),
                                               xp[i], ph->zero()));
                          ph->add(u, ph->mulf(chunk, r[c]));
                        }
                        return std::vector<HE>{u};
                      },
                      masked_by(B));
    auto T = public_message(s, U);
    Computes cb{"CoefficientBits", {}};
    put_u64(cb.params, basis->w);
    put_u64(cb.params, basis->taps.size());
    for (unsigned t : basis->taps) put_u64(cb.params, t);
    auto bitsT = s[A].pub(Bit{}, pre + ".target_bits", w, depends_on(T),
                                  cb, [pa, w](const std::vector<HE> &t) {
                                    std::vector<AE> out(w);
                                    for (size_t i = 0; i < w; ++i)
                                      out[i] = t[0][i] ? pa->one() : pa->zero();
                                    return out;
                                  });
    // U = sum_c r_c chunk_c(X_H), chunk_c = sum_i x^i X_H[c][i]: affine in
    // the bits, the coefficients r_c x^i public after beta, so placement
    // puts it on the linear test. When X_H reads a value only a circuit
    // reads (a hash output computed in the circuit), the compiler's own
    // circuit states it: the same predicate placed in the circuit is
    // slower on the post-quantum mDL.
    const bool h_affine = affine_readable(H, N, X.id);
    if (h_affine) {
      const Expr<FH> chunks = Expr<FH>(X).from_digits(xp[1]);
      const Expr<FH> mac_sum = (Expr<FH>(r) * chunks).sum();
      add_predicate(H, pre + ".H",
                    expr_internal::binary(ExprOp::kAdd, Expr<FH>(U).node,
                                          expr_internal::scale(mac_sum.node,
                                                               fh.mone()),
                                          "mac"),
                    std::make_shared<Placement>(Placement::kAuto));
    } else {
      // The closure's key (the compile cache): the powers of x.
      std::vector<uint8_t> key;
      put_str(key, "mac.H");
      put_u64(key, xp.size());
      for (const auto &x : xp) {
        std::vector<uint8_t> b(FH::kBytes);
        fh.to_bytes_field(b.data(), x);
        key.insert(key.end(), b.begin(), b.end());
      }
      gkr(s, pre + ".H", depends_on(X, r, U),
          [xp](const auto &lc, const auto &chunks, const auto &r,
               const auto &u) {
            std::optional<size_t> sum;
            for (size_t c = 0; c < r.size(); ++c) {
              const auto bits = chunks.row(c);
              std::optional<size_t> chunk;
              for (size_t i = 0; i < bits.size(); ++i) {
                const size_t t = lc.mul(xp[i], bits[i]);
                chunk = chunk ? lc.add(*chunk, t) : t;
              }
              const size_t t = lc.mul(*chunk, r[c]);
              sum = sum ? lc.add(*sum, t) : t;
            }
            lc.assert_eq(u[0], *sum);
          },
          key);
    }
    const auto groups =
        tail(b, A, pre, xa, Ref<FH>(r), Ref<FA>(B_A), bitsT, nch, conv_max);

    // Summary.
    auto &sum = b.summary();
    std::string line = "MAC " + pre + ": " + std::to_string(whats.size()) +
                       (whats.size() == 1 ? " equality, " : " equalities, ") +
                       what + "; H = " + H.name + ", A = " + A.name + ", w = " +
                       std::to_string(w) + ", nch = " + std::to_string(nch) +
                       ", convMax = " + std::to_string(conv_max) +
                       ", acc_max = " + bound_str(acc_max) +
                       (acc_max < p ? " < p" : " >= p (grouped)") +
                       "; tail assert_mod '" + pre + "'";
    sum.report.push_back(line);
    put_str(sum.descr, pre);
    put_u64(sum.descr, xhs.size());
    for (size_t k = 0; k < xhs.size(); ++k) {
      put_u64(sum.descr, xhs[k].id);
      put_u64(sum.descr, xas[k].id);
    }
    put_u64(sum.descr, basis->w);
    for (unsigned t : basis->taps) put_u64(sum.descr, t);
    put_u64(sum.descr, nch);
    put_bound(sum.descr, acc_max);
    PlanRecords::Mac rec;
    rec.name = pre;
    rec.tag_domain = H.name;
    rec.acc_domain = A.name;
    rec.challenge = s.graph().nodes.at(beta.id).name;
    rec.width = w;
    rec.nch = nch;
    rec.taps = ops::mac_taps(fh);
    rec.conv_max = conv_max;
    rec.acc_max = acc_max;
    rec.tail = pre;
    rec.groups = groups;
    rec.xh = xh.id;
    rec.xa = xa.id;
    rec.tag = U.id;
    rec.pad = B.id;
    rec.blind = B_A.id;
    rec.key = beta.id;
    rec.powers = r.id;
    (h_affine ? rec.h_predicate : rec.h_circuit) = pre + ".H";
    if (whats.size() > 1) rec.members = whats;
    // The cross equal's derivation: the MAC lemma, from its tail and its
    // H predicate (none when the compiler's circuit states H).
    {
      Deriv dv(pre + ".equal", A.name);
      std::map<size_t, size_t> done;
      dv.in_domain(A.name);
      const size_t iy = bit_ivl(dv, s.graph(), xa.id, done);
      const size_t ib = bit_ivl(dv, s.graph(), B_A.id, done);
      dv.in_domain("");
      dv.mac({rec.tail}, rec.h_predicate, {iy, ib});
      dv.commit(b.records());
    }
    b.records().macs.push_back(rec);
    // r_c = beta^(c+1), c < nch: the binding event has degree nch.
    b.records().charges.push_back({rec.challenge, Bound(nch)});
  }

  // The per-chunk MAC ablation (CompileProfile::unsound_per_chunk_mac), a
  // measurement control: Longfellow's MAC (longfellow-baselines
  // lib/circuits/mac/mac_circuit.h: MACGF2 in the binary circuit, MAC in
  // the odd one) in place of the polynomial MAC, between the sides XH of
  // the binary domain H and XA of the odd domain A. With w = FH::kBits and
  // each side split into nch chunks of w bits (the last zero-extended),
  // chunk_c(X) = sum_i x^i X[c][i]:
  //
  //   a      key shares, nch elements of H: a key pad (Lowering::key_pad),
  //          committed in phase 0, uniform from the prover's random engine
  //          (MACReference::sample)
  //   a_A    the polynomial-basis bits of a in A, Bit nch w, a pad copy
  //   beta   the verifier's key share, a challenge of H
  //   kbits  public: beta's polynomial-basis bits in A, Bit w
  //   V      late value of H, V_c = (beta + a_c) chunk_c(X_H), masked by a
  //          zero pad, so its message T, the tags, is sent in the clear
  //   tbits  public: the tags' polynomial-basis bits in A, Bit [nch][w]
  //
  // H's circuit checks V_c = (beta + a_c) chunk_c(X_H), a field product
  // (MACGF2::verify_mac). A's circuit checks tbits_c = (kbits xor a_A,c)
  // X_A,c in GF(2^w) (MAC::assert_mac): Logic::gf2k_mul, Karatsuba on bit
  // vectors and then reduction modulo the field polynomial. Both checks
  // are GKR circuits. The emulated product has degree 2 in committed bits
  // at each AND and grows at each XOR, so no affine row or batch states
  // it, and quadratic triples would commit a cell per AND and per XOR; the
  // circuit commits only the key bits.
  //
  // a, a_A, X_H, X_A and V's pad are fixed before beta, so for
  // chunk_c(X_H) != chunk_c(X_A) both checks hold for at most one beta:
  // the charge is nch, as the polynomial MAC's. A zero chunk has the tag
  // zero, so the tags reveal which chunks are zero: the system is not
  // zero-knowledge.
  template <class FH, class FA>
  static void per_chunk_mac(ConstraintSystemBuilder<S> &b, Domain<FH> &H,
                            Domain<FA> &A, Ref<FH> xh, Ref<FA> xa,
                            const MacBasis &basis,
                            const std::vector<std::string> &whats,
                            const std::string &pre) {
    using HE = typename FH::Elt;
    using AE = typename FA::Elt;
    auto &s = b.system();
    const FH &fh = H.field();
    const FA &fa = A.field();
    std::string what = whats[0];
    for (size_t k = 1; k < whats.size(); ++k) what += ", " + whats[k];
    const size_t w = FH::kBits, len = xh.n;
    const size_t nch = (len + w - 1) / w;
    const FH *ph = &fh;
    const FA *pa = &fa;
    // The sides as chunks: [nch][w], the last chunk zero-extended.
    const Ref<FH> X =
        (len == nch * w ? xh : xh.zero_extend(nch * w)).reshape({nch, w});
    const Ref<FA> XA =
        (len == nch * w ? xa : xa.zero_extend(nch * w)).reshape({nch, w});

    // The prover's key shares, one per chunk: a key pad, which the core
    // draws with the other pads from the prover's random engine, and its
    // polynomial bits in A.
    auto a = key_pad(s, H, pre + ".key_share", Field{}, nch);
    auto a_A = pad_copy(A, pre + ".key_share_bits", a,
                        PadMap<FH, FA>::polynomial_bits(fa));
    // Tests X_H, X_A, a, a_A and V's pad (inferred from the circuits).
    auto beta = s[H].challenge(pre + ".beta");
    realization(H, beta);
    Computes cb{"CoefficientBits", {}};
    put_u64(cb.params, basis.w);
    put_u64(cb.params, basis.taps.size());
    for (unsigned t : basis.taps) put_u64(cb.params, t);
    auto kbits = s[A].pub(Bit{}, pre + ".beta_bits", w, depends_on(beta), cb,
                          [pa, w](const std::vector<HE> &k) {
                            std::vector<AE> out(w);
                            for (size_t i = 0; i < w; ++i)
                              out[i] = k[0][i] ? pa->one() : pa->zero();
                            return out;
                          });
    // x^i in the polynomial basis.
    std::vector<HE> xp(w);
    xp[0] = fh.one();
    for (size_t i = 1; i < w; ++i)
      xp[i] = fh.mulf(xp[i - 1], fh.of_scalar_field(0b10));
    // The tags, sent in the clear (a zero pad).
    auto Z = zero_pad(s, H, Field{}, nch);
    auto V = priv(H, Field{}, pre + ".tag", nch, depends_on(X, a, beta),
                  [ph, xp](const Tensor<HE> &chunks, const Tensor<HE> &k,
                           const Tensor<HE> &bb) {
                    std::vector<HE> out(k.size());
                    for (size_t c = 0; c < k.size(); ++c) {
                      const auto bits = chunks.row(c);
                      HE chunk = ph->zero();
                      for (size_t i = 0; i < bits.size(); ++i)
                        ph->add(chunk, ct::select(
                                           ct::mask(ct::bit_of(*ph, bits[i])),
                                           xp[i], ph->zero()));
                      out[c] = ph->mulf(ph->addf(bb[0], k[c]), chunk);
                    }
                    return out;
                  },
                  masked_by(Z));
    auto T = public_message(s, V);
    auto tbits = s[A].pub(Bit{}, pre + ".target_bits", Shape{nch, w},
                          depends_on(T), cb,
                          [pa, w](const std::vector<HE> &t) {
                            std::vector<AE> out(t.size() * w);
                            for (size_t c = 0; c < t.size(); ++c)
                              for (size_t i = 0; i < w; ++i)
                                out[c * w + i] =
                                    t[c][i] ? pa->one() : pa->zero();
                            return out;
                          });

    // H: V_c = (beta + a_c) chunk_c(X_H). The closure's key (the compile
    // cache): the powers of x.
    std::vector<uint8_t> hkey;
    put_str(hkey, "mac.per_chunk.H");
    put_u64(hkey, xp.size());
    for (const auto &x : xp) {
      std::vector<uint8_t> e(FH::kBytes);
      fh.to_bytes_field(e.data(), x);
      hkey.insert(hkey.end(), e.begin(), e.end());
    }
    gkr(s, pre + ".H", depends_on(X, a, beta, V),
        [xp](const auto &lc, const auto &chunks, const auto &k,
             const auto &bb, const auto &v) {
          for (size_t c = 0; c < k.size(); ++c) {
            const auto bits = chunks.row(c);
            std::optional<size_t> chunk;
            for (size_t i = 0; i < bits.size(); ++i) {
              const size_t t = lc.mul(xp[i], bits[i]);
              chunk = chunk ? lc.add(*chunk, t) : t;
            }
            const size_t key = lc.add(bb[0], k[c]);
            lc.assert_eq(v[c], lc.mul(key, *chunk));
          }
        },
        hkey);

    // A: tbits_c = (kbits xor a_A,c) X_A,c in GF(2^w). The closure's key:
    // the width and the taps.
    const auto taps = ops::mac_taps(fh);
    const auto red = per_chunk_mac_reduction(w, taps);
    std::vector<uint8_t> akey;
    put_str(akey, "mac.per_chunk.A");
    put_u64(akey, w);
    put_u64(akey, taps.size());
    for (size_t t : taps) put_u64(akey, t);
    gkr(s, pre + ".A", depends_on(XA, a_A, kbits, tbits),
        [w, nch, red](const auto &lc, const auto &x, const auto &ka,
                      const auto &kb, const auto &t) {
          using L = std::decay_t<decltype(lc)>;
          using BitW = typename L::BitW;
          for (size_t c = 0; c < nch; ++c) {
            const auto xr = x.row(c);
            const auto tr = t.row(c);
            std::vector<BitW> key(w), xx(w), prod(w);
            for (size_t j = 0; j < w; ++j) {
              key[j] =
                  lc.lxor(BitW(kb[j], lc.f_), BitW(ka[c * w + j], lc.f_));
              xx[j] = BitW(xr[j], lc.f_);
            }
            lc.gf2k_mul(prod.data(), key.data(), xx.data(), red.data(), w);
            for (size_t j = 0; j < w; ++j)
              lc.assert_eq(lc.eval(prod[j]), tr[j]);
          }
        },
        akey);

    // Summary.
    auto &sum = b.summary();
    sum.report.push_back(
        "MAC " + pre + " (per-chunk ablation, not zero-knowledge): " +
        std::to_string(whats.size()) +
        (whats.size() == 1 ? " equality, " : " equalities, ") + what +
        "; H = " + H.name + ", A = " + A.name + ", w = " + std::to_string(w) +
        ", nch = " + std::to_string(nch) + "; key shares '" + pre +
        ".key_share', tags '" + pre + ".tag' in the clear; circuits '" + pre +
        ".H' (field product) and '" + pre +
        ".A' (Karatsuba product and reduction)");
    put_str(sum.descr, pre);
    put_str(sum.descr, "per-chunk");
    put_u64(sum.descr, whats.size());
    put_u64(sum.descr, xh.id);
    put_u64(sum.descr, xa.id);
    put_u64(sum.descr, basis.w);
    for (unsigned t : basis.taps) put_u64(sum.descr, t);
    put_u64(sum.descr, nch);
    // Each chunk's tags agree for unequal chunks at one beta: nch events.
    b.records().charges.push_back(
        {s.graph().nodes.at(beta.id).name, Bound(nch)});
  }

  // The MAC field object of type MF, one per process: the odd MAC's key,
  // tag and pad are values of MF, which no domain hosts.
  template <class MF>
  static const MF &mac_field() {
    static const MF *f = new MF;
    return *f;
  }

  // The MAC equality between two odd domains A and B, the sides XAS in A
  // and XBS in B, one pair per member equality (WHATS names them). The MAC
  // field M is the compile profile's (CompileProfile::odd_mac_bits), whose
  // width must have a MAC basis in the profile; no domain commits its
  // values.
  // With a pad P uniform in M, whose polynomial bits both domains copy
  // (P_A, P_B, committed in phase 0):
  //   beta   challenge in M; r_c = beta^(c+1)
  //   U      late value of M masked by P, U = sum_c chunk_c(X_A) r_c; its
  //          message T = U + P
  //   A, B   each the binary path's odd side (tail):
  //          bits(T) = P_D + sum_c MACConv(r_c)(X_D,c) mod 2, the popcount
  //          accumulators reduced mod 2
  // Both sides' tags equal T. P_A and P_B are fixed before beta, so for
  // X_A != X_B both hold for at most nch values of beta (the charge, as in
  // the binary path), and T is uniform because P is.
  template <class FA, class FB>
  static void mac_odd(ConstraintSystemBuilder<S> &b,
                      const std::vector<Ref<FA>> &xas,
                      const std::vector<Ref<FB>> &xbs,
                      const std::vector<std::string> &whats, size_t index) {
    if (b.profile().unsound_per_chunk_mac)
      fail(whats[0] + ": the per-chunk MAC ablation "
           "(CompileProfile::unsound_per_chunk_mac) lowers equalities "
           "between a binary and an odd domain only; this one is between "
           "two odd domains");
    const size_t w = b.profile().odd_mac_bits();
    const MacBasis *basis = nullptr;
    for (const auto &mb : b.profile().mac_bases)
      if (mb.w == w) basis = &mb;
    if (basis == nullptr)
      fail(whats[0] + ": an equality between two odd domains takes its MAC "
           "field from the compile profile, GF(2^" + std::to_string(w) +
           ") for profile '" + b.profile().name + "', which names no MAC "
           "basis of width " + std::to_string(w));
    if (w == 128)
      mac_odd_field<GF2_128<>>(b, *basis, xas, xbs, whats, index);
    else
      mac_odd_field<GF2_256<>>(b, *basis, xas, xbs, whats, index);
  }

  // mac_odd_in over MF, a field of S's field set (internal::WithMacFields
  // adds it to every set of two odd fields or more).
  template <class MF, class FA, class FB>
  static void mac_odd_field(ConstraintSystemBuilder<S> &b,
                            const MacBasis &basis,
                            const std::vector<Ref<FA>> &xas,
                            const std::vector<Ref<FB>> &xbs,
                            const std::vector<std::string> &whats,
                            size_t index) {
    if constexpr (S::template kContains<MF>)
      mac_odd_in<MF>(b, basis, xas, xbs, whats, index);
    else
      fail(whats[0] + ": the MAC field is not in the system's field set");
  }

  template <class MF, class FA, class FB>
  static void mac_odd_in(ConstraintSystemBuilder<S> &b, const MacBasis &basis,
                         const std::vector<Ref<FA>> &xas,
                         const std::vector<Ref<FB>> &xbs,
                         const std::vector<std::string> &whats,
                         size_t index) {
    using ME = typename MF::Elt;
    using AE = typename FA::Elt;
    using BE = typename FB::Elt;
    auto &s = b.system();
    const auto &N = s.graph().nodes;
    auto &A = typed<FA>(b, N.at(xas[0].id).domain);
    auto &B = typed<FB>(b, N.at(xbs[0].id).domain);
    const MF &mf = mac_field<MF>();
    const FA &fa = A.field();
    const FB &fb = B.field();
    std::string what = whats[0];
    for (size_t k = 1; k < whats.size(); ++k) what += ", " + whats[k];
    // Bit values; affine rows read both sides, so neither is a bit view.
    for (size_t k = 0; k < xas.size(); ++k)
      for (size_t id : {xas[k].id, xbs[k].id}) {
        if (N.at(id).type.base != Base::kBit)
          fail(whats[k] + ": '" + N.at(id).name + "' has type " +
               type_name(N.at(id).type) + "; the MAC equality compares Bit "
               "values (cells or bit views)");
        if (N.at(id).kind == Kind::kBitView)
          fail(whats[k] + ": '" + N.at(id).name + "' is a bit view; the "
               "MAC's odd rows read cells or derived views");
      }
    {
      const auto taps = ops::mac_taps(mf);
      std::vector<size_t> want(basis.taps.begin(), basis.taps.end());
      std::sort(want.begin(), want.end());
      if (taps != want)
        fail(what + ": x^" + std::to_string(MF::kBits) + " in the MAC field "
             "differs from the profile's MAC basis");
    }
    const std::string pre = index == 0 ? "mac" : "mac" + std::to_string(index);
    const Ref<FA> xa = joined(xas, pre + ".xa");
    const Ref<FB> xb = joined(xbs, pre + ".xb");
    const size_t w = MF::kBits, len = xa.n;
    const size_t nch = (len + w - 1) / w;
    const uint64_t conv_max = ops::mac_conv_max(mf);
    const Bound acc_max = ops::mac_acc_max(mf, nch);
    // p > 2w on both odd sides, so that each accumulator coefficient is its
    // own centered representative (lem:core-mod), as in mac.
    mac_require_centered(fa, w, what, A.name);
    mac_require_centered(fb, w, what, B.name);

    Domain<MF> &M = bare_field(s, mf);
    auto P = pad(s, M, Field{}, 1);
    auto P_A = pad_copy(A, pre + ".blind:" + A.name, P,
                        PadMap<MF, FA>::polynomial_bits(fa));
    auto P_B = pad_copy(B, pre + ".blind:" + B.name, P,
                        PadMap<MF, FB>::polynomial_bits(fb));
    // Tests both sides and both blinds (inferred from the odd rows).
    auto beta = challenge(s, mf, pre + ".beta");
    realization(M, beta);
    const MF *pm = &mf;
    auto r = pub(s, mf, Field{}, pre + ".powers", nch, depends_on(beta),
                 computes("chunk_powers", {nch}),
                 [pm, nch](const std::vector<ME> &bb) {
                   std::vector<ME> r(nch);
                   ME a = bb[0];
                   for (auto &v : r) {
                     v = a;
                     a = pm->mulf(a, bb[0]);
                   }
                   return r;
                 });
    // x^i in the polynomial basis.
    std::vector<ME> xp(w);
    xp[0] = mf.one();
    for (size_t i = 1; i < w; ++i)
      xp[i] = mf.mulf(xp[i - 1], mf.of_scalar_field(0b10));
    const FA *pa = &fa;
    const FB *pb = &fb;
    auto U = priv(M, Field{}, pre + ".value", 1, depends_on(xa, r),
                  [pm, pa, xp, len, w](const std::vector<AE> &x,
                                       const std::vector<ME> &r) {
                    ME u = pm->zero();
                    for (size_t c = 0; c < r.size(); ++c) {
                      ME chunk = pm->zero();
                      for (size_t i = 0; i < w && c * w + i < len; ++i)
                        pm->add(chunk,
                                ct::select(ct::mask(ct::bit_of(*pa, x[c * w + i])),
                                           xp[i], pm->zero()));
                      pm->add(u, pm->mulf(chunk, r[c]));
                    }
                    return std::vector<ME>{u};
                  },
                  masked_by(P));
    auto T = public_message(s, U);
    Computes cb{"CoefficientBits", {}};
    put_u64(cb.params, basis.w);
    put_u64(cb.params, basis.taps.size());
    for (unsigned t : basis.taps) put_u64(cb.params, t);
    auto bits_a = s[A].pub(Bit{}, pre + ".target_bits:" + A.name, w,
                           depends_on(T), cb,
                           [pa, w](const std::vector<ME> &t) {
                             std::vector<AE> out(w);
                             for (size_t i = 0; i < w; ++i)
                               out[i] = t[0][i] ? pa->one() : pa->zero();
                             return out;
                           });
    auto bits_b = s[B].pub(Bit{}, pre + ".target_bits:" + B.name, w,
                           depends_on(T), cb,
                           [pb, w](const std::vector<ME> &t) {
                             std::vector<BE> out(w);
                             for (size_t i = 0; i < w; ++i)
                               out[i] = t[0][i] ? pb->one() : pb->zero();
                             return out;
                           });
    const std::string pre_a = pre + "." + A.name, pre_b = pre + "." + B.name;
    const auto groups_a = tail(b, A, pre_a, xa, Ref<MF>(r), Ref<FA>(P_A),
                               bits_a, nch, conv_max);
    const auto groups_b = tail(b, B, pre_b, xb, Ref<MF>(r), Ref<FB>(P_B),
                               bits_b, nch, conv_max);

    // Summary.
    auto &sum = b.summary();
    sum.report.push_back(
        "MAC " + pre + ": " + std::to_string(whats.size()) +
        (whats.size() == 1 ? " equality, " : " equalities, ") + what +
        "; two odd domains A = " + A.name + ", B = " + B.name +
        ", MAC field of w = " + std::to_string(w) + " bits (no domain), nch = " +
        std::to_string(nch) + ", convMax = " + std::to_string(conv_max) +
        ", acc_max = " + bound_str(acc_max) + "; tails assert_mod '" + pre_a +
        "', '" + pre_b + "'");
    put_str(sum.descr, pre);
    put_str(sum.descr, "odd");
    put_u64(sum.descr, xas.size());
    for (size_t k = 0; k < xas.size(); ++k) {
      put_u64(sum.descr, xas[k].id);
      put_u64(sum.descr, xbs[k].id);
    }
    put_u64(sum.descr, basis.w);
    for (unsigned t : basis.taps) put_u64(sum.descr, t);
    put_u64(sum.descr, nch);
    put_bound(sum.descr, acc_max);
    // One record per odd side, A's first, both under beta; no domain hosts
    // the tag, its pad, the key or the powers. Each record's xa is its
    // side and its blind the side's copy of the pad.
    const std::string challenge_name = N.at(beta.id).name;
    auto record = [&](const std::string &dom, const std::string &tl,
                      const std::vector<PlanRecords::Mac::Group> &groups,
                      size_t side, size_t blind) {
      PlanRecords::Mac rec;
      rec.name = pre;
      rec.tag_domain = "";
      rec.acc_domain = dom;
      rec.xa = side;
      rec.tag = U.id;
      rec.pad = P.id;
      rec.blind = blind;
      rec.key = beta.id;
      rec.powers = r.id;
      rec.challenge = challenge_name;
      rec.width = w;
      rec.nch = nch;
      rec.taps = ops::mac_taps(mf);
      rec.conv_max = conv_max;
      rec.acc_max = acc_max;
      rec.tail = tl;
      rec.groups = groups;
      if (whats.size() > 1) rec.members = whats;
      b.records().macs.push_back(rec);
    };
    record(A.name, pre_a, groups_a, xa.id, P_A.id);
    record(B.name, pre_b, groups_b, xb.id, P_B.id);
    // The cross equal's derivation: the two-tail MAC lemma, from both
    // tails.
    {
      Deriv dv(pre + ".equal", A.name);
      std::map<size_t, size_t> done;
      const size_t ix = bit_ivl(dv, b.system().graph(), xa.id, done);
      const size_t ibx = bit_ivl(dv, b.system().graph(), P_A.id, done);
      std::map<size_t, size_t> done_b;
      dv.in_domain(B.name);
      const size_t iy = bit_ivl(dv, b.system().graph(), xb.id, done_b);
      const size_t ib = bit_ivl(dv, b.system().graph(), P_B.id, done_b);
      dv.in_domain("");
      dv.mac({pre_a, pre_b}, "", {ix, ibx, iy, ib});
      dv.commit(b.records());
    }
    // r_c = beta^(c+1), c < nch: the binding event has degree nch.
    b.records().charges.push_back({challenge_name, Bound(nch)});
  }

  // The MAC's A side: assert_mod(B_A + sum_c MACConv(r_c)(X_A,c), bits(T),
  // 2), unit 0 the blind and unit 1 + c chunk c. A range of chunks is one
  // MACConv over the slice of r and the chunk rows of X_A (the whole left
  // side for the range of every unit); the accumulators are the popcounts
  // over the units' chunks.
  // Returns the groups the lowering formed (chunks and bound), for the
  // plan export; none in the one-group form.
  template <class FA, class FH, class TB, class PB>
  static std::vector<PlanRecords::Mac::Group> tail(
      ConstraintSystemBuilder<S> &b, Domain<FA> &A,
                   const std::string &pre, Ref<FA> xa, Ref<FH> r,
                   Ref<FA> B_A, Ref<FA, TB, PB> bitsT, size_t nch,
                   uint64_t conv_max) {
    using HE = typename FH::Elt;
    using AE = typename FA::Elt;
    const FA &fa = A.field();
    const size_t w = FH::kBits, len = xa.n;
    const Bound p = field_characteristic(fa);
    const FA *pa = &fa;
    const auto taps = ops::mac_taps(*r.f);
    ModSpec<FA, S> sp;
    sp.name = pre;
    sp.m = 2;
    sp.rhs = Lin<FA>(Ref<FA>(bitsT));
    sp.acc_name = pre + ".acc";
    sp.acc_row = pre + ".A";
    sp.unit_max.assign(nch + 1, conv_max);
    sp.unit_max[0] = 1;
    sp.sum = [&fa, xa, r, B_A, len, nch, w, pre](size_t a, size_t e) -> Lin<FA> {
      if (a == 0 && e == 1) return Lin<FA>(B_A);
      if (a == 0 && e == nch + 1) {
        const Lin<FA> xin = len == nch * w ? Lin<FA>(xa)
                                           : ZeroExtend(fa, len, nch * w)(xa);
        return B_A + ops::MACConv(fa, r)(xin);
      }
      check(a >= 1, "mac: a chunk range without the blind starts at unit 1");
      const std::string at =
          "[" + std::to_string(a - 1) + "," + std::to_string(e - 1) + ")";
      const Ref<FA> xg = (len == nch * w ? xa : xa.zero_extend(nch * w))
                             .reshape({nch, w})
                             .slice(a - 1, e - 1)
                             .named(pre + ".chunks" + at);
      return ops::MACConv(
          fa, r.slice(a - 1, e - 1).named(pre + ".powers" + at))(xg);
    };
    auto groups = std::make_shared<std::vector<PlanRecords::Mac::Group>>();
    const std::vector<Bound> um = sp.unit_max;
    sp.accumulate = [pa, p, len, nch, w, taps, xa, r, B_A, groups, um](
                        Domain<FA> &d, const std::string &nm,
                        const typename ModSpec<FA, S>::Ranges &ranges,
                        const Shape &shape) -> Ref<FA> {
      if (ranges.size() == 1 && ranges[0].first == 0) {
        // The whole left side: the blind and every chunk.
        return priv(d, Subfield{}, nm, shape, depends_on(xa, r, B_A),
                        [pa, p, len, nch, w, taps](
                            const std::vector<AE> &x, const std::vector<HE> &r,
                            const std::vector<AE> &bl) {
                          std::vector<uint8_t> xx(nch * w, 0);
                          for (size_t i = 0; i < len; ++i)
                            xx[i] = uint8_t(ct::bit_of(*pa, x[i]));
                          const auto sum =
                              ops::mac_integer_accumulators<FH>(xx, r, taps, p);
                          return mac_accumulator_elements(*pa, p, sum, bl);
                        });
      }
      std::vector<std::pair<size_t, size_t>> chunks;
      for (const auto &[a, e] : ranges) {
        chunks.push_back({a - 1, e - 1});
        Bound bound = 0;
        for (size_t u = a; u < e; ++u) bound = bound_add(bound, um.at(u));
        groups->push_back({a - 1, e - a, bound});
      }
      return priv(d, Subfield{}, nm, shape, depends_on(xa, r),
                      [pa, p, len, nch, w, taps, chunks](
                          const std::vector<AE> &x, const std::vector<HE> &r) {
                        std::vector<uint8_t> xx(nch * w, 0);
                        for (size_t i = 0; i < len; ++i)
                          xx[i] = uint8_t(ct::bit_of(*pa, x[i]));
                        return mac_grouped_accumulator_elements<FH>(
                            *pa, p, xx, r, taps, chunks);
                      });
    };
    lower_mod(A, b, std::move(sp));
    return *groups;
  }
};

template <class S, class F1, class F2>
void lower_equality(ConstraintSystemBuilder<S> &b, Ref<F1> x, Ref<F2> y,
                    const std::vector<std::pair<size_t, size_t>> &members,
                    size_t index) {
  EqualityLoweringImpl<S>::run(b, x, y, members, index);
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_MAC_H_
