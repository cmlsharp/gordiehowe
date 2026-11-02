// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: public tables, library functions over the core.
//
// public_table(s, D, name, rows, map) declares a public table of R rows,
// each row a public vector of W entries, with a RowMap M that relates a
// committed record of W cells of domain D to a row: record = M(row). It
// returns the table's values (PublicTable), which select_row and
// lookup_rows read. The rows may come as column blocks,
// public_table(s, D, name, map, block...), each [R, w_b], a row the
// concatenation of the blocks' rows: a ring's cached key rows and its
// per-message mu limbs stay two values, neither copied. A record may come
// as several parts, select_row(s, table, name, part...), concatenated in
// order. One challenge gamma compresses a record into its digest
//
//   digest(rec) = sum_c rec[c] gamma^e(c),
//
// with distinct exponents e(c) < W, so two different records collide with
// probability at most (W - 1)/|F| over gamma. The verifier never transforms
// a row: by linearity, digest(M(row)) = <row, M^T g> with g = (gamma^e(c))_c,
// so a row's digest is one dot product (ops::RowDot, the field's narrow
// kernel: base-field coefficients and one reduction per row in a
// small-prime extension, ExtCoefTable's technique; the prescaled dot of the
// Goldilocks fields; field products otherwise).
//
// The first select_row into the table declares the challenge
//   <name>.gamma     (it tests what select_row reads)
// and writes two expressions over gamma and the rows, which the compiler
// evaluates on both sides outside the circuit (compiler/public_expr.h),
// named
//   <name>.powers    gamma^k for k < W_max (the widest leaf of the map),
//                    then gamma^off for each leaf at offset off > 0: a
//                    product of the squarings gamma^(2^b), each entry of
//                    exact degree in gamma;
//   <name>.digests   d_j = <row_j, M^T g>, R' entries (R' = R rounded up to
//                    a power of two; row j >= R repeats row j - R), with
//                    M^T g a leaf at a time: gamma^off times the powers for
//                    an identity leaf, gamma^off times ops::NttTranspose of
//                    the powers for a negacyclic leaf (sum_m gamma^m
//                    psi^((2m + 1) i), whatever the leaf's order);
// so a table only lookup_rows reads draws no gamma.
//
// The powers are factored by the record's shape: a record digest is
// sum_b gamma^off_b sum_k rec_b[k] gamma^perm_b(k) over the map's leaves b,
// so a record of 20 polynomials of 256 coefficients and 24 limbs reads 256
// + 21 power wires, not 5144.
//
// select_row(s, table, name, record) proves that RECORD (a handle or an
// expression of W coordinates) is M(row_i) for a committed index i: the
// index's bits (least significant first) and one predicate,
//   digest(record) = fold(d, index),
// where fold is a multiplexer tree, index bit t muxing each pair of the
// level, lo + b_t (hi - lo) (Expr::mux, one product): one folded tree of
// R' - 1 products and depth log2 R' with no layer boundary in it
// (a boundary per level was measured worse in gates and proof size). The
// selection is exact: its only error is the digest's.
//
// A ring whose size is not a power of two is padded by duplicating real
// members: a padded index selects a real row, so the proof still shows
// membership. A zero row would be unsafe, since the prover commits the record
// and could select it, and a zero ML-DSA key accepts every signature.
//
// lookup_rows(s, table, name, records) proves that each of m records (an
// [m][W] handle or expression) is M(row) for some row: the core's
// assert_in (membership.h) over the table of the records M(row_j), the
// rows themselves for the identity map on one block and otherwise the
// public computation <name>.records of M on each row, declared by the
// first lookup. Every lookup into one table is one argument of assert_in:
// R multiplicities <name>.mult, the domain's alpha and, when the records
// pack by a challenge, its gamma.
//
// The charges. gamma (the table's): select_row compares a record with the one
// row its index (committed before gamma) names, a degree-deg event for deg =
// max e(c) = W - 1. lookup_rows charges assert_in's: R (A - 1) on in.gamma:<D>
// for records of width A = W packed by it, R deg (a record off the table packs
// onto one of the R rows), and nothing when the fixed kappa packs them exactly
// (W <= [K : E] with the rows and records in E); m + R - 1 on alpha:<D>.
//
// Compile checks: the rows are a statement value, a constant, or a public
// computation of those (never a challenge or a message), so the digests and
// powers depend on the statement and gamma alone, and nothing public depends
// on the selected index.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_TABLE_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_TABLE_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "gordiehowe/closure_expr.h"
#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/lookup_counts.h"
#include "gordiehowe/lib/ring_core.h"
#include "gordiehowe/membership.h"
#include "gordiehowe/ops/ntt.h"
#include "gordiehowe/ops/operators.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::table {

// How a committed record relates to a public row: record = M(row).
template <class F>
class RowMap {
 public:
  using Elt = typename F::Elt;
  // A leaf of the map: W cells at OFFSET of the record. Identity: cell k is
  // row entry k, exponent k. Negacyclic: cell k is a(psi^(2 brv(k) + 1)),
  // the NTT order of ntt.h (FIPS 204's at psi = 1753), exponent brv(k).
  struct Leaf {
    bool ntt = false;
    size_t n = 0;
    size_t offset = 0;
    Elt psi{};
    // Natural order (NttOrder::kNatural, ntt_gadget's): cell k is
    // a(psi^(2k + 1)), exponent k.
    bool natural = false;
  };

  // M = I on M coordinates.
  static RowMap identity(size_t m) {
    if (m == 0) fail("RowMap::identity: no coordinates");
    RowMap r;
    r.leaves_.push_back(Leaf{false, m, 0, {}});
    r.width_ = m;
    return r;
  }
  // The negacyclic transform of length N with root PSI (psi^N = -1), in
  // ntt.h's spectrum order.
  // ORDER kNatural gives the staged transform's natural order (the carrier
  // rings commit their keys in it).
  static RowMap negacyclic(const F &f, size_t n, const Elt &psi,
                           ops::NttOrder order = ops::NttOrder::kScheme) {
    if (n < 2 || (n & (n - 1)) != 0)
      fail("RowMap::negacyclic: the length " + std::to_string(n) +
           " is not a power of two");
    Elt p = psi;
    for (size_t k = 1; k < n; ++k) p = f.mulf(p, psi);
    if (p != f.mone())
      fail("RowMap::negacyclic: psi^" + std::to_string(n) + " is not -1");
    RowMap r;
    r.leaves_.push_back(
        Leaf{true, n, 0, psi, order == ops::NttOrder::kNatural});
    r.width_ = n;
    return r;
  }
  // The scheme root of length N (FieldNtt::scheme_psi): FIPS 204's zeta
  // over an ML-DSA field, falcon_root_2n over a Falcon field.
  static RowMap negacyclic(const F &f, size_t n) {
    if constexpr (ops::kFieldNtt<F>) {
      if (auto psi = ops::FieldNtt<F>::scheme_psi(f, n))
        return negacyclic(f, n, *psi);
    }
    fail("RowMap::negacyclic: the field has no root of order " +
         std::to_string(2 * n));
  }
  // FIPS 204's NTT (Algorithm 41): length 256, zeta = 1753, over a field of
  // characteristic 8380417.
  static RowMap fips204(const F &f) {
    if constexpr (F::kCharacteristicTwo) {
      fail("RowMap::fips204: the field has characteristic 2");
    } else {
      if (field_characteristic(f) != 8380417)
        fail("RowMap::fips204: the field's characteristic is " +
             bound_str(field_characteristic(f)) + ", not 8380417");
      return negacyclic(f, 256, f.of_scalar(1753));
    }
  }
  // PARTS in order, part (map, count) repeated COUNT times.
  static RowMap blocks(const std::vector<std::pair<RowMap, size_t>> &parts) {
    RowMap r;
    for (const auto &[m, count] : parts)
      for (size_t c = 0; c < count; ++c) {
        for (Leaf l : m.leaves_) {
          l.offset += r.width_;
          r.leaves_.push_back(l);
        }
        r.width_ += m.width_;
      }
    if (r.width_ == 0) fail("RowMap::blocks: no coordinates");
    return r;
  }

  size_t width() const { return width_; }
  const std::vector<Leaf> &leaves() const { return leaves_; }
  // The widest leaf: the number of base power wires.
  size_t max_leaf() const {
    size_t w = 0;
    for (const auto &l : leaves_) w = std::max(w, l.n);
    return w;
  }
  // The leaves at a nonzero offset: one multiplier wire each.
  size_t multipliers() const {
    size_t m = 0;
    for (const auto &l : leaves_) m += l.offset != 0;
    return m;
  }
  // The power index of cell K of leaf L.
  static size_t perm(const Leaf &l, size_t k) {
    return l.ntt && !l.natural ? ops::ntt_brv(k, ops::ntt_log2(l.n)) : k;
  }

  void describe(const F &f, std::vector<uint8_t> &out) const {
    put_u64(out, width_);
    put_u64(out, leaves_.size());
    for (const auto &l : leaves_) {
      put_u64(out, l.ntt ? (l.natural ? 2 : 1) : 0);
      put_u64(out, l.n);
      put_u64(out, l.offset);
      uint8_t b[F::kBytes];
      f.to_bytes_field(b, l.ntt ? l.psi : f.zero());
      out.insert(out.end(), b, b + F::kBytes);
    }
  }

  // The record M(ROW) (host, by definition; tests and honest witnesses).
  std::vector<Elt> apply(const F &f, const std::vector<Elt> &row) const {
    if (row.size() != width_) fail("RowMap::apply: wrong row length");
    std::vector<Elt> out(width_);
    for (const auto &l : leaves_) {
      for (size_t k = 0; k < l.n; ++k) {
        if (!l.ntt) {
          out[l.offset + k] = row[l.offset + k];
          continue;
        }
        // a(x) at x = psi^(2 perm(k) + 1).
        Elt x = l.psi;
        const Elt psi2 = f.mulf(l.psi, l.psi);
        for (size_t j = 0; j < perm(l, k); ++j) x = f.mulf(x, psi2);
        Elt acc = f.zero(), xi = f.one();
        for (size_t i = 0; i < l.n; ++i) {
          f.add(acc, f.mulf(row[l.offset + i], xi));
          xi = f.mulf(xi, x);
        }
        out[l.offset + k] = acc;
      }
    }
    return out;
  }

  // G = M^T g with g[c] = gamma^e(c), e(c) = offset + perm(k): a row's
  // digest is <row, G>. Negacyclic leaf (omega = psi^2):
  //   G[off + i] = gamma^off sum_m gamma^m psi^((2m + 1) i)
  //              = gamma^off psi^i (gamma^n - 1)/(gamma omega^i - 1),
  // and n gamma^off psi^i where gamma omega^i = 1 (the sum of n ones). One
  // batch inversion (batch_invert, lib/ring_core.h) per leaf.
  std::vector<Elt> transposed(const F &f, const Elt &gamma) const {
    std::vector<Elt> G(width_);
    for (const auto &l : leaves_) {
      Elt go = f.one();
      for (size_t k = 0; k < l.offset; ++k) go = f.mulf(go, gamma);
      if (!l.ntt) {
        Elt p = go;
        for (size_t k = 0; k < l.n; ++k) {
          G[l.offset + k] = p;
          p = f.mulf(p, gamma);
        }
        continue;
      }
      Elt gn = f.one();
      for (size_t k = 0; k < l.n; ++k) gn = f.mulf(gn, gamma);
      const Elt num = f.mulf(go, f.subf(gn, f.one()));
      const Elt omega = f.mulf(l.psi, l.psi);
      std::vector<Elt> den(l.n);
      std::vector<bool> pole(l.n, false);
      Elt wi = f.one();
      for (size_t i = 0; i < l.n; ++i) {
        den[i] = f.subf(f.mulf(wi, gamma), f.one());
        if (den[i] == f.zero()) {  // public: gamma is a challenge
          pole[i] = true;
          den[i] = f.one();
        }
        wi = f.mulf(wi, omega);
      }
      const std::vector<Elt> inv = batch_invert(f, den);
      const Elt nn = f.mulf(go, f.of_scalar(uint64_t(l.n)));
      Elt pi = f.one();
      for (size_t i = 0; i < l.n; ++i) {
        G[l.offset + i] = pole[i] ? f.mulf(nn, pi) : f.mulf(pi, f.mulf(num, inv[i]));
        pi = f.mulf(pi, l.psi);
      }
    }
    return G;
  }

 private:
  std::vector<Leaf> leaves_;
  size_t width_ = 0;
};

namespace table_internal {

// The degree of a record digest in gamma: the largest exponent e(c) =
// offset + perm(k) over the map's cells.
template <class F>
Bound digest_degree(const RowMap<F> &map) {
  Bound degree = 0;
  for (const auto &l : map.leaves())
    for (size_t k = 0; k < l.n; ++k)
      degree = std::max<Bound>(degree, l.offset + RowMap<F>::perm(l, k));
  return degree;
}

}  // namespace table_internal

// The index bits of a table of ROWS rows: log2 of ROWS rounded up to a
// power of two (public_table pads the rows to 2^bits by repeating them).
inline size_t index_bits(size_t rows) {
  size_t b = 0;
  while ((size_t{1} << b) < rows) ++b;
  return b;
}

// A public table as public_table declares it: its domain, map and sizes,
// the rows, and the values select_row and lookup_rows read.
template <class F>
struct PublicTable {
  std::string name;  // NAME in the declaring scope
  Domain<F> *D = nullptr;  // the records' domain
  std::optional<Scope> scope;  // the declaring scope
  std::string local;           // NAME before the scope's prefix
  RowMap<F> map;
  size_t rows = 0, padded_rows = 0, width = 0, index_bits = 0;
  // The rows as column blocks: block b holds R rows of widths[b] entries.
  std::vector<Ref<F>> parts;
  std::vector<size_t> widths;
  // Every row entry lies in the designated subfield by its type (Bit or
  // Subfield<>).
  bool rows_in_subfield = false;
  // What select_row reads: the challenge gamma, and its powers and the
  // rows' digests as expressions, written by the first select_row
  // (declare_digests).
  struct Digests {
    Ref<F, Field, Public> gamma;
    Expr<F> powers, digests;
  };
  std::shared_ptr<std::optional<Digests>> digests =
      std::make_shared<std::optional<Digests>>();
  std::function<Digests()> declare_digests;
  // The table of records M(row) that lookup_rows' assert_in reads, made by
  // the first lookup.
  std::shared_ptr<std::optional<InTable<F>>> lookup =
      std::make_shared<std::optional<InTable<F>>>();
};
// What select_row declares and reads.
template <class F>
struct Selected {
  Ref<F, Bit, Committed> index;   // log2 R' bits, least significant first
  Ref<F, Field, Public> gamma;
  Expr<F> powers, digests;
};

namespace table_internal {

// PARTS side by side along the leading axis, by halves (each concatenation
// copies its index map, so a long list costs n log n, not n^2).
template <class F>
Expr<F> concat_all(const std::vector<Expr<F>> &parts, size_t a, size_t e) {
  if (e - a == 1) return parts[a];
  const size_t m = a + (e - a) / 2;
  return concat_all(parts, a, m).concat(concat_all(parts, m, e));
}

// The powers of gamma as expressions of exact degree: SQ[j] = gamma^(2^j),
// RANGE(n) = [gamma^0, ..., gamma^(n - 1)] (the first h = 2^j < n powers,
// then gamma^h times RANGE(n - h), so degree n - 1), and AT(e) = gamma^e,
// the product of the squarings of e's bits.
template <class F>
class GammaPowers {
 public:
  GammaPowers(const Domain<F> &D, const Ref<F, Field, Public> &gamma)
      : D_(D) {
    sq_.push_back(Expr<F>(gamma));
  }
  Expr<F> range(size_t n) {
    check(n >= 1, "GammaPowers: an empty range");
    auto it = ranges_.find(n);
    if (it != ranges_.end()) return it->second;
    Expr<F> out = D_.constant(std::vector<uint64_t>{1});
    if (n > 1) {
      size_t j = 0;
      while ((size_t{2} << j) < n) ++j;
      const size_t h = size_t{1} << j;
      out = range(h).concat(square(j) * range(n - h));
    }
    ranges_.emplace(n, out);
    return out;
  }
  Expr<F> at(size_t e) {
    check(e >= 1, "GammaPowers: gamma^0 is a constant");
    std::optional<Expr<F>> out;
    for (size_t b = 0; (e >> b) != 0; ++b)
      if ((e >> b) & 1) out = out ? *out * square(b) : square(b);
    return *out;
  }

 private:
  Expr<F> square(size_t j) {
    while (sq_.size() <= j) sq_.push_back(sq_.back() * sq_.back());
    return sq_[j];
  }
  const Domain<F> &D_;
  std::vector<Expr<F>> sq_;
  std::map<size_t, Expr<F>> ranges_;
};

// The table's powers (gamma^k for k < W_max, then gamma^off per offset
// leaf) and digests (d_j = <row_j, M^T g> over the column blocks PARTS of
// widths WIDTHS, padded to RP rows by repeating rows), as expressions.
template <class F, class... T, class... P>
std::pair<Expr<F>, Expr<F>> digest_exprs(const Domain<F> &D,
                                         const Ref<F, Field, Public> &gamma,
                                         const RowMap<F> &map,
                                         const std::vector<size_t> &widths,
                                         size_t R, size_t Rp,
                                         const Ref<F, T, P> &...parts) {
  const size_t wmax = map.max_leaf();
  GammaPowers<F> g(D, gamma);
  std::vector<Expr<F>> pw = {g.range(wmax)};
  for (const auto &l : map.leaves())
    if (l.offset != 0) pw.push_back(g.at(l.offset));
  const Expr<F> powers = concat_all(pw, 0, pw.size());
  // M^T g, a leaf at a time in offset order.
  std::vector<Expr<F>> leaves;
  size_t mi = 0, at = 0;
  for (const auto &l : map.leaves()) {
    check(l.offset == at, "digest_exprs: the map's leaves are not contiguous");
    at += l.n;
    Expr<F> x = powers.slice(0, l.n);
    if (l.ntt) x = ops::NttTranspose(D.field(), l.n, l.psi)(x);
    if (l.offset != 0) {
      x = powers.slice(wmax + mi, wmax + mi + 1) * x;
      ++mi;
    }
    leaves.push_back(x);
  }
  const Expr<F> G = concat_all(leaves, 0, leaves.size());
  // Each block's rows against its columns of G.
  std::vector<Expr<F>> blocks;
  size_t off = 0, b = 0;
  (
      [&](const auto &part) {
        blocks.push_back(ops::RowDot(part)(G.slice(off, off + widths[b])));
        off += widths[b];
        ++b;
      }(parts),
      ...);
  Expr<F> d = blocks[0];
  for (size_t k = 1; k < blocks.size(); ++k) d = d + blocks[k];
  if (Rp > R) {
    std::vector<size_t> idx(Rp);
    for (size_t j = 0; j < Rp; ++j) idx[j] = j < R ? j : j - R;
    d = d.reindex(idx);
  }
  return {powers, d};
}

// The record digest of RECORD ([W]): sum_b gamma^off_b sum_k rec[off_b + k]
// gamma^perm_b(k), reading the base powers POWERS[0, WMAX) and the
// multipliers POWERS[WMAX, ...) in leaf order: one product per cell and one
// per leaf at an offset.
template <class F>
Expr<F> record_digest(const Expr<F> &record, const Expr<F> &powers,
                      const RowMap<F> &map) {
  const size_t wmax = map.max_leaf();
  std::optional<Expr<F>> total;
  size_t mi = 0;
  for (const auto &l : map.leaves()) {
    std::vector<size_t> idx(l.n);
    for (size_t k = 0; k < l.n; ++k) idx[k] = RowMap<F>::perm(l, k);
    Expr<F> d = (record.slice(l.offset, l.offset + l.n) * powers.reindex(idx))
                    .sum();
    if (l.offset != 0) d = powers.slice(wmax + mi, wmax + mi + 1) * d;
    mi += l.offset != 0;
    total = total.has_value() ? *total + d : d;
  }
  return *total;
}

// The entry of the folded DIGESTS ([2^k]) at the index BITS (k bits, least
// significant first): a multiplexer tree, level t keeping lo + b_t (hi - lo)
// of each pair, one folded tree of 2^k - 1 products.
template <class F>
Expr<F> fold(Expr<F> digests, const Expr<F, Bit> &bits) {
  for (size_t t = 0; t < bits.size(); ++t) {
    std::vector<size_t> lo, hi;
    for (size_t i = 0; 2 * i + 1 < digests.size(); ++i) {
      lo.push_back(2 * i);
      hi.push_back(2 * i + 1);
    }
    digests = bits.at(t).mux(digests.reindex(hi), digests.reindex(lo));
  }
  return digests;
}

}  // namespace table_internal

// The public table NAME (in scope S) of the records of domain D, the rows
// given as column blocks: PARTS, public values of shapes [R, ...] whose
// trailing axes together hold MAP's width, a row the concatenation of the
// blocks' rows (a ring's static key records and its per-message mu limbs,
// without a copy of either). The digest of a row is the sum of its blocks'
// narrow dot products.
template <class F, class... T, class... P>
PublicTable<F> public_table(const Scope &s, Domain<F> &D,
                            const std::string &name, RowMap<F> map,
                            Ref<F, T, P>... parts) {
  static_assert(sizeof...(T) >= 1, "public_table: no rows");
  static_assert(
      ((std::is_same_v<P, Public> || std::is_same_v<P, AnyPlace>) && ...),
      "public_table: the rows are a public value (a statement value, a "
      "constant or a public computation)");
  static_assert(!(is_bytes_v<T> || ...),
                "public_table: the rows are field values; decode a Bytes "
                "statement with a public computation");
  const F &f = D.field();
  const std::string what = "PublicTable '" + s.scoped(name) + "'";
  PublicTable<F> t;
  t.parts = {Ref<F>(parts)...};
  // The digests and powers depend on the statement and gamma alone.
  for (const auto &p : t.parts) {
    const Provenance pv = provenance(p);
    if (!pv.statement)
      fail(what + ": the rows read '" + pv.why + "', which is not a "
           "statement value, a constant or a public computation of those");
  }
  t.name = s.scoped(name);
  t.D = &D;
  t.scope = s;
  t.local = name;
  t.map = std::move(map);
  t.rows = t.parts[0].dims().at(0);
  t.width = t.map.width();
  if (t.rows < 2) fail(what + ": a table of fewer than two rows");
  size_t width = 0;
  for (const auto &p : t.parts) {
    if (p.dims().at(0) != t.rows || p.n % t.rows != 0)
      fail(what + ": the column blocks hold different numbers of rows");
    t.widths.push_back(p.n / t.rows);
    width += p.n / t.rows;
  }
  if (width != t.width)
    fail(what + ": a row has " + std::to_string(width) +
         " entries and the map " + std::to_string(t.width));
  t.index_bits = index_bits(t.rows);
  t.padded_rows = size_t{1} << t.index_bits;
  const RowMap<F> rmap = t.map;
  const size_t R = t.rows, Rp = t.padded_rows;
  const std::vector<size_t> widths = t.widths;
  t.rows_in_subfield =
      ((is_bit_v<T> || std::is_same_v<T, Subfield<>>) && ...);
  const size_t wmax = t.map.max_leaf(), nm = t.map.multipliers();
  // gamma, its powers and the digests, declared by the first select_row:
  // a table only lookup_rows reads draws no gamma.
  const Scope sc = s;
  Domain<F> *pd = &D;
  const std::string tname = t.name;
  t.declare_digests = [sc, pd, name, tname, rmap, R, Rp, widths, parts...]() {
    typename PublicTable<F>::Digests dg;
    dg.gamma = sc[*pd].challenge(name + ".gamma");
    // The plan export, select_row's event: a record off the table has the
    // digest of the one row its index (committed before gamma) names. A
    // digest is a polynomial in gamma of degree deg, the largest exponent
    // e(c), so that holds for at most deg gammas.
    sc.note("charge", "public_table",
            ChallengeCharge{dg.gamma, table_internal::digest_degree(rmap)});
    auto [powers, digests] = table_internal::digest_exprs(
        *pd, dg.gamma, rmap, widths, R, Rp, parts...);
    dg.powers = powers.named(tname + ".powers");
    dg.digests = digests.named(tname + ".digests");
    return dg;
  };
  // The plan export: rows and padding, the column blocks, the row map's
  // leaves and the factored powers (the widest leaf, one multiplier per
  // offset leaf).
  {
    std::vector<std::pair<std::string, SignedInt>> ps = {
        {"rows", __int128(R)},
        {"paddedRows", __int128(Rp)},
        {"padding", __int128(Rp - R)},
        {"width", __int128(t.width)},
        {"indexBits", __int128(t.index_bits)},
        {"blocks", __int128(widths.size())}};
    for (size_t b = 0; b < widths.size(); ++b)
      ps.push_back({"block" + std::to_string(b) + ".width", __int128(widths[b])});
    ps.push_back({"leaves", __int128(t.map.leaves().size())});
    for (size_t i = 0; i < t.map.leaves().size(); ++i) {
      const auto &l = t.map.leaves()[i];
      const std::string k = "leaf" + std::to_string(i) + ".";
      ps.push_back({k + "ntt", l.ntt ? 1 : 0});
      // The transform's output order: 0 natural (NttOrder::kNatural), 1
      // the scheme's (ntt.h's bit-reversed spectrum order).
      if (l.ntt) ps.push_back({k + "order", l.natural ? 0 : 1});
      ps.push_back({k + "n", __int128(l.n)});
      ps.push_back({k + "offset", __int128(l.offset)});
      if constexpr (!F::kCharacteristicTwo)
        if (l.ntt && subfield_contains(f, l.psi))
          ps.push_back({k + "psi", SignedInt(nat_of(f, l.psi))});
    }
    ps.push_back({"maxLeaf", __int128(wmax)});
    ps.push_back({"multipliers", __int128(nm)});
    s.note("public-table", name, std::move(ps), D);
  }
  return t;
}
// The public table NAME (in scope S) of the records of domain D: ROWS, a
// public value of shape [R, ...] whose trailing axes hold MAP's width.
template <class F, class T, class P>
PublicTable<F> public_table(const Scope &s, Domain<F> &D,
                            const std::string &name, Ref<F, T, P> rows,
                            RowMap<F> map) {
  return public_table(s, D, name, std::move(map), rows);
}

namespace table_internal {

// The node of X when X is a whole handle (one term of coefficient 1 and no
// operator reading every coordinate of its node), or none.
template <class F>
std::optional<size_t> whole_handle(const Expr<F> &x) {
  const ExprNode<F> &e = *x.node;
  if (e.op != ExprOp::kLin || e.lin.terms.size() != 1) return std::nullopt;
  const auto &t = e.lin.terms[0];
  if (!t.chain.empty() || t.scale != e.f->one() || t.in_n != e.n)
    return std::nullopt;
  return t.node;
}

// Records on T's domain that PARTS (the record's parts, in order, of a
// record of T's width repeated every width coordinates) equal M(row) for
// rows of T, by the predicate NM, for interval propagation
// (Domain::TableRecord): each part that is a whole handle.
template <class F>
void note_records(const PublicTable<F> &t, const std::vector<Expr<F>> &parts,
                  const Name &nm) {
  using Rec = typename Domain<F>::TableRecord;
  using Leaf = typename Domain<F>::TableLeaf;
  Rec base;
  base.width = t.width;
  base.pred = nm.prefix.empty() ? nm.name : nm.prefix + "." + nm.name;
  for (const auto &l : t.map.leaves())
    base.leaves.push_back(Leaf{l.offset, l.n, l.ntt, l.natural, l.psi});
  for (size_t b = 0; b < t.parts.size(); ++b)
    base.blocks.push_back({t.parts[b].id, t.widths[b]});
  size_t at = 0;
  for (const auto &p : parts) {
    if (const auto id = whole_handle(p)) {
      Rec r = base;
      r.node = *id;
      r.at = at;
      t.D->note_table_record(std::move(r));
    }
    at += p.size();
  }
}

}  // namespace table_internal

namespace table_internal {
// select_row with the index bits INDEX, or bits NAME.index declared after
// the table's digests when INDEX is empty.
template <class F>
Selected<F> select_row_at(const Scope &s, const PublicTable<F> &t,
                          const std::string &name,
                          const std::optional<Ref<F, Bit, Committed>> &index,
                          const std::vector<Expr<F>> &parts) {
  Domain<F> &D = *t.D;
  const std::string what = "select '" + s.scoped(name) + "'";
  size_t width = 0;
  for (const auto &p : parts) width += p.size();
  if (width != t.width)
    fail(what + ": the record has " + std::to_string(width) +
         " coordinates and the map " + std::to_string(t.width));
  Expr<F> record = parts.at(0).flat();
  for (size_t i = 1; i < parts.size(); ++i)
    record = record.concat(parts[i].flat());
  if (!t.digests->has_value()) *t.digests = t.declare_digests();
  const auto &dg = **t.digests;
  Selected<F> out;
  out.gamma = dg.gamma;
  out.powers = dg.powers;
  out.digests = dg.digests;
  if (index) {
    if (index->n != t.index_bits)
      fail(what + ": the index has " + std::to_string(index->n) +
           " bits and the table " + std::to_string(t.index_bits));
    out.index = *index;
  } else {
    out.index = s[D].priv(Bit{}, name + ".index", t.index_bits);
  }
  // The plan export: the record's parts and the fold over the padded rows
  // (a multiplexer tree: R' - 1 products, depth log2 R').
  {
    std::vector<std::pair<std::string, SignedInt>> ps = {
        {"parts", __int128(parts.size())}};
    for (size_t i = 0; i < parts.size(); ++i)
      ps.push_back({"part" + std::to_string(i) + ".width",
                    __int128(parts[i].size())});
    ps.push_back({"rows", __int128(t.rows)});
    ps.push_back({"paddedRows", __int128(t.padded_rows)});
    ps.push_back({"indexBits", __int128(t.index_bits)});
    ps.push_back({"foldProducts", __int128(t.padded_rows - 1)});
    ps.push_back({"foldDepth", __int128(t.index_bits)});
    s.note("table-select", name, std::move(ps), out.index);
  }
  assert_equal(table_internal::record_digest(record, Expr<F>(dg.powers), t.map),
               table_internal::fold(Expr<F>(dg.digests), out.index),
               s.name(name));
  note_records(t, parts, s.name(name));
  return out;
}
}  // namespace table_internal

// RECORD = M(row_i) of table T for a committed index i (bits NAME.index in
// scope S, filled by the prover). The record is the concatenation of
// PARTS (expressions), of the map's width in all. One predicate NAME:
//   record_digest(record) = fold(digests, index).
template <class F>
Selected<F> select_row(const Scope &s, const PublicTable<F> &t,
                       const std::string &name,
                       const std::vector<Expr<F>> &parts) {
  return table_internal::select_row_at<F>(s, t, name, std::nullopt, parts);
}
// The same with the index bits INDEX (T.index_bits Bits, least
// significant first) that the caller commits, for example computed from a
// Witness member.
template <class F>
Selected<F> select_row(const Scope &s, const PublicTable<F> &t,
                       const std::string &name,
                       const Ref<F, Bit, Committed> &index,
                       const std::vector<Expr<F>> &parts) {
  return table_internal::select_row_at<F>(s, t, name, index, parts);
}
// The same for a RECORD that is one handle or expression.
template <class F, class X,
          class = std::enable_if_t<kIsPoly<X>>>
Selected<F> select_row(const Scope &s, const PublicTable<F> &t,
                       const std::string &name, const X &record) {
  static_assert(std::is_same_v<PolyField<X>, F>,
                "select_row: the record lies in the table's field");
  return select_row(s, t, name, std::vector<Expr<F>>{Expr<F>(as_expr(record))});
}
// The same for a record given as several handles or expressions, in order.
template <class F, class X, class Y, class... Z,
          class = std::enable_if_t<kIsPoly<X> && kIsPoly<Y> &&
                                   (kIsPoly<Z> && ...)>>
Selected<F> select_row(const Scope &s, const PublicTable<F> &t,
                       const std::string &name, const X &x, const Y &y,
                       const Z &...z) {
  static_assert(std::is_same_v<PolyField<X>, F> &&
                    std::is_same_v<PolyField<Y>, F> &&
                    (std::is_same_v<PolyField<Z>, F> && ...),
                "select_row: the record lies in the table's field");
  return select_row(s, t, name,
                    std::vector<Expr<F>>{Expr<F>(as_expr(x)),
                                         Expr<F>(as_expr(y)),
                                         Expr<F>(as_expr(z))...});
}

namespace table_internal {

// The rows of table T as the records M(row) a lookup compares (an
// assert_in table, named as T): the rows themselves when the map is the
// identity on one block, otherwise the public computation NAME.records of
// M applied to each row (both parties compute it, once per statement).
// Made by the first lookup into T. Its entries lie in the designated
// subfield when the rows do by type and every transform's root does.
template <class F>
const InTable<F> &lookup_table(const PublicTable<F> &t) {
  using Elt = typename F::Elt;
  if (t.lookup->has_value()) return **t.lookup;
  const Scope &s = *t.scope;
  Domain<F> &D = *t.D;
  const F &f = D.field();
  InTable<F> it;
  it.name = t.name;
  it.R = t.rows;
  it.A = t.width;
  it.rows_in_subfield = t.rows_in_subfield;
  for (const auto &l : t.map.leaves())
    it.rows_in_subfield =
        it.rows_in_subfield && (!l.ntt || subfield_contains(f, l.psi));
  const bool identity = t.parts.size() == 1 && t.map.leaves().size() == 1 &&
                        !t.map.leaves()[0].ntt;
  if (identity) {
    it.rows = t.parts[0].reshape({t.rows, t.width});
    *t.lookup = it;
    return **t.lookup;
  }
  // The blocks side by side, [R, W].
  Expr<F> rows = Expr<F>(t.parts[0]).reshape({t.rows, t.widths[0]});
  for (size_t b = 1; b < t.parts.size(); ++b)
    rows = rows.concat(Expr<F>(t.parts[b]).reshape({t.rows, t.widths[b]}), 1);
  std::vector<uint8_t> descr;
  t.map.describe(f, descr);
  Computes id{"public_table_records", {}};
  put_u64(id.params, t.rows);
  id.params.insert(id.params.end(), descr.begin(), descr.end());
  const F *pf = &f;
  const RowMap<F> map = t.map;
  const size_t R = t.rows, W = t.width;
  it.rows = s[D].pub(
      Field{}, t.local + ".records", Shape{R, W}, depends_on(rows), id,
      [pf, map, R, W](const std::vector<Elt> &v) {
        std::vector<Elt> out;
        out.reserve(R * W);
        for (size_t j = 0; j < R; ++j) {
          const auto r = map.apply(
              *pf, std::vector<Elt>(v.begin() + long(j * W),
                                    v.begin() + long((j + 1) * W)));
          out.insert(out.end(), r.begin(), r.end());
        }
        return out;
      });
  *t.lookup = it;
  return **t.lookup;
}

}  // namespace table_internal

// Each of the m records (RECORDS: [m, ...] of m times the map's width
// coordinates) is M(row) for some row of table T: assert_in over the table of
// the records M(row_j) (lookup_table). Every lookup into one table shares its
// multiplicities and its fraction tree, and the domain's alpha (and gamma, when
// the records pack by a challenge): the charges of assert_in, R (A - 1) on
// gamma for a record of width A = W, and m + R - 1 on alpha (deg = W - 1). NAME
// (in scope S) names the request.
template <class F, class X,
          class = std::enable_if_t<kIsPoly<X>>>
void lookup_rows(const Scope &s, const PublicTable<F> &t,
                 const std::string &name, const X &records) {
  static_assert(std::is_same_v<PolyField<X>, F>,
                "lookup_rows: the records lie in the table's field");
  static_assert(!F::kCharacteristicTwo,
                "lookup_rows: a log-derivative lookup needs an odd "
                "characteristic (multiplicities are integers)");
  const std::string what = "lookup '" + s.scoped(name) + "'";
  const auto e = as_expr(records);
  if (e.size() == 0 || e.size() % t.width != 0)
    fail(what + ": " + std::to_string(e.size()) +
         " coordinates are not a whole number of records of width " +
         std::to_string(t.width));
  assert_in(e, table_internal::lookup_table(t), s.name(name));
  table_internal::note_records(t, std::vector<Expr<F>>{Expr<F>(e)},
                               s.name(name));
}

}  // namespace proofs::gordiehowe::lib::table

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_TABLE_H_
