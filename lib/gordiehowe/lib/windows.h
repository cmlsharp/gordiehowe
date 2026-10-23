// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: byte windows at private offsets of a committed text. Each window
// is a byte string, constant bytes and committed bytes, that the text holds at
// a private offset. One filtered multiset equality (permutation.h) over
// (position, byte, flag) records checks every window, where Longfellow shifts
// each window into place with a barrel shifter (Routing::shift, as in
// mdoc_hash.h):
//
//   match_windows(s, H, name, text, offsets, windows) -> delta
//   window_bytes(s, H, name, text, offsets, w, at, len)  -> Bit [len * 8]
//   keyed_window(s, H, windows, name, text, offsets, key, len)
//                                                        -> Bit [len * 8]
//
// TEXT (WindowText) is n committed bytes, Bit [n * 8] (bit 8 i + t is bit t
// of byte i), with a Bit IN_TEXT per byte and the range [first, end) of
// bytes a window may cover. OFFSETS is 2 W bytes that only generators read
// (a host input, or a Witness member through depends_on): window
// w's offset k_w, little-endian, so the window covers bytes first + k_w ..
// first + k_w + L_w - 1. window_bytes is a priv value of a window's
// committed bytes: L bytes at first + k_w + AT, read from the text by a
// masked scan.
//
// Positions and byte values depend on the characteristic (if constexpr on
// the field):
//   characteristic 2   position i is g^i, g of order 2^16 - 1 in GF(2^16);
//                      a byte is sum_t beta_t b_t in GF(2^16);
//   odd                position i is the integer i; a byte is sum_t 2^t b_t.
// The records:
//   text   (pos(i), B_i, f_i) for first <= i < end, B_i the value of byte
//          i, f_i = IN_TEXT_i, and a committed Bit a_i (active) per record;
//   window (z_w * g^j, W_{w,j}, 1), or (z_w + j, W_{w,j}, 1), for j < L_w,
//          with z_w = pos(first + k_w) a committed Subfield cell (named
//          NAME.kappa) and W_{w,j} the window's byte j (a constant, or the
//          value of committed bits);
// and assert_filtered_multiset_equal proves that the active text records
// equal the window records as multisets, under one challenge NAME.delta.
//
// Soundness (given the multiset equality): the text records are pairwise
// distinct (their positions are), so each window record equals a distinct
// active text record. Characteristic 2: z_w g^j = g^{i_j} with first <= i_j
// < end makes z_w nonzero, z_w = g^k for one k < 2^16 - 1, and i_j = k + j
// mod (2^16 - 1). The i_j for j < L_w lie in [first, end) and the residues
// k + j are consecutive, so when end - first + L_w <= 2^16 - 1 they do not
// wrap: i_j = k + j. Odd characteristic: z_w + j = i_j for j < L_w, so z_w
// = i_0 is an integer in [first, end) and i_j = z_w + j, with no wrap when
// end + L_w is below p. So the text holds W_w at bytes k .. k + L_w - 1,
// each with f = 1. Distinct window records match distinct text records, so
// the windows are pairwise disjoint: a statement whose windows overlap has
// no proof (its honest windows never do when their contents differ).
// Conditions: the records' packing is injective (permutation.h), the
// position ranges above (checked here), and the challenge's error is
// max(left, right) / |F| (with A max(left, right) / |F| over both
// challenges when the records pack by a challenge).
//
// Cost: one product per text record (the filter) plus the two product
// trees, about 2 (end - first) + sum L_w multiplications in one circuit;
// the window and text bytes enter as constant combinations of committed
// bits. A barrel shift costs about 8 log2(n) L_w multiplexers per window.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_WINDOWS_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_WINDOWS_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/lib/permutation.h"
#include "gordiehowe/lib/select.h"
#include "gordiehowe/system.h"

namespace proofs::gordiehowe::lib::windows {

// The text windows are matched against.
template <class F>
struct WindowText {
  Ref<F, Bit, Committed> bytes;    // Bit [n * 8]
  Ref<F, Bit, Committed> in_text;  // Bit [n]: a window covers bytes with 1
  size_t first = 0, end = 0;       // bytes a window may cover
  size_t size() const { return in_text.n; }
};

// A part of a window: constant bytes, or committed bytes (Bit [len * 8]).
template <class F>
struct WindowPart {
  bool constant = true;
  std::vector<uint8_t> bytes;
  Ref<F, Bit> value;
  size_t length() const { return constant ? bytes.size() : value.n / 8; }
};
template <class F>
WindowPart<F> window_part(std::vector<uint8_t> bytes) {
  WindowPart<F> p;
  p.bytes = std::move(bytes);
  return p;
}
template <class F, class P>
WindowPart<F> window_part(Ref<F, Bit, P> value) {
  WindowPart<F> p;
  p.constant = false;
  p.value = value;
  return p;
}
template <class F>
struct Window {
  std::vector<WindowPart<F>> parts;
  size_t length() const {
    size_t n = 0;
    for (const auto &p : parts) n += p.length();
    return n;
  }
};

namespace windows_internal {

// The number of bytes a byte dependency holds: a host input's, or a byte
// slice's (a Statement or Witness member).
inline size_t byte_count(const HostInput &h) { return h.n; }
inline size_t byte_count(const BytesSlice &b) { return b.len; }

// alpha^e for 0 <= e < 2^16, by a square-and-multiply with no branch on e.
template <class F>
typename F::Elt power(const F &f, const typename F::Elt &alpha, uint64_t e) {
  typename F::Elt r = f.one(), a = alpha;
  for (size_t t = 0; t < 16; ++t) {
    r = ct::select(ct::mask(e >> t), f.mulf(r, a), r);
    a = f.mulf(a, a);
  }
  return r;
}
// Window w's offset in OFFSETS.
inline uint64_t offset(const std::vector<uint8_t> &off, size_t w) {
  return uint64_t(off.at(2 * w)) | (uint64_t(off.at(2 * w + 1)) << 8);
}

// Positions and byte values (above): g^i and sum_t beta_t b_t in
// characteristic 2, i and sum_t 2^t b_t in odd characteristic.
template <class F>
struct Encoding {
  using Elt = typename F::Elt;
  const F *f = nullptr;
  Elt g{};
  explicit Encoding(const F &field) : f(&field) {
    if constexpr (F::kCharacteristicTwo)
      g = lib::select::subfield_generator(field);
  }
  // pos(e), with no branch on E (a witness's offset).
  Elt position(uint64_t e) const {
    if constexpr (F::kCharacteristicTwo) {
      return power(*f, g, e);
    } else {
      return f->of_scalar(e);
    }
  }
  // pos(i) for i in [b, e).
  std::vector<Elt> positions(size_t b, size_t e) const {
    std::vector<Elt> out;
    out.reserve(e - b);
    if constexpr (F::kCharacteristicTwo) {
      Elt p = power(*f, g, b);
      for (size_t i = b; i < e; ++i) {
        out.push_back(p);
        p = f->mulf(p, g);
      }
    } else {
      for (size_t i = b; i < e; ++i) out.push_back(f->of_scalar(i));
    }
    return out;
  }
  // The position of byte j of a window starting at Z (a Subfield value).
  Expr<F> shifted(const Domain<F> &D, const Expr<F> &z, size_t j0,
                  size_t len) const {
    if constexpr (F::kCharacteristicTwo) {
      return z * D.constant(positions(j0, j0 + len));
    } else {
      return z + D.constant(positions(j0, j0 + len));
    }
  }
  // The byte weights: beta_t (GF(2^16)'s basis) or 2^t.
  std::vector<Elt> weights() const {
    std::vector<Elt> w(8);
    for (size_t t = 0; t < 8; ++t) {
      if constexpr (F::kCharacteristicTwo) {
        w[t] = f->beta(t);
      } else {
        w[t] = f->of_scalar(uint64_t(1) << t);
      }
    }
    return w;
  }
  // The byte values of the bits X (Bit [m * 8]): [m].
  Expr<F> bytes(const Domain<F> &D, const Expr<F, Bit> &x) const {
    const size_t m = x.size() / 8;
    return (Expr<F>(x.reshape({m, 8})) * D.constant(weights())).sum(1);
  }
  // Constant bytes B as values.
  std::vector<Elt> byte_values(const std::vector<uint8_t> &b) const {
    const auto w = weights();
    std::vector<Elt> out;
    for (uint8_t x : b) {
      Elt v = f->zero();
      for (size_t t = 0; t < 8; ++t)
        if ((x >> t) & 1) f->add(v, w[t]);
      out.push_back(v);
    }
    return out;
  }
};

}  // namespace windows_internal

// A priv value NAME in scope S: LEN committed bytes of window W at AT,
// bytes first + k_w + AT .. of TEXT, Bit [len * 8] (zero past the text),
// read by an oblivious rotation: the text, zero-padded to a power of two
// N >= n, rotated left by base mod N in log2 N masked stages (one per bit
// of base), so byte j of the result is byte (base + j) mod N, and masked
// to zero where base + j >= n. The same instructions for every offset.
template <class F, class Off>
Ref<F, Bit, Committed> window_bytes(const Scope &s,
                                    Domain<F> &H,
                                    const std::string &name,
                                    const WindowText<F> &text,
                                    const Off &offsets, size_t w, size_t at,
                                    size_t len) {
  using Elt = typename F::Elt;
  const F *pf = &H.field();
  const size_t n = text.size(), first = text.first;
  return s[H].priv(
      Bit{}, name, Shape(8 * len), depends_on(text.bytes, offsets),
      [pf, n, first, w, at, len](const std::vector<Elt> &bits,
                                 const std::vector<uint8_t> &off) {
        const F &f = *pf;
        size_t lg = 0;
        while ((size_t(1) << lg) < n) ++lg;
        const size_t N = size_t(1) << lg;
        std::vector<uint64_t> byte(N, 0), next(N);
        for (size_t i = 0; i < n; ++i)
          for (size_t t = 0; t < 8; ++t)
            byte[i] |= ct::bit_of(f, bits[8 * i + t]) << t;
        const uint64_t base = first + windows_internal::offset(off, w) + at;
        for (size_t k = 0; k < lg; ++k) {
          const uint64_t m = ct::mask((base >> k) & 1);
          const size_t sh = size_t(1) << k;
          for (size_t i = 0; i < N; ++i)
            next[i] = ct::select(m, byte[(i + sh) & (N - 1)], byte[i]);
          byte.swap(next);
        }
        std::vector<Elt> out(8 * len);
        for (size_t j = 0; j < len; ++j) {
          const uint64_t v = ct::mask(ct::lt(base + j, n)) & byte[j & (N - 1)];
          for (size_t t = 0; t < 8; ++t) out[8 * j + t] = ct::bit_elt(f, v >> t);
        }
        return out;
      });
}

// A window of the constant bytes KEY followed by LEN committed bytes,
// appended to WINDOWS as window w = |WINDOWS|: its committed bytes are
// window_bytes NAME in scope S at |KEY|, which this returns.
template <class F, class Off>
Ref<F, Bit, Committed> keyed_window(const Scope &s, Domain<F> &H,
                                    std::vector<Window<F>> &windows,
                                    const std::string &name,
                                    const WindowText<F> &text,
                                    const Off &offsets,
                                    const std::vector<uint8_t> &key,
                                    size_t len) {
  const auto value = window_bytes(s, H, name, text, offsets, windows.size(),
                                  key.size(), len);
  windows.push_back({{window_part<F>(key), window_part(value)}});
  return value;
}

// The windows WINDOWS lie in TEXT at the offsets OFFSETS (above). Returns
// the multiset equality's challenge.
template <class F, class Off>
Ref<F, Field, Public> match_windows(const Scope &s,
                                    Domain<F> &H,
                                    const std::string &name,
                                    const WindowText<F> &text,
                                    const Off &offsets,
                                    const std::vector<Window<F>> &windows) {
  using Elt = typename F::Elt;
  namespace wi = windows_internal;
  const std::string what = "match_windows '" + s.scoped(name) + "'";
  const F &f = H.field();
  const size_t W = windows.size(), first = text.first, end = text.end;
  if (W == 0) fail(what + ": no window");
  const size_t off_bytes =
      wi::byte_count(DepEntry<Off>::of(offsets));
  if (off_bytes != 2 * W)
    fail(what + ": the offsets hold " + std::to_string(off_bytes) +
         " bytes for " + std::to_string(W) + " windows");
  if (text.bytes.n != 8 * text.size() || end > text.size() || first >= end)
    fail(what + ": the text's bytes, flags or range");
  size_t max_len = 0;
  std::vector<size_t> lens;
  for (const auto &win : windows) {
    lens.push_back(win.length());
    max_len = std::max(max_len, win.length());
    if (win.length() == 0) fail(what + ": an empty window");
  }
  if constexpr (F::kCharacteristicTwo) {
    if (end - first + max_len > 65535)
      fail(what + ": positions wrap in GF(2^16)^*");
  } else {
    if (Bound(end + max_len) >= field_characteristic(f))
      fail(what + ": positions wrap modulo the characteristic");
  }
  const wi::Encoding<F> enc(f);

  // z_w = pos(first + k_w).
  const auto kappa = s[H].priv(
      Subfield{}, name + ".kappa", Shape(W), depends_on(offsets),
      [enc, first, W](const std::vector<uint8_t> &off) {
        std::vector<Elt> out(W);
        for (size_t w = 0; w < W; ++w)
          out[w] = enc.position(first + wi::offset(off, w));
        return out;
      });
  // a_i: byte first + i lies in a window.
  const F *pf = &f;
  const auto active = s[H].priv(
      Bit{}, name + ".active", Shape(end - first),
      depends_on(offsets), [pf, lens, first, end](const std::vector<uint8_t> &off) {
        std::vector<Elt> out(end - first);
        for (size_t i = 0; i < out.size(); ++i) {
          uint64_t a = 0;
          for (size_t w = 0; w < lens.size(); ++w) {
            const uint64_t k = wi::offset(off, w);
            a |= (ct::lt(i, k + lens[w]) & (ct::lt(i, k) ^ 1));
          }
          out[i] = ct::bit_elt(*pf, a);
        }
        return out;
      });

  lib::permutation::Records<F, 3> left(H), right(H);
  {
    const auto bytes = text.bytes.slice(8 * first, 8 * end)
                           .named(s.scoped(name + ".text"));
    const auto flags = text.in_text.slice(first, end)
                           .named(s.scoped(name + ".in_text"));
    left.push(H.constant(enc.positions(first, end)), enc.bytes(H, bytes),
              flags);
  }
  std::vector<std::string> kappa_names;
  for (size_t w = 0; w < W; ++w) {
    kappa_names.push_back(s.scoped(name + ".kappa." + std::to_string(w)));
    const auto kw = kappa.slice(w, w + 1).named(kappa_names.back());
    size_t j0 = 0;
    for (const WindowPart<F> &part : windows[w].parts) {
      const size_t L = part.length();
      const Expr<F> at = enc.shifted(H, kw, j0, L);
      if (part.constant) {
        right.push(at, H.constant(enc.byte_values(part.bytes)), 1);
      } else {
        right.push(at, enc.bytes(H, part.value), 1);
      }
      j0 += L;
    }
  }
  const auto m = lib::permutation::assert_filtered_multiset_equal(
      s, H, name, left, active, right);
  // The plan export: the windows as the multiset equality checks them.
  // Window w starts at byte first + k_w, in [first, end - L_w] (the text
  // records cover [first, end)); positions are powers of g in GF(2^16)^* in
  // characteristic 2, integers otherwise.
  {
    PlanRecords::FilteredPermutation rec;
    rec.domain = H.name;
    rec.message = text.bytes.name();
    rec.message_len = text.size();
    for (size_t w = 0; w < W; ++w)
      rec.windows.push_back({kappa_names[w], lens[w], first, end - lens[w]});
    if constexpr (F::kCharacteristicTwo) {
      rec.offset_field = "GF(2^16)";
      rec.position_bits = 16;
    } else {
      rec.offset_field = "integers";
      size_t bits = 0;
      while ((size_t{1} << bits) < end + max_len) ++bits;
      rec.position_bits = bits;
    }
    rec.message_records = left.size();
    rec.window_records = right.size();
    rec.challenge = m.delta.name();
    s.note("filtered-permutation", name, std::move(rec));
  }
  return m.delta;
}

}  // namespace proofs::gordiehowe::lib::windows

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_LIB_WINDOWS_H_
