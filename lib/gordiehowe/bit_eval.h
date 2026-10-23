// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: word-level evaluation of Bit expressions in characteristic 2,
// the honest witness of D.priv(e) (domain.h's expr_advice).
//
// In characteristic 2 a Bit expression whose operations keep every value
// in GF(2) is a Boolean function of its leaves' bits: + and ^ are XOR, *
// and & AND, | OR, ~ NOT, mux a select, sums of coordinates XORs, products
// and all() ANDs, any() ORs. Such an expression is compiled once, when it
// is declared, into a flat program over bit arrays, 64 coordinates per
// uint64_t, and the program computes the same values as eval_expr (the
// Logic emitter over the evaluation backend) on 0/1 leaves:
//   leaf      a node of type Bit, read in place from the packed bits a
//             program kept for it in this run, else its elements read as
//             bits (ct::bit_of), kept the same way, so that a node many
//             programs read (a long message) is converted once per run;
//   const     constant bits;
//   xor, and, or, not, mux   word by word;
//   select    a view (rotate, reindex, slice, concat, broadcast), or one
//             term j of each group of a sum, product, any or all: runs of
//             consecutive source bits, copied a word at a time. Views of
//             views are composed when the program is built, so a rotation
//             of a rotation is one select, and a run of zero constants
//             copies nothing.
// An expression with another operation (a comparison, a linear operator, a
// convolution), a leaf of another type, a leaf through an operator, or a
// constant or coefficient outside {0, 1} has no program; its value is
// eval_expr's. The program reads the structure only: no branch reads a
// value. Its operations, runs and constants are three flat arrays, so that
// a program run once per proof reads little memory.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BIT_EVAL_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BIT_EVAL_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <initializer_list>
#include <map>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>

#include "gordiehowe/core.h"
#include "gordiehowe/ct.h"
#include "gordiehowe/expr.h"

namespace proofs::gordiehowe {

template <class F>
class BitProgram {
 public:
  using Elt = typename F::Elt;

  // The program of E over the nodes of graph G, or null when E has none
  // (above). F is of characteristic 2.
  static std::shared_ptr<const BitProgram> compile(const F &f,
                                                   const ExprPtr<F> &e,
                                                   const Graph &g) {
    static_assert(F::kCharacteristicTwo,
                  "BitProgram: Bit expressions of characteristic 2");
    auto p = std::shared_ptr<BitProgram>(new BitProgram(f));
    Builder b{*p, g, {}, {}};
    const int out = b.build(*e);
    if (out < 0) return nullptr;
    p->out_ = uint32_t(out);
    p->n_ = e->n;
    size_t at = 0, scratch = 0;
    for (auto &op : p->ops_) {
      // A leaf is read in place (execute): it has no words here.
      if (op.k == K::kLeaf) continue;
      op.at = uint32_t(at);
      at += words(op.n);
      if (op.k == K::kSelect && op.t1 - op.t0 > 1)
        scratch = std::max(scratch, words(op.n));
    }
    // One term of a select of several terms is built in the scratch words.
    p->scratch_ = at;
    p->total_ = at + scratch;
    p->ops_.shrink_to_fit();
    p->runs_.shrink_to_fit();
    p->terms_.shrink_to_fit();
    p->consts_.shrink_to_fit();
    return p;
  }

  // E's values from the leaves' values V: 0 and 1 of F. A leaf whose
  // packed bits V holds (ValueReader::packed_bits) is read from them; with
  // SELF, the node these values fill, the output's packed bits are kept
  // there for the programs that read it.
  std::vector<Elt> run(const ValueReader &v, size_t self = SIZE_MAX) const {
    const uint64_t *r = execute(v);
    const Elt zero = f_->zero(), one = f_->one();
    std::vector<Elt> out;
    out.reserve(n_);
    for (size_t i = 0; i < n_; ++i)
      out.push_back(ct::select(ct::mask(r[i / 64] >> (i % 64)), one, zero));
    if (self != SIZE_MAX) v.packed_bits[self].assign(r, r + words(n_));
    return out;
  }
  // The same values as packed bits, 64 coordinates per word (bit i % 64 of
  // word i / 64), kept under SELF as run() keeps them (a value stored as
  // words packs them).
  std::vector<uint64_t> run_packed(const ValueReader &v,
                                   size_t self = SIZE_MAX) const {
    const uint64_t *r = execute(v);
    std::vector<uint64_t> out(r, r + words(n_));
    if (self != SIZE_MAX) v.packed_bits[self] = out;
    return out;
  }

  // The same packed bits in this thread's memory, valid until the
  // thread's next run of a program, and not kept.
  const uint64_t *run_in_place(const ValueReader &v) const {
    return execute(v);
  }

  // The number of operations (for tests and reports).
  size_t size() const { return ops_.size(); }

 private:
  enum class K : uint8_t {
    kLeaf,
    kConst,
    kXor,
    kAnd,
    kOr,
    kNot,
    kMux,
    kSelect,
    kFill,
  };
  // LEN bits of operation FROM starting at bit SRC, written at bit DST.
  struct Run {
    uint32_t from, src, dst, len;
  };
  struct Op {
    K k;
    // kSelect: how its terms combine (kXor, kAnd or kOr).
    K combine = K::kXor;
    uint32_t n = 0;
    // The operation's words in the program's memory.
    uint32_t at = 0;
    // Operands (operation indices).
    uint32_t a[3] = {0, 0, 0};
    // kSelect: its terms T0 .. T1 - 1, term j the runs terms_[j] ..
    // terms_[j + 1] - 1. kConst: its words at consts_[t0].
    uint32_t t0 = 0, t1 = 0;
    // kLeaf: the graph node.
    size_t node = 0;
  };

  explicit BitProgram(const F &f) : f_(&f) {}

  static size_t words(size_t n) { return (n + 63) / 64; }

  // The program under construction from an expression of graph G.
  struct Builder {
    BitProgram &p;
    const Graph &g;
    std::map<const ExprNode<F> *, int> memo;
    std::map<size_t, uint32_t> leaves;

    const F &f() const { return *p.f_; }
    uint32_t add(const Op &op) {
      p.ops_.push_back(op);
      return uint32_t(p.ops_.size() - 1);
    }
    bool is01(const Elt &x) const { return x == f().zero() || x == f().one(); }
    // A constant of the packed bits C, N of them.
    uint32_t konst(size_t n, const std::vector<uint64_t> &c) {
      Op op{K::kConst};
      op.n = uint32_t(n);
      op.t0 = uint32_t(p.consts_.size());
      p.consts_.insert(p.consts_.end(), c.begin(), c.end());
      return add(op);
    }
    uint32_t zeros(size_t n) {
      return konst(n, std::vector<uint64_t>(words(n), 0));
    }
    // The operation of node X, or -1 when X has no program.
    int build(const ExprNode<F> &x) {
      auto it = memo.find(&x);
      if (it != memo.end()) return it->second;
      const int r = make(x);
      memo[&x] = r;
      return r;
    }
    // The operation reading node ID's elements as bits.
    int leaf(size_t id) {
      auto it = leaves.find(id);
      if (it != leaves.end()) return int(it->second);
      const Node &nd = g.nodes.at(id);
      if (nd.type.base != Base::kBit) return -1;
      Op op{K::kLeaf};
      op.n = uint32_t(nd.n);
      op.node = id;
      const uint32_t r = add(op);
      leaves[id] = r;
      return int(r);
    }
    int nary(K k, std::initializer_list<int> in, size_t n) {
      Op op{k};
      op.n = uint32_t(n);
      size_t j = 0;
      for (int x : in) {
        if (x < 0) return -1;
        op.a[j++] = uint32_t(x);
      }
      return int(add(op));
    }
    // Coordinate I of node X as (operation, bit): through views to the
    // first other node.
    bool source(const ExprNode<F> *x, size_t i, uint32_t &op, size_t &bit) {
      while (x->op == ExprOp::kGather) {
        size_t q = x->idx[i], k = 0;
        while (q >= x->kids[k]->n) q -= x->kids[k++]->n;
        x = x->kids[k].get();
        i = q;
      }
      const int r = build(*x);
      if (r < 0) return false;
      op = uint32_t(r);
      bit = i;
      return true;
    }
    bool zero_run(const Run &r) const {
      const Op &s = p.ops_[r.from];
      if (s.k != K::kConst) return false;
      const uint64_t *c = &p.consts_[s.t0];
      for (size_t i = r.src; i < size_t(r.src) + r.len; ++i)
        if ((c[i / 64] >> (i % 64)) & 1) return false;
      return true;
    }
    // The runs of the coordinates AT(0), ..., AT(N - 1) of node X.
    template <class At>
    bool runs_of(const ExprNode<F> *x, size_t n, At at,
                 std::vector<Run> &out) {
      for (size_t d = 0; d < n; ++d) {
        uint32_t op;
        size_t bit;
        if (!source(x, at(d), op, bit)) return false;
        if (!out.empty()) {
          Run &b = out.back();
          if (b.from == op && size_t(b.src) + b.len == bit &&
              size_t(b.dst) + b.len == d) {
            ++b.len;
            continue;
          }
        }
        out.push_back(Run{op, uint32_t(bit), uint32_t(d), 1});
      }
      // A run of zero constants copies nothing: the destination starts
      // zero.
      out.erase(std::remove_if(out.begin(), out.end(),
                               [this](const Run &r) { return zero_run(r); }),
                out.end());
      return true;
    }
    // A select of N outputs whose terms are TERMS, combined by COMBINE.
    uint32_t select(size_t n, const std::vector<std::vector<Run>> &terms,
                    K combine) {
      Op op{K::kSelect};
      op.n = uint32_t(n);
      op.combine = combine;
      op.t0 = uint32_t(p.terms_.size());
      for (const auto &t : terms) {
        p.terms_.push_back(uint32_t(p.runs_.size()));
        p.runs_.insert(p.runs_.end(), t.begin(), t.end());
      }
      op.t1 = uint32_t(p.terms_.size());
      return add(op);
    }
    // COMBINE of term j < W of each group of W coordinates of X: N outputs.
    int grouped(const ExprNode<F> &x, size_t n, size_t w, K combine) {
      std::vector<std::vector<Run>> terms(w);
      for (size_t j = 0; j < w; ++j)
        if (!runs_of(&x, n, [w, j](size_t k) { return k * w + j; },
                     terms[j]))
          return -1;
      return int(select(n, terms, combine));
    }

    int make(const ExprNode<F> &x) {
      switch (x.op) {
        case ExprOp::kLin: {
          int acc = -1;
          for (const auto &t : x.lin.terms) {
            if (!t.chain.empty() || !is01(t.scale)) return -1;
            const int l = leaf(t.node);
            if (l < 0 || p.ops_[size_t(l)].n != x.n) return -1;
            if (t.scale == f().zero()) continue;
            acc = acc < 0 ? l : nary(K::kXor, {acc, l}, x.n);
          }
          return acc < 0 ? int(zeros(x.n)) : acc;
        }
        case ExprOp::kConst: {
          std::vector<uint64_t> c(words(x.n), 0);
          for (size_t i = 0; i < x.n; ++i) {
            if (!is01(x.c[i])) return -1;
            if (x.c[i] == f().one()) c[i / 64] |= uint64_t(1) << (i % 64);
          }
          return int(konst(x.n, c));
        }
        case ExprOp::kScale: {
          if (!is01(x.c.at(0))) return -1;
          const int a = build(*x.kids[0]);
          if (a < 0) return -1;
          return x.c[0] == f().one() ? a : int(zeros(x.n));
        }
        case ExprOp::kAdd:
        case ExprOp::kXor:
        case ExprOp::kMul:
        case ExprOp::kAnd:
        case ExprOp::kOr: {
          const K k = x.op == ExprOp::kAdd || x.op == ExprOp::kXor ? K::kXor
                      : x.op == ExprOp::kOr                        ? K::kOr
                                                                   : K::kAnd;
          int acc = build(*x.kids[0]);
          for (size_t i = 1; i < x.kids.size(); ++i)
            acc = nary(k, {acc, build(*x.kids[i])}, x.n);
          return acc;
        }
        case ExprOp::kNot:
          return nary(K::kNot, {build(*x.kids[0])}, x.n);
        case ExprOp::kMux:
          return nary(K::kMux,
                      {build(*x.kids[0]), build(*x.kids[1]),
                       build(*x.kids[2])},
                      x.n);
        case ExprOp::kSum:
        case ExprOp::kProd:
        case ExprOp::kAny:
        case ExprOp::kAll: {
          const ExprNode<F> &k = *x.kids[0];
          const size_t w = x.w == 0 ? k.n : x.w;
          const K c = x.op == ExprOp::kSum   ? K::kXor
                      : x.op == ExprOp::kAny ? K::kOr
                                             : K::kAnd;
          return grouped(k, x.n, w, c);
        }
        case ExprOp::kBroadcast:
          return nary(K::kFill, {build(*x.kids[0])}, x.n);
        case ExprOp::kGather: {
          std::vector<std::vector<Run>> terms(1);
          if (!runs_of(&x, x.n, [](size_t d) { return d; }, terms[0]))
            return -1;
          // A view that reads one operation whole and in order (a reshape)
          // is that operation.
          const auto &r = terms[0];
          if (r.size() == 1 && r[0].src == 0 && r[0].dst == 0 &&
              r[0].len == x.n && p.ops_[r[0].from].n == x.n)
            return int(r[0].from);
          return int(select(x.n, terms, K::kXor));
        }
        case ExprOp::kMaterialize:
          return build(*x.kids[0]);
        default:
          return -1;
      }
    }
  };

  // Runs the program on V in this thread's memory (zeroed first, as the
  // selects require); returns the output's words, valid until the thread's
  // next run. Each operation reads its operands through SRC: a computed
  // operation's words in the memory, a leaf's packed bits where V keeps
  // them (leaf_bits), so no leaf is copied.
  const uint64_t *execute(const ValueReader &v) const {
    static thread_local std::vector<uint64_t> mem;
    static thread_local std::vector<const uint64_t *> src;
    static thread_local std::vector<std::vector<uint64_t>> spare;
    mem.assign(total_, 0);
    src.assign(ops_.size(), nullptr);
    spare.clear();
    for (size_t i = 0; i < ops_.size(); ++i) {
      const Op &op = ops_[i];
      if (op.k == K::kLeaf) {
        src[i] = leaf_bits(op, v, spare);
        continue;
      }
      exec(op, src.data(), mem.data());
      src[i] = mem.data() + op.at;
    }
    return src[out_];
  }
  // Leaf OP's bits: the packed bits V keeps for its node (a program's
  // output, or an earlier leaf's conversion), else its elements read as
  // bits (ct::bit_of), which V then keeps for the programs that read the
  // node later in the run (in SPARE when V keeps bits of another length
  // under the node).
  const uint64_t *leaf_bits(const Op &op, const ValueReader &v,
                            std::vector<std::vector<uint64_t>> &spare) const {
    const size_t nw = words(op.n);
    const std::vector<uint64_t> *kept = v.packed_bits.find(op.node);
    if (kept != nullptr && kept->size() == nw) return kept->data();
    const auto &x = v.template get<F>(op.node);
    if (x.size() != op.n)
      throw std::runtime_error(
          "a word-level program reads a node of another length");
    std::vector<uint64_t> b(nw, 0);
    const Elt one = f_->one();
    if constexpr (sizeof(Elt) % 8 == 0) {
      // Element i is 1 when its 64-bit units equal one's (a loop that
      // vectorizes; the same bit as ct::equal).
      constexpr size_t kU = sizeof(Elt) / 8;
      uint64_t o[kU];
      std::memcpy(o, &one, sizeof(Elt));
      for (size_t i0 = 0; i0 < op.n; i0 += 64) {
        uint64_t word = 0;
        const size_t e = std::min(size_t(op.n), i0 + 64);
        for (size_t i = i0; i < e; ++i) {
          uint64_t u[kU];
          std::memcpy(u, &x[i], sizeof(Elt));
          uint64_t d = 0;
          for (size_t k = 0; k < kU; ++k) d |= u[k] ^ o[k];
          word |= (ct::nonzero(d) ^ 1) << (i - i0);
        }
        b[i0 / 64] = word;
      }
    } else {
      for (size_t i = 0; i < op.n; ++i)
        b[i / 64] |= ct::equal(x[i], one) << (i % 64);
    }
    std::vector<uint64_t> &slot = kept != nullptr
                                      ? spare.emplace_back()
                                      : v.packed_bits[op.node];
    slot = std::move(b);
    return slot.data();
  }

  // 64 bits of the array S from bit B (zeros past its N_WORDS words).
  static uint64_t get64(const uint64_t *s, size_t n_words, size_t b) {
    const size_t w = b / 64, o = b % 64;
    uint64_t lo = s[w] >> o;
    if (o != 0 && w + 1 < n_words) lo |= s[w + 1] << (64 - o);
    return lo;
  }
  // Copies run R of S (N_WORDS words) into D, whose run bits are zero.
  static void copy(uint64_t *d, const uint64_t *s, size_t n_words,
                   const Run &r) {
    size_t src = r.src, dst = r.dst, len = r.len;
    while (len > 0) {
      const size_t o = dst % 64;
      const size_t k = std::min(len, size_t(64) - o);
      uint64_t b = get64(s, n_words, src);
      if (k < 64) b &= (uint64_t(1) << k) - 1;
      d[dst / 64] |= b << o;
      src += k;
      dst += k;
      len -= k;
    }
  }

  void exec(const Op &op, const uint64_t *const *src, uint64_t *mem) const {
    uint64_t *d = mem + op.at;
    const size_t nw = words(op.n);
    auto in = [&](size_t i) { return src[op.a[i]]; };
    // Bits past N stay zero.
    const uint64_t tail =
        op.n % 64 == 0 ? ~uint64_t(0) : (uint64_t(1) << (op.n % 64)) - 1;
    switch (op.k) {
      case K::kLeaf:
        // Read in place (execute).
        break;
      case K::kConst:
        std::copy(&consts_[op.t0], &consts_[op.t0] + nw, d);
        break;
      case K::kXor: {
        const uint64_t *a = in(0), *b = in(1);
        for (size_t i = 0; i < nw; ++i) d[i] = a[i] ^ b[i];
        break;
      }
      case K::kAnd: {
        const uint64_t *a = in(0), *b = in(1);
        for (size_t i = 0; i < nw; ++i) d[i] = a[i] & b[i];
        break;
      }
      case K::kOr: {
        const uint64_t *a = in(0), *b = in(1);
        for (size_t i = 0; i < nw; ++i) d[i] = a[i] | b[i];
        break;
      }
      case K::kNot: {
        const uint64_t *a = in(0);
        for (size_t i = 0; i < nw; ++i) d[i] = ~a[i];
        d[nw - 1] &= tail;
        break;
      }
      case K::kMux: {
        const uint64_t *c = in(0), *t = in(1), *e = in(2);
        for (size_t i = 0; i < nw; ++i) d[i] = e[i] ^ (c[i] & (t[i] ^ e[i]));
        break;
      }
      case K::kFill: {
        const uint64_t m = uint64_t(0) - (in(0)[0] & 1);
        for (size_t i = 0; i < nw; ++i) d[i] = m;
        d[nw - 1] &= tail;
        break;
      }
      case K::kSelect: {
        uint64_t *t = mem + scratch_;
        for (uint32_t j = op.t0; j < op.t1; ++j) {
          uint64_t *dst = d;
          if (j > op.t0) {
            std::fill(t, t + nw, 0);
            dst = t;
          }
          const uint32_t r1 =
              j + 1 < terms_.size() ? terms_[j + 1] : uint32_t(runs_.size());
          for (uint32_t r = terms_[j]; r < r1; ++r) {
            const Run &run = runs_[r];
            copy(dst, src[run.from], words(ops_[run.from].n), run);
          }
          if (j == op.t0) continue;
          if (op.combine == K::kXor) {
            for (size_t i = 0; i < nw; ++i) d[i] ^= t[i];
          } else if (op.combine == K::kOr) {
            for (size_t i = 0; i < nw; ++i) d[i] |= t[i];
          } else {
            for (size_t i = 0; i < nw; ++i) d[i] &= t[i];
          }
        }
        break;
      }
    }
  }

  const F *f_;
  std::vector<Op> ops_;
  std::vector<Run> runs_;
  std::vector<uint32_t> terms_;
  std::vector<uint64_t> consts_;
  uint32_t out_ = 0;
  size_t n_ = 0, total_ = 0, scratch_ = 0;
};

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_BIT_EVAL_H_
