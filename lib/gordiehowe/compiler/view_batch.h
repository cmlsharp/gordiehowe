// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the realizations of a placed batch, over the operand maps
// built from its predicates' views (view_map.h).
//
//   ViewBitOperands    Bit operands in characteristic 2: the bit-sliced
//                      first round (BasicBooleanSkip's chi kernel when Q is
//                      a b + c, RuntimeBooleanSkip otherwise), the claim on
//                      the tables' words in W Frobenius forms, which joins
//                      the bit node's stage.
//   ViewFieldOperands  field-element operands of one subfield (or the
//                      field): the first round evaluated in F, the claim as
//                      one form on the tables' coordinates.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_VIEW_BATCH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_VIEW_BATCH_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/batch.h"
#include "gordiehowe/compiler/batch_form.h"
#include "gordiehowe/compiler/bit_skip.h"
#include "gordiehowe/compiler/field_skip.h"
#include "gordiehowe/compiler/view_map.h"
#include "sumcheck/boolean_skip.h"
#include "util/parallel.h"

namespace proofs::gordiehowe::compiler {

// Q of a batched form as a relation over its operands.
template <class F>
FieldRelation<F> form_relation(const BatchForm<F> &q, const std::string &nm) {
  FieldRelation<F> rel;
  rel.name = nm;
  rel.operands = unsigned(q.atoms.size());
  for (const auto &m : q.monos) rel.monomials.push_back({m.coeff, m.ops});
  return rel;
}

// Whether Q is chi, x y + z on three distinct operands with coefficients 1;
// then ORDER is (x, y, z).
template <class F>
bool chi_shaped(const F &f, const FieldRelation<F> &q,
                std::array<unsigned, 3> &order) {
  if (q.operands != 3 || q.monomials.size() != 2) return false;
  const auto *two = &q.monomials[0], *one = &q.monomials[1];
  if (two->ops.size() == 1) std::swap(two, one);
  if (two->ops.size() != 2 || one->ops.size() != 1) return false;
  if (two->coeff != f.one() || one->coeff != f.one()) return false;
  order = {two->ops[0], two->ops[1], one->ops[0]};
  return order[0] != order[1] && order[0] != order[2] && order[1] != order[2];
}

// Public values by space, packed in lanes.
template <class F>
std::vector<std::vector<uint64_t>> public_lanes(const F &f,
                                                const BatchPublics<F> &pub) {
  std::vector<std::vector<uint64_t>> out(pub.values.size());
  for (size_t s = 0; s < pub.values.size(); ++s) {
    if (pub.values[s] == nullptr) continue;
    const auto &x = *pub.values[s];
    out[s].assign((x.size() + 63) / 64, 0);
    for (size_t i = 0; i < x.size(); ++i)
      if (x[i] == f.one()) out[s][i / 64] |= uint64_t(1) << (i % 64);
  }
  return out;
}

template <class F, size_t W = 16>
class ViewBitOperands final : public BatchOperands<F> {
 public:
  using Elt = typename F::Elt;
  using Skip = MaskedFieldSkip<F>;
  using Map = BitViewMap<F, W>;

  ViewBitOperands(const F &f, FieldRelation<F> rel,
                  std::shared_ptr<const Map> map, unsigned width)
      : f_(f), rel_(std::move(rel)), map_(std::move(map)), width_(width),
        bits_(SubfieldInfo<F>::get(f, W)) {
    for (const auto &m : rel_.monomials) {
      check(m.coeff == f.one(), "a bit batch's coefficients are 1");
      monos_.push_back(m.ops);
    }
    chi_ = chi_shaped(f, rel_, order_);
    if (chi_) {
      // The kernel's operands are (x, y, z) of x y + z: renumbered.
      FieldRelation<F> r;
      r.name = rel_.name;
      r.operands = 3;
      r.monomials = {{f.one(), {0, 1}}, {f.one(), {2}}};
      rel_ = std::move(r);
      chi_skip_ = std::make_unique<BasicBooleanSkip<F, SkipChi>>(f, width);
    } else {
      run_skip_ = std::make_unique<RuntimeBooleanSkip<F>>(
          f, rel_.operands, monos_, width);
    }
    if constexpr (W == 16 && domain_subfield<F>::kBitWords)
      decode_ = std::make_unique<SubfieldDecoder<F>>(f);
    // The bit phase's decoder of the words' bits (the basis beta_k of the
    // first round's decode).
    if constexpr (W == 16 && domain_subfield<F>::kBitWords &&
                  !IsCountingField<F>::value) {
      std::vector<Elt> beta;
      for (size_t k = 0; k < W; ++k) beta.push_back(f.beta(k));
      pivots_ = PivotDecoder<F>(f, beta);
    }
  }

  size_t words() const override { return map_->words(); }
  size_t word_degree() const override { return W; }
  bool bit_operands() const override { return true; }
  size_t instances() const override { return map_->lanes() * 64; }
  FieldRelation<F> relation(const Elt &) const override { return rel_; }
  void describe(std::vector<uint8_t> &out, unsigned width) const override {
    put_str(out, "bit-view-skip/bit-node-claim");
    put_u64(out, rel_.operands);
    put_u64(out, rel_.monomials.size());
    for (const auto &m : rel_.monomials) {
      put_u64(out, m.ops.size());
      for (unsigned j : m.ops) put_u64(out, j);
    }
    put_u64(out, width);
    put_str(out, map_->name());
    const auto p = map_->params();
    put_u64(out, p.size());
    out.insert(out.end(), p.begin(), p.end());
  }
  std::string report(const Skip &sk, size_t pads,
                     size_t message_elts) const override {
    return "bit-sliced skip: Q degree " + std::to_string(sk.D) + " in " +
           std::to_string(sk.K) + " operands, " +
           std::to_string(map_->predicates()) + " predicates in " +
           std::to_string(map_->templates()) + " templates, " +
           std::to_string(map_->lanes()) + " lanes, width " +
           std::to_string(sk.width()) + ", " +
           std::to_string(sk.layout.logs) + " rounds, " +
           std::to_string(pads) + " pads, " + std::to_string(message_elts) +
           " message elements";
  }
  size_t shape_instances() const override { return map_->lanes(); }
  std::vector<std::string> parts() const override { return {rel_.name}; }
  std::vector<size_t> public_nodes() const override {
    std::vector<size_t> out;
    bool any = false;
    for (const auto &s : map_->spaces()) {
      out.push_back(s.kind == BatchSpace::kPublic ? s.node : SIZE_MAX);
      any = any || s.kind == BatchSpace::kPublic;
    }
    return any ? out : std::vector<size_t>{};
  }

  std::unique_ptr<SkipOperands<F>> first_round(
      const Skip &, const std::vector<Elt> &words,
      const BatchPublics<F> &pub, BatchScratch<F> *scratch) const override {
    // The tables, lanes and rows are SCRATCH's when given
    // (prover_scratch.h), this call's own otherwise.
    BatchScratch<F> own;
    BatchScratch<F> &buf = scratch != nullptr ? *scratch : own;
    // Each table's host words as lanes. The lanes of all the table spaces
    // are numbered in one range, which runs in chunks under a runner
    // (util/parallel.h), each chunk writing its own lanes: one dispatch per
    // first round, where a batch over many small spaces (SHA3-256's, of 25
    // lanes each) would otherwise dispatch per space, its chunks a few lanes
    // that share cache lines. The boundaries depend on the spaces' sizes
    // only.
    auto phase = std::make_unique<profiling::Scope>("batch.first_round.decode");
    const auto &sp = map_->spaces();
    std::vector<std::vector<uint64_t>> &tables = buf.tables;
    tables.resize(sp.size());
    // Per table space: its index, its first lane in the range and its first
    // word in WORDS; a last entry closes the range.
    std::vector<size_t> ts, lane0(1, 0), word0(1, 0);
    for (size_t s = 0; s < sp.size(); ++s) {
      if (sp[s].kind != BatchSpace::kTable) {
        tables[s].clear();
        continue;
      }
      const size_t nw = (sp[s].size + W - 1) / W;
      const size_t nl = (nw + Map::kChunks - 1) / Map::kChunks;
      tables[s].assign(nl, 0);
      ts.push_back(s);
      lane0.push_back(lane0.back() + nl);
      word0.push_back(word0.back() + nw);
    }
    check(word0.back() == words.size(), "bit view batch: table words");
    const size_t nlanes = lane0.back();
    parallel::for_chunks(
        nlanes, parallel::grain_for(nlanes, parallel::kChunks),
        [&](size_t g0, size_t g1) {
          // The space of lane G0, then each space the chunk reaches.
          size_t k = size_t(std::upper_bound(lane0.begin(), lane0.end(), g0) -
                            lane0.begin()) -
                     1;
          for (size_t g = g0; g < g1; ++k) {
            const size_t e = std::min(g1, lane0[k + 1]);
            const size_t nw = word0[k + 1] - word0[k];
            const Elt *wk = words.data() + word0[k];
            uint64_t *tab = tables[ts[k]].data();
            const size_t q1 = std::min(nw, (e - lane0[k]) * Map::kChunks);
            for (size_t q = (g - lane0[k]) * Map::kChunks; q < q1; ++q) {
              const uint64_t h = decode_ ? uint64_t((*decode_)(wk[q]))
                                         : bits_.bits(f_, wk[q]);
              tab[q / Map::kChunks] |= h << (W * (q % Map::kChunks));
            }
            g = e;
          }
        });
    phase = std::make_unique<profiling::Scope>("batch.first_round.apply");
    std::vector<uint64_t> &lanes = buf.lanes;
    map_->apply_into(tables, public_lanes(f_, pub), lanes);
    phase = std::make_unique<profiling::Scope>("batch.first_round.rows");
    const unsigned K = map_->operands();
    // In the scratch's first proof the tables and lanes go back to the
    // allocator once the rows are made (BatchScratch::keep).
    auto done = [&buf](std::unique_ptr<SkipOperands<F>> ops) {
      if (!buf.keep) {
        release(buf.tables);
        release(buf.lanes);
      }
      return ops;
    };
    if (chi_) {
      // The kernel's rows straight from the lanes, in chunks under a
      // runner (BasicBooleanSkip::rows_of).
      const uint64_t *const ln = lanes.data();
      const std::array<unsigned, 3> ord = order_;
      using Rows = typename BasicBooleanSkip<F, SkipChi>::Rows;
      Rows &rows = buf.template rows<Rows>();
      chi_skip_->rows_of_into(
          map_->lanes(),
          [ln, ord, K](size_t l, unsigned j) { return ln[l * K + ord[j]]; },
          rows);
      if (scratch == nullptr)
        return std::make_unique<BitSkipOperands<F, SkipChi>>(*chi_skip_,
                                                             std::move(rows));
      return done(
          std::make_unique<BitSkipOperands<F, SkipChi>>(*chi_skip_, rows));
    }
    size_t n = 0;
    using Rows = typename RuntimeBooleanSkip<F>::Rows;
    Rows &rows = buf.template rows<Rows>();
    run_skip_->rows_into(lanes, n, rows);
    if (scratch == nullptr)
      return std::make_unique<RuntimeBitSkipOperands<F>>(*run_skip_,
                                                         std::move(rows), n);
    return done(
        std::make_unique<RuntimeBitSkipOperands<F>>(*run_skip_, rows, n));
  }
  // The first round's byte-lane steps: at each of the (D - 1)(w - 1) skip
  // points, per 16 rows (the live rows, the lanes' 64 / w each), one table
  // lookup per operand and byte of the width, and one skip-subfield
  // product per further factor of a monomial; and the map's lane terms.
  OpCounts lane_work(unsigned width) const override {
    OpCounts c;
    const size_t rows = map_->lanes() * (64 / width);
    const uint64_t points = uint64_t(rel_.degree() - 1) * (width - 1);
    const uint64_t blocks = (rows + 15) / 16, chunks = (width + 7) / 8;
    uint64_t factors = 0;
    for (const auto &m : rel_.monomials) factors += m.ops.size() - 1;
    c.lane_lookup = points * blocks * rel_.operands * chunks;
    c.lane_mul = points * blocks * factors;
    c.lane_term = map_->lane_terms();
    return c;
  }
  SkipKind skip_kind() const override {
    return chi_ ? SkipKind::kBitChi : SkipKind::kBitRuntime;
  }
  void map_work(unsigned width) const override {
    const auto &sp = map_->spaces();
    std::vector<std::vector<uint64_t>> tables(sp.size()), publics(sp.size());
    for (size_t s = 0; s < sp.size(); ++s) {
      const size_t lanes = ((sp[s].size + W - 1) / W + Map::kChunks - 1) /
                           Map::kChunks;
      (sp[s].kind == BatchSpace::kTable ? tables : publics)[s].assign(
          sp[s].kind == BatchSpace::kTable ? lanes : (sp[s].size + 63) / 64,
          0);
    }
    (void)map_->apply(tables, publics);
    size_t rounds = 0;
    while ((size_t(1) << rounds) * width < map_->lanes() * 64) ++rounds;
    (void)map_->adjoint(width, std::vector<Elt>(width, f_.one()),
                        std::vector<Elt>(rounds, f_.one()),
                        std::vector<Elt>(rel_.operands, f_.one()), publics);
  }
  BitForms<F> forms(const Skip &, const typename Skip::Context &ctx,
                    const BatchPublics<F> &pub) const override {
    const auto lb =
        chi_ ? chi_skip_->bit_basis(ctx.r) : run_skip_->bit_basis(ctx.r);
    // The claims in the map's operand order.
    std::vector<Elt> u(ctx.u.begin(), ctx.u.end());
    if (chi_)
      for (size_t i = 0; i < 3; ++i) u[order_[i]] = ctx.u[i];
    return map_->adjoint(width_, lb, ctx.s, u, public_lanes(f_, pub));
  }

  // The bit phase (bit_phase.h) on GF(2^16) words: the map's word weights
  // and weight classes at the terminal claims' point.
  bool bit_phase_supported() const override {
    return W == 16 && !IsCountingField<F>::value;
  }
  void prepare_bit_phase() const override { map_->prepare_bit_phase(); }
  BitForms<F> word_weights(const Skip &, const typename Skip::Context &ctx,
                           const BatchPublics<F> &pub,
                           const std::vector<Elt> &eq) const override {
    return map_->word_weights(width_, basis_at(ctx), ctx.s, map_order(ctx),
                              public_lanes(f_, pub), eq);
  }
  void bit_phase_tables(const Skip &, const typename Skip::Context &ctx,
                        const std::vector<Elt> &words, std::vector<Elt> &sigma,
                        std::vector<Elt> &g) const override {
    if constexpr (F::kCharacteristicTwo && !IsCountingField<F>::value) {
      // The table words' bits, in chunks under a runner: their pivot bits
      // g = t A (PivotDecoder, GFNI) where the target has the kernel, the
      // classes' sums then taken back to the words' basis (t = g A^-1);
      // elsewhere their coordinates t as the first round decodes them.
      const bool by_pivots = pivots_.has_kernel();
      std::vector<uint64_t> host(words.size());
      {
        profiling::Scope sc("batch.bitphase.decode");
        const size_t n = words.size();
        std::vector<uint8_t> lo, hi;
        if (by_pivots) {
          lo.resize(n);
          hi.resize(n);
        }
        parallel::for_chunks(
            n, parallel::grain_for(n, parallel::kChunks),
            [&](size_t b, size_t e) {
              if (by_pivots) {
                pivots_.pivots([&](size_t q) -> const Elt & { return words[q]; },
                               b, e, lo.data(), hi.data());
                for (size_t q = b; q < e; ++q)
                  host[q] = uint64_t(lo[q]) | (uint64_t(hi[q]) << 8);
                return;
              }
              for (size_t q = b; q < e; ++q)
                host[q] = decode_ ? uint64_t((*decode_)(words[q]))
                                  : bits_.bits(f_, words[q]);
            });
      }
      map_->bit_phase_tables(width_, basis_at(ctx), ctx.s, map_order(ctx),
                             host, sigma, g);
      if (by_pivots) {
        // G[b] = XOR over i of (A^-1)_{i,b} G'[i], per class.
        std::array<Elt, W> gp;
        for (size_t k = 0; k * W < g.size(); ++k) {
          for (size_t i = 0; i < W; ++i) gp[i] = g[k * W + i];
          for (size_t b = 0; b < W; ++b) {
            Elt s = f_.zero();
            for (size_t i = 0; i < W; ++i)
              if ((pivots_.inv(i) >> b) & 1) f_.add(s, gp[i]);
            g[k * W + b] = s;
          }
        }
      }
    }
  }
  std::vector<Elt> bit_dual() const override { return map_->dual(); }

 private:
  // The skip's Lagrange weights at the terminal claims' skip point.
  std::vector<Elt> basis_at(const typename Skip::Context &ctx) const {
    return chi_ ? chi_skip_->bit_basis(ctx.r) : run_skip_->bit_basis(ctx.r);
  }
  // The claims' combination u in the map's operand order.
  std::vector<Elt> map_order(const typename Skip::Context &ctx) const {
    std::vector<Elt> u(ctx.u.begin(), ctx.u.end());
    if (chi_)
      for (size_t i = 0; i < 3; ++i) u[order_[i]] = ctx.u[i];
    return u;
  }
  const F &f_;
  FieldRelation<F> rel_;
  std::vector<std::vector<unsigned>> monos_;
  std::shared_ptr<const Map> map_;
  unsigned width_;
  bool chi_ = false;
  std::array<unsigned, 3> order_{};
  std::unique_ptr<BasicBooleanSkip<F, SkipChi>> chi_skip_;
  std::unique_ptr<RuntimeBooleanSkip<F>> run_skip_;
  std::unique_ptr<SubfieldDecoder<F>> decode_;
  PivotDecoder<F> pivots_;
  const SubfieldInfo<F> &bits_;
};

template <class F>
class ViewFieldOperands final : public BatchOperands<F> {
 public:
  using Elt = typename F::Elt;
  using Skip = MaskedFieldSkip<F>;
  using Map = FieldViewMap<F>;

  ViewFieldOperands(const F &f, FieldRelation<F> rel,
                    std::shared_ptr<const Map> map, size_t word_degree,
                    BatchEval eval)
      : f_(f), rel_(std::move(rel)), map_(std::move(map)),
        word_degree_(word_degree), eval_(eval) {}

  size_t words() const override { return map_->words(); }
  size_t word_degree() const override { return word_degree_; }
  bool bit_operands() const override { return false; }
  size_t instances() const override { return map_->instances(); }
  FieldRelation<F> relation(const Elt &) const override { return rel_; }
  void describe(std::vector<uint8_t> &out, unsigned width) const override {
    put_str(out, "field-view-skip");
    put_u64(out, uint64_t(eval_));
    put_u64(out, rel_.operands);
    put_u64(out, rel_.monomials.size());
    for (const auto &m : rel_.monomials) {
      uint8_t b[F::kBytes];
      f_.to_bytes_field(b, m.coeff);
      out.insert(out.end(), b, b + F::kBytes);
      put_u64(out, m.ops.size());
      for (unsigned j : m.ops) put_u64(out, j);
    }
    put_u64(out, width);
    put_u64(out, word_degree_);
    put_str(out, map_->name());
    const auto p = map_->params();
    put_u64(out, p.size());
    out.insert(out.end(), p.begin(), p.end());
  }
  std::string report(const Skip &sk, size_t pads,
                     size_t message_elts) const override {
    return std::string(batch_eval_name(eval_)) + " skip: Q degree " +
           std::to_string(sk.D) + " in " + std::to_string(sk.K) +
           " operands, " + std::to_string(map_->predicates()) +
           " predicates, " + std::to_string(sk.rows) + " instances, width " +
           std::to_string(sk.width()) + ", skip domain " +
           std::to_string(sk.dom.points()) +
           (F::kCharacteristicTwo ? " points of the additive GF(2^8) subspace"
                                  : " consecutive integers") +
           ", " + std::to_string(sk.layout.logs) + " rounds, " +
           std::to_string(pads) + " pads, " + std::to_string(message_elts) +
           " message elements";
  }
  std::vector<std::string> parts() const override { return {rel_.name}; }
  std::vector<size_t> public_nodes() const override {
    std::vector<size_t> out;
    bool any = false;
    for (const auto &s : map_->spaces()) {
      out.push_back(s.kind == BatchSpace::kPublic ? s.node : SIZE_MAX);
      any = any || s.kind == BatchSpace::kPublic;
    }
    return any ? out : std::vector<size_t>{};
  }
  std::unique_ptr<SkipOperands<F>> first_round(
      const Skip &, const std::vector<Elt> &words,
      const BatchPublics<F> &pub, BatchScratch<F> *) const override {
    auto ops = map_->apply(words, publics(pub));
    return std::make_unique<FieldSkipOperands<F>>(std::move(ops));
  }
  void map_work(unsigned) const override {
    std::vector<std::vector<Elt>> values;
    std::vector<const std::vector<Elt> *> pub;
    for (const auto &s : map_->spaces())
      values.push_back(std::vector<Elt>(
          s.kind == BatchSpace::kPublic ? s.size : 0, f_.zero()));
    for (const auto &v : values) pub.push_back(&v);
    (void)map_->apply(std::vector<Elt>(map_->words(), f_.zero()), pub);
    std::vector<Elt> a;
    Elt c;
    map_->adjoint(std::vector<Elt>(map_->instances(), f_.one()),
                  std::vector<Elt>(rel_.operands, f_.one()), pub, a, c);
  }
  BitForms<F> forms(const Skip &sk, const typename Skip::Context &ctx,
                    const BatchPublics<F> &pub) const override {
    const auto weight = sk.instance_weights(ctx);
    BitForms<F> out{{}, f_.zero(), words()};
    map_->adjoint(weight, ctx.u, publics(pub), out.a, out.constant);
    return out;
  }

 private:
  std::vector<const std::vector<Elt> *> publics(
      const BatchPublics<F> &pub) const {
    std::vector<const std::vector<Elt> *> out = pub.values;
    out.resize(map_->spaces().size(), nullptr);
    return out;
  }
  const F &f_;
  FieldRelation<F> rel_;
  std::shared_ptr<const Map> map_;
  size_t word_degree_;
  BatchEval eval_;
};

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_VIEW_BATCH_H_
