// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the batched-relation constraint kind.
//
// A batched relation says: for every instance t, Q(L_1(W, t), ...,
// L_K(W, t)) = 0, where Q is a polynomial of bounded degree and each
// operand L_j is an affine view of phase-0 tables W. A domain proves its
// batched relations as reductions inside its proof: masked messages in the
// pad-dependency order, then rows of the domain's opening.
//
// One protocol driver proves every batch: BatchKernel runs the masked
// univariate-skip zerocheck of field_skip.h (MaskedFieldSkip: the skip
// domain, masked messages in pad order, the rounds, the terminal check),
// and ends at one linear row on the table words, which the domain's packing
// tree opens. A realization (BatchOperands) supplies what depends on the
// operand type:
//   - BitOperands<F, R, W>: characteristic 2, operands the bits of GF(2^W)
//     table words, read through a BitOperandMap (keccak.h, sha256.h). Its
//     first round is the bit-sliced kernel of sumcheck/boolean_skip.h, 64
//     rows per word operation and 16 per register shuffle; its row's part
//     on the table words is the W Frobenius trace forms of the map's
//     adjoint, a claim on the words' bits that joins the bit node's stage
//     (tree_zk.h).
//   - FieldOperands<F>: operands field elements of one subfield, in any
//     characteristic, read through FieldOperandMaps; several relations of
//     the same instances may be merged as sum_i gamma^i Q_i. Its first
//     round is evaluated generically in F, and its row's part on the table
//     words is one form, opened from the subfield's node.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BATCH_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BATCH_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "arrays/eqs.h"
#include "gordiehowe/core.h"
#include "gordiehowe/compiler/bit_phase.h"
#include "gordiehowe/compiler/counting_field.h"
#include "gordiehowe/compiler/field_skip.h"
#include "gordiehowe/compiler/packing.h"
#include "gordiehowe/compiler/test_switches.h"
#include "ligero/ligero_param.h"
#include "sumcheck/boolean_skip.h"
#include "zk/zk_packed.h"

namespace proofs::gordiehowe::compiler {

// ------------------------------------------------------- realization --

// The public values a batch's operands read, by the batch's space index
// (null for a space that is not public): both parties know them when they
// prove and verify, so they enter the operands' constant parts.
template <class F>
struct BatchPublics {
  std::vector<const std::vector<typename F::Elt> *> values;
};

// The first round a batch's skip runs: field operands, the bit-sliced chi
// kernel (x y + z), or the bit-sliced kernel of any relation.
enum class SkipKind : uint8_t { kField, kBitChi, kBitRuntime };

// What a batch's operand type decides: the tables it reads, the relation
// the driver proves, the prover's first round, and the terminal row's part
// on the table words.
template <class F>
class BatchOperands {
 public:
  using Elt = typename F::Elt;
  using Skip = MaskedFieldSkip<F>;
  virtual ~BatchOperands() = default;
  // Table words the relation reads (its tables, concatenated), and their
  // subfield's degree over the prime field.
  virtual size_t words() const = 0;
  virtual size_t word_degree() const = 0;
  // Whether the operands are the bits of the table words (the claim joins
  // the bit node's stage).
  virtual bool bit_operands() const = 0;
  // The zerocheck's instances.
  virtual size_t instances() const = 0;
  // The relations merged as sum_i gamma^i Q_i (one for most).
  virtual size_t relations() const { return 1; }
  // sum_i gamma^i Q_i over the concatenated operands.
  virtual FieldRelation<F> relation(const Elt &gamma) const = 0;
  virtual void describe(std::vector<uint8_t> &out, unsigned width) const = 0;
  virtual std::string report(const Skip &sk, size_t pads,
                             size_t message_elts) const = 0;
  // The plan export's instances (bit operands: the 64-bit lanes), the
  // merged relations' names, and the instances of each call sharing the
  // relation (empty for one call).
  virtual size_t shape_instances() const { return instances(); }
  virtual std::vector<std::string> parts() const = 0;
  virtual std::vector<size_t> call_instances() const { return {}; }
  // The public nodes the operands read, by space index (SIZE_MAX for a
  // space that is not public); empty when they read none.
  virtual std::vector<size_t> public_nodes() const { return {}; }
  // The prover's first round over the table words. Its tables, lanes and
  // rows are SCRATCH's when given (prover_scratch.h): the operands it
  // returns read them, so SCRATCH outlives the operands.
  virtual std::unique_ptr<SkipOperands<F>> first_round(
      const Skip &sk, const std::vector<Elt> &words,
      const BatchPublics<F> &pub, BatchScratch<F> *scratch) const = 0;
  // The terminal operand claims, combined by ctx.u: constant + the forms'
  // part on the table words (one form, or the W Frobenius trace forms of a
  // claim on their bits).
  virtual BitForms<F> forms(const Skip &sk, const typename Skip::Context &ctx,
                            const BatchPublics<F> &pub) const = 0;
  // The byte-lane work of one proof at skip WIDTH (bit operands; op_counts.h),
  // which no field operation counts.
  virtual OpCounts lane_work(unsigned width) const { return {}; }
  // The first round's kernel, and the operand map's work in one proof: its
  // operands from zero table words and its forms (op_counts.h; over
  // CountingField the field operations are counted).
  virtual SkipKind skip_kind() const { return SkipKind::kField; }
  virtual void map_work(unsigned width) const {}

  // The bit phase (bit_phase.h): bit operands on 16-bit table words whose
  // claim coefficients the realization reads per weight class.
  virtual bool bit_phase_supported() const { return false; }
  // Builds what the prover's tables read (at compile time).
  virtual void prepare_bit_phase() const {}
  // alpha_q = sum_b EQ[b] W_q[b] per table word (a, one form) and the
  // terminal claims' constant: the adjoint with one weight per word.
  virtual BitForms<F> word_weights(const Skip &sk,
                                   const typename Skip::Context &ctx,
                                   const BatchPublics<F> &pub,
                                   const std::vector<Elt> &eq) const {
    check(false, "the bit phase on operands without it");
    return {};
  }
  // The prover's weight classes over the table WORDS: SIGMA and G, 16 per
  // class (BitViewMap::bit_phase_tables).
  virtual void bit_phase_tables(const Skip &sk,
                                const typename Skip::Context &ctx,
                                const std::vector<Elt> &words,
                                std::vector<Elt> &sigma,
                                std::vector<Elt> &g) const {
    check(false, "the bit phase on operands without it");
  }
  // The trace-dual basis of the table words' bits (BitForms' contraction).
  virtual std::vector<Elt> bit_dual() const { return {}; }
};

// ------------------------------------------------------------- kernel --


// One batched relation, proved by the masked skip. Indices into the
// committed witness are Ligero witness coordinates (circuit input minus
// the public inputs). HASH is the domain's protocol hash. Messages, in
// transcript order: the skip values, D per sumcheck round, the K terminal
// values. Rows: the terminal check and the opening row.
template <class F, class Hash>
class BatchKernel {
 public:
  using Elt = typename F::Elt;
  using Transcript = BasicTranscript<Hash>;
  using Llc = LigeroLinearConstraint<F>;
  using Skip = MaskedFieldSkip<F>;

  // The rows the reduction adds to the domain's opening: sparse terms A, B
  // (row indices from 0), and the opening row's part on the table words,
  // FORMS (row FORM_ROW).
  //   BIT_CLAIM false: one form, the row's coefficients on the table words.
  //   BIT_CLAIM true: the row is a claim on the bits of the table words,
  //     its bit part sum_k Frob^k(<a_k, W>) with a_k FORMS's form k: it
  //     joins the bit node's stage (tree_zk.h), whose measurement opens it
  //     with the stage's other claims. With the bit phase the claim is
  //     PRODUCT (bit_phase.h) in place of FORMS.
  struct Rows {
    std::vector<Llc> a;
    std::vector<Elt> b;
    size_t form_row = 0;
    std::shared_ptr<const BitForms<F>> forms;
    std::shared_ptr<const ProductClaim<F>> product;
    bool bit_claim = false;
  };
  // The relation's shape (the plan export): K operands, degree D, the
  // instances, the skip width, the sumcheck rounds, and the relations
  // merged as sum_i gamma^i Q_i (their names; one for a single relation).
  struct Shape {
    size_t arity = 0, degree = 0, instances = 0, width = 0, rounds = 0;
    std::vector<std::string> parts;
    // The instances of each call sharing the relation (its tables in
    // order); empty for one call.
    std::vector<size_t> call_instances = {};
  };
  // A test's cheating prover (reduce; empty for an honest one). MESSAGES
  // changes the prover's messages before they are absorbed. SWAP_ROUND >= 0
  // masks the bit phase's round SWAP_ROUND's two messages with each other's
  // pads (the committed pads unchanged), which the verifier must reject.
  struct Tamper {
    std::function<void(std::vector<Elt> &)> messages;
    int swap_round = -1;
  };

  // BIT_PHASE: the bit phase (bit_phase.h) after the zerocheck, for bit
  // operands that support it (16-bit table words); others ignore it.
  BatchKernel(const F &f, std::shared_ptr<const BatchOperands<F>> ops,
              unsigned width, bool bit_phase = false)
      : f_(f), ops_(std::move(ops)), width_(width),
        skip_(f, ops_->relation(f.one()), ops_->instances(), width),
        bit_phase_(bit_phase && ops_->bit_operands() &&
                   ops_->bit_phase_supported()) {
    if (bit_phase_) ops_->prepare_bit_phase();
  }

  size_t words() const { return ops_->words(); }
  bool bit_operands() const { return ops_->bit_operands(); }
  std::vector<size_t> public_nodes() const { return ops_->public_nodes(); }
  size_t word_degree() const { return ops_->word_degree(); }
  // The skip polynomial's D (w - 1) + 1 points.
  size_t skip_points() const { return skip_.dom.points(); }
  // The bit phase's rounds (0 without it).
  size_t bit_phase_rounds() const {
    return bit_phase_ ? BitPhaseShape::kRounds : 0;
  }
  // Committed pads the reduction owns, and their quadratic constraints
  // (relative to pad 0): the zerocheck's, then the bit phase's (full-field
  // pads without products).
  size_t pads() const {
    return skip_.layout.count + (bit_phase_ ? BitPhaseShape::kPads : 0);
  }
  std::vector<LigeroQuadraticConstraint> pad_quadratic() const {
    return skip_.pad_quadratic;
  }
  void fill_pads(Elt *p, RandomEngine &rng) const {
    skip_.fill_pads(p, rng);
    if (bit_phase_)
      for (size_t i = 0; i < BitPhaseShape::kPads; ++i)
        p[skip_.layout.count + i] = rng.elt(f_);
  }
  // Masked field elements in the reduction transcript.
  size_t message_elts() const {
    return skip_.message_elts() + (bit_phase_ ? BitPhaseShape::kMessages : 0);
  }
  // The byte-lane work of one proof (op_counts.h).
  OpCounts lane_work() const { return ops_->lane_work(width_); }
  // The terminal check and the opening row.
  size_t reduction_rows() const { return 2; }
  void describe(std::vector<uint8_t> &out) const {
    ops_->describe(out, width_);
    if (bit_phase_) {
      put_str(out, "bit-sumcheck/v1");
      put_u64(out, BitPhaseShape::kRounds);
    }
  }
  std::string report() const {
    std::string r = ops_->report(skip_, pads(), message_elts());
    if (bit_phase_)
      r += ", bit phase of " + std::to_string(BitPhaseShape::kRounds) +
           " rounds";
    return r;
  }
  Shape shape() const {
    return {skip_.K,
            skip_.D,
            ops_->shape_instances(),
            width_,
            skip_.layout.logs,
            ops_->parts(),
            ops_->call_instances()};
  }

  // Runs the reduction on T. The prover passes the table words and the pads,
  // and receives MESSAGES; the verifier passes MESSAGES from the proof. PAD_AT
  // is the witness coordinate of pad 0. TAMPER.messages (tests only) changes
  // the prover's messages before they are absorbed: it sees every message, the
  // bit phase's as zeros, and its change to a bit-phase message is added when
  // that message is absorbed. The later rounds are not recomputed from the
  // changed transcript, so this is a tampered message, not an adaptive cheater.
  // The prover's working buffers are SCRATCH's when given
  // (prover_scratch.h).
  Rows reduce(Transcript &t, std::vector<Elt> &messages, size_t pad_at,
              const std::vector<Elt> *words, const Elt *pads,
              const Tamper &tamper,
              const BatchPublics<F> &pub = BatchPublics<F>{},
              BatchScratch<F> *scratch = nullptr) const {
    const F &f = f_;
    // gamma, when several relations share the zerocheck. The prover's
    // zerocheck runs on a clone taken before gamma's challenge point opens
    // (a clone restarts an open point), and draws gamma there too.
    const bool merged = ops_->relations() > 1;
    static const char kLabel[] = "gordiehowe.field-batch.gamma";
    if (merged)
      t.write(reinterpret_cast<const uint8_t *>(kLabel), sizeof(kLabel) - 1);
    auto sc = t.clone();
    std::unique_ptr<Skip> gamma_skip;
    const Skip *skip = &skip_;
    if (merged) {
      const Elt gamma = skip_.challenge(t);
      if (words != nullptr) (void)skip_.challenge(sc);
      gamma_skip = std::make_unique<Skip>(f, ops_->relation(gamma),
                                          skip_.rows, width_);
      skip = gamma_skip.get();
    }
    typename Skip::Proof proof;
    // The tamper's change to each bit-phase message (prover, tests only).
    std::vector<Elt> phase_delta;
    if (words != nullptr) {
      check(words->size() == this->words(), "batch table words");
      // The phase timers (util/prover_profile.h).
      auto first_scope =
          std::make_unique<profiling::Scope>("batch.first_round");
      auto first = ops_->first_round(*skip, *words, pub, scratch);
      first_scope.reset();
      proof = skip->prove(*first, sc, pads, scratch);
      first.reset();
      if (scratch != nullptr && !scratch->keep) scratch->release_rows();
      messages = flatten(proof);
      if (tamper.messages) {
        const size_t nz = messages.size();
        messages.resize(message_elts(), f.zero());
        tamper.messages(messages);
        phase_delta.assign(messages.begin() + long(nz), messages.end());
        messages.resize(nz);
        unflatten(messages, proof);
      }
    } else {
      check(messages.size() == message_elts(), "batch message size");
      unflatten(messages, proof);
    }
    auto zc_scope = std::make_unique<profiling::Scope>("batch.zerocheck");
    auto ctx = skip->rows_of(proof, t, pad_at);
    zc_scope.reset();
    if (bit_phase_)
      return bit_phase(t, *skip, ctx, messages, pad_at, words, pads,
                       phase_delta, tamper.swap_round, pub);
    auto forms_scope = std::make_unique<profiling::Scope>("batch.forms");
    auto forms = std::make_shared<BitForms<F>>(ops_->forms(*skip, ctx, pub));
    forms_scope.reset();
    const size_t form_row = ctx.b.size();
    skip->opening_row(ctx, forms->constant, pad_at);
    Rows rows;
    rows.a = std::move(ctx.a);
    rows.b = std::move(ctx.b);
    rows.form_row = form_row;
    rows.forms = std::move(forms);
    rows.bit_claim = ops_->bit_operands();
    return rows;
  }

 private:
  // The bit phase after the zerocheck's context CTX (bit_phase.h): its
  // rounds on T, then the opening row on its output claim. The prover
  // (WORDS set) appends its masked messages to MESSAGES, each changed by
  // its DELTA, round SWAP_ROUND's with its pads swapped (tests); the
  // verifier reads them after the zerocheck's.
  Rows bit_phase(Transcript &t, const Skip &skip,
                 typename Skip::Context &ctx, std::vector<Elt> &messages,
                 size_t pad_at, const std::vector<Elt> *words,
                 const Elt *pads, const std::vector<Elt> &delta,
                 int swap_round, const BatchPublics<F> &pub) const {
    const F &f = f_;
    using X = PhaseExpr<F>;
    const size_t pad0 = skip_.layout.count;
    const size_t at0 = skip_.message_elts();
    // The opening claim C = sum_j u_j (m_j - P_j) - constant. The constant
    // comes with the word weights after the rounds; each round scales the
    // claim by L1, so CC is its coefficient in the claim so far.
    X claim{f.zero(), {}};
    for (unsigned j = 0; j < skip.K; ++j)
      claim.add(f, X::scaled(f, X::message(f, ctx.terminal[j],
                                           pad_at + skip.layout.terminal + j),
                             ctx.u[j]));
    Elt cc = f.mone();
    t.write(reinterpret_cast<const uint8_t *>(BitPhaseShape::kLabel),
            sizeof(BitPhaseShape::kLabel) - 1);
    std::unique_ptr<BitPhaseProver<F>> prover;
    if (words != nullptr) {
      profiling::Scope sc("batch.bitphase.tables");
      std::vector<Elt> sigma, g;
      ops_->bit_phase_tables(skip, ctx, *words, sigma, g);
      prover = std::make_unique<BitPhaseProver<F>>(f, std::move(sigma),
                                                   std::move(g));
    }
    auto rounds_scope =
        std::make_unique<profiling::Scope>("batch.bitphase.rounds");
    std::vector<Elt> rho(BitPhaseShape::kRounds);
    for (size_t i = 0; i < BitPhaseShape::kRounds; ++i) {
      std::array<Elt, 2> m;
      if (prover) {
        m = prover->message();
        // Tests only: the round's two pads swapped (Tamper::swap_round).
        const bool swap = swap_round == int(i);
        for (size_t d = 0; d < 2; ++d) {
          f.add(m[d], pads[pad0 + 2 * i + (swap ? 1 - d : d)]);
          if (!delta.empty()) f.add(m[d], delta[2 * i + d]);
          messages.push_back(m[d]);
        }
      } else {
        m = {messages[at0 + 2 * i], messages[at0 + 2 * i + 1]};
      }
      t.write(m.data(), 1, 2, f);
      rho[i] = skip.challenge(t);
      if (prover) prover->bind(rho[i]);
      // p(1) = claim - p(0); claim' = L0 p(0) + L1 p(1) + L2 p(g).
      const auto l = phase_lagrange(f, rho[i]);
      const X p0 = X::message(f, m[0], pad_at + pad0 + 2 * i);
      const X pg = X::message(f, m[1], pad_at + pad0 + 2 * i + 1);
      X next = X::scaled(f, claim, l[1]);
      next.add(f, X::scaled(f, p0, f.subf(l[0], l[1])));
      next.add(f, X::scaled(f, pg, l[2]));
      claim = std::move(next);
      f.mul(cc, l[1]);
    }
    rounds_scope.reset();
    // The word weights alpha at eq(rho, .) and the constant, then the
    // claim's forms on the bit stage.
    auto forms_scope = std::make_unique<profiling::Scope>("batch.forms");
    const size_t kW = size_t(1) << BitPhaseShape::kLogW;
    std::vector<Elt> eq(kW);
    {
      Eqs<F> e(BitPhaseShape::kLogW, kW, rho.data(), f);
      for (size_t b = 0; b < kW; ++b) eq[b] = e.at(b);
    }
    BitForms<F> alpha = ops_->word_weights(skip, ctx, pub, eq);
    forms_scope.reset();
    f.add(claim.known, f.mulf(cc, alpha.constant));
    // The claim in product form (bit_phase.h), which the bit stage opens
    // as it is; the bit_phase_bridge test switch (test_switches.h)
    // materializes its 16 forms instead.
    auto pc_scope = std::make_unique<profiling::Scope>("batch.product_claim");
    auto pc = std::make_shared<ProductClaim<F>>(
        product_claim(f, std::move(alpha.a), eq, ops_->bit_dual()));
    pc_scope.reset();
    std::shared_ptr<const BitForms<F>> forms;
    if (test_switches().bit_phase_bridge) {
      profiling::Scope sc("batch.bitphase.forms");
      forms = std::make_shared<BitForms<F>>(phase_forms(f, *pc));
      pc.reset();
    }
    // The opening row: the claim on the bits equals claim_4, its pads'
    // terms moved left: bits + sum (-c) P = known.
    const size_t form_row = ctx.b.size();
    for (const auto &[at, c] : claim.terms)
      ctx.a.push_back({form_row, at, f.negf(c)});
    ctx.b.push_back(claim.known);
    Rows rows;
    rows.a = std::move(ctx.a);
    rows.b = std::move(ctx.b);
    rows.form_row = form_row;
    rows.forms = std::move(forms);
    rows.product = std::move(pc);
    rows.bit_claim = true;
    return rows;
  }

  // The zerocheck messages in transcript order.
  static std::vector<Elt> flatten(const typename Skip::Proof &p) {
    std::vector<Elt> out(p.skip.begin(), p.skip.end());
    for (const auto &q : p.rounds) out.insert(out.end(), q.begin(), q.end());
    out.insert(out.end(), p.terminal.begin(), p.terminal.end());
    return out;
  }
  void unflatten(const std::vector<Elt> &v, typename Skip::Proof &p) const {
    size_t at = skip_.extra();
    p.skip.assign(v.begin(), v.begin() + long(at));
    p.rounds.assign(skip_.layout.logs, std::vector<Elt>(skip_.D));
    for (auto &q : p.rounds)
      for (auto &x : q) x = v[at++];
    p.terminal.assign(skip_.K, f_.zero());
    for (auto &x : p.terminal) x = v[at++];
  }

  const F &f_;
  std::shared_ptr<const BatchOperands<F>> ops_;
  unsigned width_;
  Skip skip_;  // layout (gamma = 1)
  bool bit_phase_ = false;
};


// Why the relation R at skip WIDTH has no bit-packed realization, or "" if
// it has one. The checks of BasicBooleanSkip, as compile errors: every
// monomial reads an operand (Q has no constant term, since the zerocheck
// pads its rows with zeros), each monomial's operands come first and its
// -1 entries last, indices lie below K, the width is a power of two up to
// 64, and the D (w - 1) + 1 skip points fit the 8-bit skip subfield.
template <class R>
std::string relation_error(unsigned width) {
  constexpr unsigned K = R::kOperands, D = R::kDegree;
  if (K < 1 || D < 1 || R::kMonomials < 1)
    return "the relation has no operand, degree or monomial";
  for (size_t m = 0; m < R::kMonomials; ++m) {
    if (R::kTerms[m][0] < 0)
      return "monomial " + std::to_string(m) +
             " is constant; Q has no constant term";
    bool ended = false;
    for (unsigned t = 0; t < D; ++t) {
      const int x = R::kTerms[m][t];
      if (x < -1 || x >= int(K))
        return "monomial " + std::to_string(m) + " reads operand " +
               std::to_string(x) + " of " + std::to_string(K);
      if (x == -1) ended = true;
      if (x >= 0 && ended)
        return "monomial " + std::to_string(m) +
               " has an operand after a -1 entry";
    }
  }
  bool full = false;
  for (size_t m = 0; m < R::kMonomials; ++m)
    full = full || R::kTerms[m][D - 1] >= 0;
  if (!full)
    return "no monomial has the relation's degree " + std::to_string(D);
  if (width < 1 || width > 64 || (width & (width - 1)) != 0)
    return "skip width " + std::to_string(width) +
           " is not a power of two up to 64";
  if (D * (width - 1) + 1 > 256)
    return "skip width " + std::to_string(width) + " is too large for degree " +
           std::to_string(D) + ": D (w - 1) + 1 = " +
           std::to_string(D * (width - 1) + 1) + " points exceed the 256 of "
           "the skip subfield";
  return "";
}

// ------------------------------------------------- bit-packed operands --

// The operand map of a characteristic-2 bit-packed batched relation: K
// operands of LANES 64-bit lanes (64 / w skip rows each), each bit an affine
// function over GF(2) of the table bits. Table word y holds 16 bits, bit b
// as the coefficient of beta_b (F::of_scalar).
template <class F, class R, size_t W = 16>
class BitOperandMap {
 public:
  using Elt = typename F::Elt;
  using Skip = BasicBooleanSkip<F, R>;
  using Word = typename R::Word;
  static constexpr unsigned K = R::kOperands;
  // Table words of W bits (words of GF(2^W)).
  static constexpr size_t kWordBits = W;
  using HostWord = std::conditional_t<
      (W <= 16), uint16_t, std::conditional_t<(W <= 32), uint32_t, uint64_t>>;
  virtual ~BitOperandMap() = default;
  virtual std::string name() const = 0;
  // Parameters that fix the map, for the system digest.
  virtual std::vector<uint8_t> params() const = 0;
  virtual size_t lanes() const = 0;
  virtual size_t words() const = 0;
  // The lanes of each call when several share the map (in table order);
  // empty for one call (the plan export).
  virtual std::vector<size_t> call_lanes() const { return {}; }
  // Host direction: the operand lanes of the table words.
  virtual std::vector<Word> apply(const std::vector<HostWord> &words) const = 0;
  // The adjoint at the reduction's point (skip point r, row point s) and
  // combination u: sum_j u_j L_j(r, s) = constant + sum_k Frob^k(<a_k, W>).
  virtual BitForms<F> adjoint(const Skip &skip, const Elt &r,
                              const std::vector<Elt> &s,
                              const std::array<Elt, K> &u) const = 0;
};

// A lane-affine operand map: operand j's lane l is a constant XOR the
// rotations of table lanes,
//   L_j(l) = constant ^ XOR_src rotl(T(src.lane), src.rot),
// where table lane m is the 64 bits of words 4m..4m+3 (word 4m + c holds bits
// 16c..16c+15). Keccak's theta, rho, pi and chi operands have this shape;
// keccak.h uses its fused adjoint instead.
template <class F, class R>
class LaneOperandMap final : public BitOperandMap<F, R> {
 public:
  using Elt = typename F::Elt;
  using Base = BitOperandMap<F, R>;
  using Skip = typename Base::Skip;
  using Word = typename Base::Word;
  static constexpr unsigned K = R::kOperands;
  struct Source {
    size_t lane;
    unsigned rot;
  };
  struct Lane {
    uint64_t constant = 0;
    std::vector<Source> src;
  };

  // ops[j][l] for j < K, l < lanes; the tables hold WORDS words (a multiple
  // of 4).
  LaneOperandMap(const F &f, std::string name, size_t words,
                 std::array<std::vector<Lane>, K> ops)
      : f_(f), basis_(f), name_(std::move(name)), words_(words),
        ops_(std::move(ops)) {
    check(words_ % 4 == 0, "lane map: whole lanes");
    for (unsigned j = 0; j < K; ++j) {
      check(ops_[j].size() == ops_[0].size(), "lane map: operand lengths");
      for (const auto &l : ops_[j])
        for (const auto &s : l.src)
          check(s.lane < words_ / 4 && s.rot < 64, "lane map: source");
    }
  }

  std::string name() const override { return name_; }
  std::vector<uint8_t> params() const override {
    std::vector<uint8_t> out;
    put_u64(out, words_);
    put_u64(out, lanes());
    for (const auto &op : ops_)
      for (const auto &l : op) {
        put_u64(out, l.constant);
        put_u64(out, l.src.size());
        for (const auto &s : l.src) {
          put_u64(out, s.lane);
          put_u64(out, s.rot);
        }
      }
    return out;
  }
  size_t lanes() const override { return ops_[0].size(); }
  size_t words() const override { return words_; }

  std::vector<Word> apply(const std::vector<uint16_t> &w) const override {
    check(w.size() == words_, "lane map: table size");
    std::vector<Word> out(lanes());
    for (size_t l = 0; l < lanes(); ++l)
      for (unsigned j = 0; j < K; ++j) {
        uint64_t v = ops_[j][l].constant;
        for (const auto &s : ops_[j][l].src) v ^= rotl(lane(w, s.lane), s.rot);
        out[l][j] = v;
      }
    return out;
  }

  // Row l * (64 / w) + c holds bits c w .. c w + w - 1 of lane l. With
  // low[z] = eq(s_chunk, z / w) L_{z mod w}(r), operand j's claim is
  //   sum_l eq(s_lane, l) sum_z low[z] L_j(l)_z,
  // and table bit 16c + b of lane m gets, from a source (m, rot) of lane l,
  // the weight u_j eq(s_lane, l) low[(16c + b + rot) mod 64]. The form k
  // twists each weight by Frob^-k, a field automorphism that fixes the 0/1
  // structure, and contracts the 16 bits of a word with the dual basis.
  BitForms<F> adjoint(const Skip &skip, const Elt &r, const std::vector<Elt> &s,
                      const std::array<Elt, K> &u) const override {
    const F &f = f_;
    const unsigned w = skip.width();
    size_t nchunk = 64 / w, lgchunk = 0;
    while ((size_t(1) << lgchunk) < nchunk) ++lgchunk;
    check(s.size() >= lgchunk, "operand claim dimensions");
    const size_t lglane = s.size() - lgchunk, nlane = size_t(1) << lglane;
    check(nlane >= lanes(), "operand claim lane dimension");
    Eqs<F> eql(lgchunk, nchunk, s.data(), f);
    auto lb = skip.bit_basis(r);
    std::array<Elt, 64> low;
    for (size_t z = 0; z < 64; ++z) low[z] = f.mulf(eql.at(z / w), lb[z % w]);

    BitForms<F> out{std::vector<Elt>(16 * words_, f.zero()), f.zero(), words_};
    // The constant, untwisted.
    {
      Eqs<F> eq(lglane, nlane, s.data() + lgchunk, f);
      for (unsigned j = 0; j < K; ++j)
        for (size_t l = 0; l < lanes(); ++l) {
          const uint64_t c = ops_[j][l].constant;
          if (c == 0) continue;
          Elt v = f.zero();
          for (size_t z = 0; z < 64; ++z)
            if ((c >> z) & 1) f.add(v, low[z]);
          f.add(out.constant, f.mulf(u[j], f.mulf(eq.at(l), v)));
        }
    }
    std::vector<Elt> tw(lglane * 16), uk(K * 16), lk(64 * 16);
    for (size_t i = 0; i < lglane; ++i)
      inverse_frobenius_powers(s[lgchunk + i], 16, &tw[i * 16], f);
    for (unsigned j = 0; j < K; ++j)
      inverse_frobenius_powers(u[j], 16, &uk[j * 16], f);
    for (size_t z = 0; z < 64; ++z)
      inverse_frobenius_powers(low[z], 16, &lk[z * 16], f);
    for (size_t k = 0; k < 16; ++k) {
      std::vector<Elt> twisted(lglane);
      for (size_t i = 0; i < lglane; ++i) twisted[i] = tw[i * 16 + k];
      Eqs<F> eq(lglane, nlane, twisted.data(), f);
      // d[rot][c] = sum_b low_k[(16c + b + rot) mod 64] dual_b.
      std::vector<std::array<Elt, 4>> d(64);
      for (size_t rot = 0; rot < 64; ++rot)
        for (size_t c = 0; c < 4; ++c) {
          typename F::Accum acc{};
          for (size_t b = 0; b < 16; ++b)
            f.mac(acc, lk[((16 * c + b + rot) % 64) * 16 + k], basis_.dual(b));
          d[rot][c] = f.reduce(acc);
        }
      Elt *a = out.a.data() + k * words_;
      for (unsigned j = 0; j < K; ++j)
        for (size_t l = 0; l < lanes(); ++l) {
          const Elt q = f.mulf(uk[j * 16 + k], eq.at(l));
          for (const auto &src : ops_[j][l].src)
            for (size_t c = 0; c < 4; ++c)
              f.add(a[4 * src.lane + c], f.mulf(q, d[src.rot][c]));
        }
    }
    return out;
  }

 private:
  static uint64_t rotl(uint64_t x, unsigned r) {
    return r == 0 ? x : (x << r) | (x >> (64 - r));
  }
  static uint64_t lane(const std::vector<uint16_t> &w, size_t m) {
    uint64_t v = 0;
    for (size_t c = 0; c < 4; ++c) v |= uint64_t(w[4 * m + c]) << (16 * c);
    return v;
  }
  const F &f_;
  PackedBasis<F> basis_;
  std::string name_;
  size_t words_;
  std::array<std::vector<Lane>, K> ops_;
};


// --------------------------------------------- bit-operand realization --

// The bit-sliced first round: the zerocheck's rows (each operand lane split
// into 64 / w rows of w bits), evaluated by BasicBooleanSkip's kernel. The
// rows from sk.live_rows() on are the zero padding of Skip::rows.
template <class F, class R>
class BitSkipOperands final : public SkipOperands<F> {
 public:
  using Elt = typename F::Elt;
  using Skip = BasicBooleanSkip<F, R>;
  // Owns ROWS, or borrows them (a scratch's, prover_scratch.h).
  BitSkipOperands(const Skip &skip, typename Skip::Rows &&rows)
      : skip_(skip), own_(std::move(rows)), rows_(own_) {}
  BitSkipOperands(const Skip &skip, const typename Skip::Rows &rows)
      : skip_(skip), rows_(rows) {}
  std::vector<Elt> skip_values(const MaskedFieldSkip<F> &sk,
                               const std::vector<Elt> &e) const override {
    check(e.size() == rows_.size(), "bit skip rows");
    check(sk.live_rows() <= rows_.size(), "bit skip live rows");
    return skip_.skip_values(rows_, e, sk.live_rows());
  }
  using Table = typename SkipOperands<F>::Table;
  void bind_into(const MaskedFieldSkip<F> &sk, const Elt &r,
                 std::vector<Table> &out) const override {
    out.resize(Skip::K);
    skip_.bind_into(rows_, r, sk.live_rows(), out.data());
  }

 private:
  const Skip &skip_;
  typename Skip::Rows own_;
  const typename Skip::Rows &rows_;
};

// Characteristic 2, operand bits packed W to a GF(2^W) word of a Subfield
// table, read through MAP; R is the relation (relation_error<R> holds).
// The zerocheck's instances are the bits of the operand lanes, instance
// 64 l + c of lane l's bit c. The terminal operand claims, combined by u,
// are through the Frobenius trace forms of the map's adjoint a claim on the
// table words' bits.
template <class F, class R, size_t W = 16>
class BitOperands final : public BatchOperands<F> {
 public:
  using Elt = typename F::Elt;
  using Map = BitOperandMap<F, R, W>;
  using HostWord = typename Map::HostWord;
  using Skip = MaskedFieldSkip<F>;
  static constexpr unsigned K = R::kOperands, D = R::kDegree;

  BitOperands(const F &f, std::shared_ptr<const Map> map, unsigned width)
      : f_(f), map_(std::move(map)), skip_(f, width),
        bits_(SubfieldInfo<F>::get(f, W)) {
    if constexpr (W == 16 && domain_subfield<F>::kBitWords)
      decode_ = std::make_unique<SubfieldDecoder<F>>(f);
  }

  size_t words() const override { return map_->words(); }
  size_t word_degree() const override { return W; }
  bool bit_operands() const override { return true; }
  size_t instances() const override { return map_->lanes() * 64; }
  // Q's monomials, coefficient 1, their operands sorted.
  FieldRelation<F> relation(const Elt &) const override {
    FieldRelation<F> out;
    out.name = map_->name();
    out.operands = K;
    for (size_t m = 0; m < R::kMonomials; ++m) {
      typename FieldRelation<F>::Monomial mono{f_.one(), {}};
      for (unsigned t = 0; t < D && R::kTerms[m][t] >= 0; ++t)
        mono.ops.push_back(unsigned(R::kTerms[m][t]));
      std::sort(mono.ops.begin(), mono.ops.end());
      out.monomials.push_back(std::move(mono));
    }
    return out;
  }
  void describe(std::vector<uint8_t> &out, unsigned width) const override {
    put_str(out, "bit-packed-skip/bit-node-claim");
    put_u64(out, K);
    put_u64(out, D);
    put_u64(out, R::kMonomials);
    for (size_t m = 0; m < R::kMonomials; ++m)
      for (unsigned t = 0; t < D; ++t)
        put_u64(out, uint64_t(R::kTerms[m][t] + 1));
    put_u64(out, width);
    put_str(out, map_->name());
    const auto p = map_->params();
    put_u64(out, p.size());
    out.insert(out.end(), p.begin(), p.end());
  }
  std::string report(const Skip &sk, size_t pads,
                     size_t message_elts) const override {
    return "bit-packed skip: Q degree " + std::to_string(D) + " in " +
           std::to_string(K) + " operands, map " + map_->name() + ", " +
           std::to_string(map_->lanes()) + " lanes, width " +
           std::to_string(sk.width()) + ", " +
           std::to_string(sk.layout.logs) + " rounds, " +
           std::to_string(pads) + " pads, " + std::to_string(message_elts) +
           " message elements";
  }
  size_t shape_instances() const override { return map_->lanes(); }
  std::vector<std::string> parts() const override { return {map_->name()}; }
  std::vector<size_t> call_instances() const override {
    return map_->call_lanes();
  }

  std::unique_ptr<SkipOperands<F>> first_round(
      const Skip &, const std::vector<Elt> &words, const BatchPublics<F> &,
      BatchScratch<F> *) const override {
    std::vector<HostWord> host(words.size());
    for (size_t i = 0; i < host.size(); ++i)
      host[i] = decode_ ? HostWord((*decode_)(words[i]))
                        : HostWord(bits_.bits(f_, words[i]));
    return std::make_unique<BitSkipOperands<F, R>>(
        skip_, skip_.rows(map_->apply(host)));
  }
  BitForms<F> forms(const Skip &, const typename Skip::Context &ctx,
                    const BatchPublics<F> &) const override {
    std::array<Elt, K> u;
    for (unsigned j = 0; j < K; ++j) u[j] = ctx.u[j];
    return map_->adjoint(skip_, ctx.r, ctx.s, u);
  }

 private:
  const F &f_;
  std::shared_ptr<const Map> map_;
  BasicBooleanSkip<F, R> skip_;
  // Table words to host words: SubfieldDecoder's table for GF(2^16)
  // words, the subfield's coordinates otherwise.
  std::unique_ptr<SubfieldDecoder<F>> decode_;
  const SubfieldInfo<F> &bits_;
};


// ------------------------------------------------ field operand maps --

// The operand map of a field batch.
template <class F>
class FieldOperandMap {
 public:
  using Elt = typename F::Elt;
  virtual ~FieldOperandMap() = default;
  virtual std::string name() const = 0;
  virtual std::vector<uint8_t> params() const = 0;
  virtual size_t operands() const = 0;
  virtual size_t instances() const = 0;
  virtual size_t words() const = 0;
  // Host direction: the operands of every instance.
  virtual std::vector<std::vector<Elt>> apply(
      const F &f, const std::vector<Elt> &words) const = 0;
  // sum_t weight_t sum_j u_j L_j(W, t) = constant + sum_c a_c W_c.
  virtual void adjoint(const F &f, const std::vector<Elt> &weight,
                       const std::vector<Elt> &u, std::vector<Elt> &a,
                       Elt &constant) const = 0;
};

// An affine operand map: L_j(W, t) = constant_{j,t} + sum k W_c over its
// terms.
template <class F>
class AffineOperandMap final : public FieldOperandMap<F> {
 public:
  using Elt = typename F::Elt;
  struct Term {
    size_t word;
    Elt k;
  };
  struct Operand {
    Elt constant;
    std::vector<Term> terms;
  };
  // ops[t][j] for instance t, operand j.
  AffineOperandMap(const F &f, std::string name, size_t words,
                   std::vector<std::vector<Operand>> ops)
      : f_(f), name_(std::move(name)), words_(words), ops_(std::move(ops)) {
    check(!ops_.empty(), "affine operand map: no instance");
    for (const auto &t : ops_) {
      check(t.size() == ops_[0].size(), "affine operand map: operands");
      for (const auto &o : t)
        for (const auto &x : o.terms) check(x.word < words_, "operand word");
    }
  }
  // Operand j of instance t is word t + j * instances (the tables hold the
  // operands' columns).
  static std::shared_ptr<const AffineOperandMap> columns(const F &f,
                                                         std::string name,
                                                         size_t operands,
                                                         size_t instances) {
    std::vector<std::vector<Operand>> ops(instances);
    for (size_t t = 0; t < instances; ++t)
      for (size_t j = 0; j < operands; ++j)
        ops[t].push_back(Operand{f.zero(), {{t + j * instances, f.one()}}});
    return std::make_shared<AffineOperandMap>(f, std::move(name),
                                              operands * instances, ops);
  }
  std::string name() const override { return name_; }
  std::vector<uint8_t> params() const override {
    std::vector<uint8_t> out;
    put_u64(out, words_);
    put_u64(out, ops_.size());
    put_u64(out, ops_[0].size());
    for (const auto &t : ops_)
      for (const auto &o : t) {
        put_elt(out, o.constant);
        put_u64(out, o.terms.size());
        for (const auto &x : o.terms) {
          put_u64(out, x.word);
          put_elt(out, x.k);
        }
      }
    return out;
  }
  size_t operands() const override { return ops_[0].size(); }
  size_t instances() const override { return ops_.size(); }
  size_t words() const override { return words_; }
  std::vector<std::vector<Elt>> apply(
      const F &f, const std::vector<Elt> &w) const override {
    std::vector<std::vector<Elt>> out(ops_.size());
    for (size_t t = 0; t < ops_.size(); ++t)
      for (const auto &o : ops_[t]) {
        Elt v = o.constant;
        for (const auto &x : o.terms) f.add(v, f.mulf(x.k, w.at(x.word)));
        out[t].push_back(v);
      }
    return out;
  }
  void adjoint(const F &f, const std::vector<Elt> &weight,
               const std::vector<Elt> &u, std::vector<Elt> &a,
               Elt &constant) const override {
    a.assign(words_, f.zero());
    constant = f.zero();
    for (size_t t = 0; t < ops_.size(); ++t)
      for (size_t j = 0; j < ops_[t].size(); ++j) {
        const Elt c = f.mulf(weight[t], u[j]);
        f.add(constant, f.mulf(c, ops_[t][j].constant));
        for (const auto &x : ops_[t][j].terms)
          f.add(a[x.word], f.mulf(c, x.k));
      }
  }

 private:
  void put_elt(std::vector<uint8_t> &out, const Elt &x) const {
    uint8_t b[F::kBytes];
    f_.to_bytes_field(b, x);
    out.insert(out.end(), b, b + F::kBytes);
  }
  const F &f_;
  std::string name_;
  size_t words_;
  std::vector<std::vector<Operand>> ops_;
};

// One relation of a field batch and the operand map it reads.
template <class F>
struct FieldBatchPart {
  FieldRelation<F> rel;
  std::shared_ptr<const FieldOperandMap<F>> map;
};

// ---------------------------------------------- field-operand realization --

// One or more relations on field-element operands, words of one subfield
// of degree WORD_DEGREE, with the same instances: one zerocheck of
// sum_i gamma^i Q_i over the concatenated operands (gamma = 1 for one
// relation, drawn from the transcript for several). The opening row's part
// on the table words is one form.
template <class F>
class FieldOperands final : public BatchOperands<F> {
 public:
  using Elt = typename F::Elt;
  using Part = FieldBatchPart<F>;
  using Skip = MaskedFieldSkip<F>;

  FieldOperands(const F &f, std::vector<Part> parts, size_t word_degree)
      : f_(f), parts_(std::move(parts)), word_degree_(word_degree) {
    for (const auto &p : parts_)
      check(p.map->instances() == parts_.at(0).map->instances(),
            "merged field batches have the same instances");
  }

  size_t words() const override {
    size_t n = 0;
    for (const auto &p : parts_) n += p.map->words();
    return n;
  }
  size_t word_degree() const override { return word_degree_; }
  bool bit_operands() const override { return false; }
  size_t instances() const override { return parts_[0].map->instances(); }
  size_t relations() const override { return parts_.size(); }
  FieldRelation<F> relation(const Elt &gamma) const override {
    const F &f = f_;
    FieldRelation<F> out;
    Elt g = f.one();
    unsigned off = 0;
    for (const auto &p : parts_) {
      out.name += (out.name.empty() ? "" : "+") + p.rel.name;
      for (const auto &m : p.rel.monomials) {
        typename FieldRelation<F>::Monomial mm{f.mulf(g, m.coeff), {}};
        for (unsigned j : m.ops) mm.ops.push_back(j + off);
        out.monomials.push_back(std::move(mm));
      }
      off += p.rel.operands;
      f.mul(g, gamma);
    }
    out.operands = off;
    return out;
  }
  void describe(std::vector<uint8_t> &out, unsigned width) const override {
    put_str(out, "field-skip");
    put_u64(out, parts_.size());
    for (const auto &p : parts_) {
      put_str(out, p.rel.name);
      put_u64(out, p.rel.operands);
      put_u64(out, p.rel.monomials.size());
      for (const auto &m : p.rel.monomials) {
        uint8_t b[F::kBytes];
        f_.to_bytes_field(b, m.coeff);
        out.insert(out.end(), b, b + F::kBytes);
        put_u64(out, m.ops.size());
        for (unsigned j : m.ops) put_u64(out, j);
      }
      put_str(out, p.map->name());
      const auto q = p.map->params();
      put_u64(out, q.size());
      out.insert(out.end(), q.begin(), q.end());
    }
    put_u64(out, width);
    put_u64(out, word_degree_);
  }
  std::string report(const Skip &sk, size_t pads,
                     size_t message_elts) const override {
    std::string names;
    for (const auto &p : parts_)
      names += (names.empty() ? "" : " + gamma ") + p.rel.name;
    const std::string pts = std::to_string(sk.dom.points());
    return "field skip: " + names + ", degree " + std::to_string(sk.D) +
           " in " + std::to_string(sk.K) + " operands, " +
           std::to_string(sk.rows) + " instances, width " +
           std::to_string(sk.width()) + ", skip domain " + pts +
           (F::kCharacteristicTwo ? " points of the additive GF(2^8) subspace"
                                  : " consecutive integers") + ", " +
           std::to_string(sk.layout.logs) + " rounds, " +
           std::to_string(pads) + " pads, " + std::to_string(message_elts) +
           " message elements";
  }
  std::vector<std::string> parts() const override {
    std::vector<std::string> out;
    for (const auto &p : parts_) out.push_back(p.rel.name);
    return out;
  }

  // The operands of every part, concatenated, evaluated in F.
  std::unique_ptr<SkipOperands<F>> first_round(
      const Skip &, const std::vector<Elt> &words, const BatchPublics<F> &,
      BatchScratch<F> *) const override {
    std::vector<std::vector<Elt>> ops(instances());
    size_t at = 0;
    for (const auto &p : parts_) {
      const std::vector<Elt> w(words.begin() + long(at),
                               words.begin() + long(at + p.map->words()));
      const auto o = p.map->apply(f_, w);
      for (size_t i = 0; i < ops.size(); ++i)
        ops[i].insert(ops[i].end(), o[i].begin(), o[i].end());
      at += p.map->words();
    }
    return std::make_unique<FieldSkipOperands<F>>(std::move(ops));
  }
  void map_work(unsigned) const override {
    const F &f = f_;
    for (const auto &p : parts_) {
      (void)p.map->apply(f, std::vector<Elt>(p.map->words(), f.zero()));
      std::vector<Elt> a;
      Elt c;
      p.map->adjoint(f, std::vector<Elt>(p.map->instances(), f.one()),
                     std::vector<Elt>(p.map->operands(), f.one()), a, c);
    }
  }
  // sum_t weight_t sum_j u_j L_j(W, t), weight_t = eq(s, r) L_z(r_skip)
  // for t = r w + z, through each part's adjoint.
  BitForms<F> forms(const Skip &sk, const typename Skip::Context &ctx,
                    const BatchPublics<F> &) const override {
    const F &f = f_;
    const auto weight = sk.instance_weights(ctx);
    BitForms<F> out{std::vector<Elt>(words(), f.zero()), f.zero(), words()};
    size_t at = 0, op = 0;
    for (const auto &p : parts_) {
      std::vector<Elt> u(ctx.u.begin() + long(op),
                         ctx.u.begin() + long(op + p.map->operands()));
      std::vector<Elt> a;
      Elt c;
      p.map->adjoint(f, weight, u, a, c);
      for (size_t i = 0; i < a.size(); ++i) out.a[at + i] = a[i];
      f.add(out.constant, c);
      at += p.map->words();
      op += p.map->operands();
    }
    return out;
  }

 private:
  const F &f_;
  std::vector<Part> parts_;
  size_t word_degree_;
};

// Why PARTS at skip WIDTH are no field batch of F, or "".
template <class F>
std::string field_batch_error(const F &f,
                              const std::vector<FieldBatchPart<F>> &parts,
                              unsigned width) {
  for (const auto &p : parts) {
    const auto e = p.rel.error();
    if (!e.empty()) return e;
    if (p.rel.operands != p.map->operands())
      return "the relation reads " + std::to_string(p.rel.operands) +
             " operands, the map gives " + std::to_string(p.map->operands());
  }
  if (width < 1 || (width & (width - 1)) != 0)
    return "skip width " + std::to_string(width) + " is not a power of two";
  unsigned deg = 0;
  for (const auto &p : parts) deg = std::max(deg, p.rel.degree());
  const size_t pts = size_t(deg) * (width - 1) + 1;
  if (F::kCharacteristicTwo && pts > 256)
    return "the skip's D (w - 1) + 1 = " + std::to_string(pts) +
           " points exceed the 256 of the binary skip subfield";
  if (!F::kCharacteristicTwo && !characteristic_above(f, Bound(pts)))
    return "the skip's points exceed the characteristic";
  return "";
}

// The operands of PARTS (field_batch_error holds) on words of degree
// WORD_DEGREE, which a kernel of any protocol hash runs.
template <class F>
std::shared_ptr<const BatchOperands<F>> field_batch_operands(
    const F &f, std::vector<FieldBatchPart<F>> parts, size_t word_degree) {
  return std::make_shared<FieldOperands<F>>(f, std::move(parts), word_degree);
}
// The operands of R on the bits MAP reads (relation_error<R> holds), with
// skip WIDTH.
template <class F, class R, size_t W>
std::shared_ptr<const BatchOperands<F>> bit_batch_operands(
    const F &f, std::shared_ptr<const BitOperandMap<F, R, W>> map,
    unsigned width) {
  return std::make_shared<BitOperands<F, R, W>>(f, std::move(map), width);
}

// The batch of PARTS (field_batch_error holds) on words of degree
// WORD_DEGREE, with skip WIDTH.
template <class Hash, class F>
std::shared_ptr<BatchKernel<F, Hash>> make_field_batch(
    const F &f, std::vector<FieldBatchPart<F>> parts, unsigned width,
    size_t word_degree) {
  return std::make_shared<BatchKernel<F, Hash>>(
      f,
      std::make_shared<FieldOperands<F>>(f, std::move(parts), word_degree),
      width);
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_BATCH_H_
