// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: one field domain.
//
// A domain is the unit of commitment: one field, its values and its
// predicates. Domain<F> is typed by its field alone; DomainImpl<F, RSF, S>
// is the system's implementation of it, with the profile's Reed-Solomon
// factory and Ligero parameters, which the domain's compiler
// (compiler/compiled_domain.h) turns into one Circuit<Field> proved by the
// existing ZkProver. CompilePlan, DomainPlan and the compiled domain's,
// prover's and verifier's interfaces are what the system's runtime reads.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_DOMAIN_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_DOMAIN_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "arrays/dense.h"
#include "circuits/compiler/compiler.h"
#include "circuits/logic/compiler_backend.h"
#include "circuits/logic/logic.h"
#include "gordiehowe/bit_eval.h"
#include "gordiehowe/compiler/batch.h"
#include "gordiehowe/compiler/compile_options.h"
#include "gordiehowe/compiler/ligero_choice.h"
#include "gordiehowe/compiler/placement.h"
#include "gordiehowe/compiler/placement_rates.h"
#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/core.h"
#include "gordiehowe/expr.h"
#include "gordiehowe/linear.h"
#include "gordiehowe/system_core.h"
#include "gordiehowe/word_pack.h"
#include "sumcheck/circuit.h"
#include "sumcheck/circuit_id.h"
#include "util/optimization_options.h"
#include "util/parallel.h"
#include "zk/zk_common.h"
#include "zk/zk_proof.h"
#include "zk/zk_prover.h"
#include "zk/zk_verifier.h"

namespace proofs::gordiehowe {

// What compile() hands each domain: the graph after pad allocation, the
// inferred phases, and each late variable's pad.
struct CompilePlan {
  const std::vector<Node> *nodes = nullptr;
  // The compile's options (compile_options.h).
  CompileOptions options;
  std::vector<size_t> phase;
  std::vector<long> pad_of;  // late advice -> its pad; -1 otherwise
  // Each bounded challenge's charge with its phase and field: the phases'
  // terms the fallback reads (compiled_domain.h's choose_tableau). EXACT is
  // PlanRecords::Charge's exact numerator, else its degree: EXACT over the
  // field's order never exceeds the Lean's error of the challenge.
  struct PhaseCharge {
    std::string label;
    size_t phase = 0, field = 0;
    const void *fobj = nullptr;
    Bound exact = 0;
  };
  std::vector<PhaseCharge> charges;
  // Phase-0 advice whose storage is an affine view of later cells
  // (Lowering::bind_view): no cell of its own.
  std::set<size_t> bound;
  // Bit views whose values no party reads: no generator depends on them and
  // no circuit or affine row reads their bits (a batch reads the words they
  // view). The prover does not compute them.
  std::set<size_t> unread;
  // UNREAD as a flag per node (mark_unread), for the prover's loop.
  std::vector<uint8_t> unread_flag;
  void mark_unread(size_t id) {
    unread.insert(id);
    if (id >= unread_flag.size()) unread_flag.resize(id + 1, 0);
    unread_flag[id] = 1;
  }
  bool is_unread(size_t id) const {
    return id < unread_flag.size() && unread_flag[id] != 0;
  }
  bool late(size_t id) const {
    return (*nodes)[id].kind == Kind::kAdvice && phase[id] >= 1;
  }
  // A committed phase-0 cell: a private input, unbound phase-0 advice, a
  // pad, or a pad copy.
  bool cell(size_t id) const {
    const Kind k = (*nodes)[id].kind;
    return k == Kind::kPad || k == Kind::kPadCopy ||
           ((k == Kind::kAdvice || k == Kind::kPrivateInput) &&
            phase[id] == 0 && !bound.count(id));
  }
};

namespace compiler {
template <class S>
class ConstraintSystemBuilder;
// The range lowering of one domain (compiler/range.h).
template <class F, class S>
void lower_ranges(Domain<F> &d, compiler::ConstraintSystemBuilder<S> &b);
// A domain's compiler (compiler/compiled_domain.h).
template <class F, class RSF, class S>
class CompiledDomain;
// The row reductions' test seams (compiler/tree_zk.h).
struct TreeTestHooks;
class Lowering;
}  // namespace compiler

namespace internal {
class TaskPool;  // threads.h
}  // namespace internal

// S is the system's field set (FieldSet); S::Hash is the protocol hash of
// every domain of the system (DomainProfile).
template <class S>
class DomainProverBase {
 public:
  using Transcript = BasicTranscript<typename S::Hash>;
  virtual ~DomainProverBase() = default;
  // The commitment in two parts: COMMIT_COMPUTE fills, encodes and hashes
  // the witness (RNG also draws the batched relations' reduction pads) and
  // touches no transcript, so the domains' computations may run
  // concurrently; COMMIT_WRITE then absorbs the commitment into T.
  virtual void commit_compute(const ValueStore<S> &v, RandomEngine &rng) = 0;
  virtual void commit_write(Transcript &t) = 0;
  void commit(const ValueStore<S> &v, Transcript &t, RandomEngine &rng) {
    commit_compute(v, rng);
    commit_write(t);
  }
  // The low-degree round of list-radius Ligero (DomainProfile::list_radius),
  // after every domain's commitment; nothing otherwise.
  virtual void ldt(Transcript &t) = 0;
  // BATCH_TAMPER (tests only) changes batch B's zerocheck messages before
  // they are absorbed; MESSAGES holds the domain field's alternative.
  // BATCH_WORDS (tests only) changes the table words batch B's reduction
  // reads, and not the committed words. SWAP_ROUND >= 0 (tests only) masks
  // every bit phase's round SWAP_ROUND with its pads swapped
  // (BatchKernel::Tamper).
  using BatchTamper =
      std::function<void(size_t b, typename S::Value &messages)>;
  // The reductions run on the branches of the nested fork
  // (transcript_fork.h), on POOL when given.
  virtual bool prove(const ValueStore<S> &v, Transcript &t,
                     bool require_satisfied, const BatchTamper &batch_tamper,
                     const BatchTamper &batch_words, int swap_round,
                     internal::TaskPool *pool = nullptr) = 0;
  virtual void write(std::vector<uint8_t> &out) const = 0;
};

template <class S>
class DomainVerifierBase {
 public:
  using Transcript = BasicTranscript<typename S::Hash>;
  virtual ~DomainVerifierBase() = default;
  virtual bool read(ReadBuffer &rb) = 0;
  virtual void recv(Transcript &t) = 0;
  // As DomainProverBase::ldt.
  virtual void ldt(Transcript &t) = 0;
  virtual bool verify(const ValueStore<S> &v, Transcript &t,
                      internal::TaskPool *pool = nullptr) = 0;
};

// The realized program a domain is built from (compiler/realized_program.h)
// and the domain's index in it.
struct DomainSource {
  const ir::Program *program = nullptr;
  size_t domain = 0;
  // On a fresh compile, the domain's compiler that built the program (a
  // CompiledDomainBase of the system's field set): its batch kernels, built
  // from the same decisions and layout, are taken in place of building them
  // again when they match. A hit has none.
  const void *donor = nullptr;
};

// A compiled domain as plain data, for the plan export (plan_export.h).
struct DomainPlan {
  // The Ligero tableau as LigeroParam laid it out: the rate, block_enc,
  // the code length N = block_ext and dimension k = block, the opened
  // columns t (nreq), the blinding width r, the rows, and the mode.
  size_t rate = 0, block_enc = 0, N = 0, k = 0, t = 0, r = 0, nrow = 0;
  bool list_radius = false, split = false;
  // The low-degree test's repetitions (LigeroMode::ldt_reps).
  size_t ldt_reps = 1;
  // Under a Ligero target (DomainProfile::target): the bits s of the target
  // the tableau was planned at (the profile's, or, TARGET_FALLBACK, when
  // one of the domain's own rounds besides Ligero's exceeds it, the largest
  // of them, TARGET_NUM/|K|, 0 otherwise), the agreement threshold A, the
  // line certificate's exceptional count, and the -log2 of the commit, test
  // and column rounds (ligero_choice.h); 0 under explicit parameters.
  double target = 0;
  bool target_fallback = false;
  uint64_t target_num = 0;
  size_t agreement = 0;
  uint64_t exceptions = 0;
  double commit_bits = 0, test_bits = 0, column_bits = 0;
  // The committed witness length and the quadratic constraints the tableau
  // was laid out for (LigeroParam::nw, ::nq).
  size_t nw = 0, nq = 0;
  // The domain's field: its characteristic and degree from kProtocolFieldId
  // (0 for a field without one) and its serialized element size.
  uint64_t characteristic = 0, protocol_degree = 0;
  size_t field_bytes = 0;
  // The packing tree: K's degree over the prime field, the degree of S0
  // (the prefix-row test's subfield), and the non-root nodes bottom-up,
  // each with its edge to its parent: its mode, the revealed measurements,
  // the mask cells (a squaring-chain-masks stage's d masks; a
  // subfield-masks stage's prefix coordinates) and the chain cells; and
  // the rows reaching its stage (TreePlan::routed: 0 at the root's
  // children, whose stages the root runs), which open a stream point when
  // two or more.
  struct TreeNode {
    size_t degree = 0, parent_degree = 0;
    bool declared = false, squaring_chain = false;
    size_t revealed = 0, masks = 0, chain_cells = 0, routed = 0;
  };
  size_t field_degree = 0, s0 = 0;
  std::vector<TreeNode> tree;
  // The circuit and its id, the affine rows by constraint name, and the
  // quadratic triples.
  size_t ninputs = 0, npub = 0, layers = 0, wires = 0, quad_terms = 0;
  std::vector<uint8_t> circuit_id;
  // Whether the domain runs GKR: false when it has no circuit constraint
  // (its circuit then has no layers and describes the inputs only).
  bool gkr = true;
  std::vector<std::pair<std::string, size_t>> affine_rows;
  size_t quad_triples = 0;
  // The circuit inputs of each node, in input order: a public value, a
  // late value's message, a committed cell (a pad's included) or a bit
  // view a circuit reads.
  struct Input {
    enum Storage { kPublic, kMessage, kCell, kView };
    size_t id = 0, at = 0, n = 0;
    Storage storage = kCell;
  };
  std::vector<Input> inputs;
  // The batched relations: name, shape and pads, and the packing-tree
  // node of their table words (its degree).
  struct Batch {
    std::string name;
    size_t table_degree = 0, pads = 0;
    bool bit_operands = false;
    size_t arity = 0, degree = 0, instances = 0, width = 0, rounds = 0;
    // The bit phase's rounds after the zerocheck (compiler/bit_phase.h;
    // DomainProfile::bit_phase), 0 without it. Its pads are the last
    // 2 bit_phase of PADS, full-field and without products. Exported as the
    // program's bitSumcheck (plan_program.h).
    size_t bit_phase = 0;
    std::vector<std::string> parts;
    // The first of its pad inputs (PADS of them).
    size_t pad_input = 0;
    // Several calls sharing the relation: each call's table node and
    // instances.
    std::vector<std::pair<size_t, size_t>> calls;
    // The placement rule's count of its work in one proof (op_counts.h;
    // zero for a declared batch). Not exported.
    compiler::OpCounts work;
  };
  std::vector<Batch> batches;
  // The Fiat-Shamir points whose stream the domain's proof extends
  // (BasicTranscript::extend_point_budget_for), in transcript order: each
  // packing stage (stage:<node>), the root combination (root) and Ligero's
  // linear test (ligero.alphal), with the row slots n it is extended by and
  // its stream length N = k + kFSStreamExtraBytes + 4 n kBytes
  // (TreePlan::stream_rows).
  struct StreamPoint {
    std::string name;
    size_t rows = 0, bytes = 0;
  };
  std::vector<StreamPoint> stream_points;
  // A domain without relative packing: the Boolean checks of its Bit
  // cells, per node in node order, as quadratic triples b * b = b or as
  // circuit constraints b b - b = 0, whichever the placement rule chose
  // (placement.h). A relatively packed domain lists none: its checks are
  // circuit constraints or the batch <domain>.boolean.
  struct BitCheck {
    size_t id = 0, cells = 0;
    bool in_circuit = false;
  };
  std::vector<BitCheck> bit_checks;
  // Each predicate's placement target (assert_zero, assert_true, and
  // assert_equal within a field), in declaration order: predicates the
  // placement rule merged into one group appear once, under their first
  // predicate's name, with their count and instances; BATCH names the
  // batch of a predicate placed in one. The proved side of the boundary
  // the formalization draws: affine rows, triples and the circuit are
  // GKR and Ligero's, a batch is the masked skip's.
  struct Placed {
    std::string name;
    size_t predicates = 1, instances = 0;
    Placement where = Placement::kCircuit;
    std::string batch;
    // A batched predicate's operands per instance, the count the placement
    // rule's batch cost reads (not exported).
    size_t operands = 0;
  };
  std::vector<Placed> placements;
  // Each predicate's own target, in declaration order (the plan export's
  // program): where it is placed, its batch's name when batched, and for
  // a quadratic triple its operands a b = c.
  struct PredTarget {
    Placement where = Placement::kCircuit;
    std::string batch;
    size_t a = 0, b = 0, c = 0;
  };
  std::vector<PredTarget> pred_targets;
  // The Boolean checks x x = x the domain proves, per value: its Bit cells,
  // its late Bit values and its checked derived Bit values, with the
  // target each check is placed on (kBatch: the batch <domain>.boolean).
  struct TypeCheck {
    size_t id = 0;
    Placement where = Placement::kCircuit;
  };
  std::vector<TypeCheck> type_checks;
  // The circuit's constraints in emission order (the plan export's GKR
  // circuit record): a Boolean check of a value (ID), the zero checks of
  // the alignment inputs, a predicate (ID, its index), or a lowering's own
  // circuit (NAME).
  struct CircuitEntry {
    enum Kind { kTypeCheck, kAlignment, kPredicate, kRealization };
    Kind kind = kPredicate;
    size_t id = 0;
    std::string name;
  };
  std::vector<CircuitEntry> circuit_entries;
  // The alignment inputs (each asserted zero or packed as zero bits), in
  // input order.
  std::vector<size_t> filler;
};

template <class S>
class CompiledDomainBase {
 public:
  virtual ~CompiledDomainBase() = default;
  virtual const uint8_t *circuit_id() const = 0;
  virtual DomainPlan plan() const = 0;
  // Serialized bytes of each batched relation's messages, in proof order.
  virtual std::vector<size_t> batch_message_bytes() const = 0;
  // The bit views whose bits the domain's prover reads (circuit inputs).
  virtual std::vector<size_t> views_read() const = 0;
  virtual void describe(std::vector<uint8_t> &out) const = 0;
  virtual std::string report() const = 0;
  virtual std::unique_ptr<DomainProverBase<S>> prover() const = 0;
  virtual std::unique_ptr<DomainVerifierBase<S>> verifier() const = 0;
  // The branches of the nested fork: one per batch, and one for GKR.
  virtual size_t branches() const = 0;
  // The test seams of the domain's row reductions (compiler/tree_zk.h's
  // TreeTestHooks), which a test sets between proofs.
  virtual compiler::TreeTestHooks &tree_test_hooks() const = 0;
  // The branch with the largest estimated cost, which the domain's prover
  // and verifier run on the calling thread (compiler/compiled_domain.h).
  virtual size_t heaviest_branch() const = 0;
  // The size of the domain's Ligero tableau (rows times encoded columns),
  // which orders the commitments' placement (system.h).
  virtual size_t tableau_size() const = 0;
  // The prover's check before proving: the name of the first range request
  // whose value in V leaves the bound its realization establishes, or ""
  // when every request holds.
  virtual std::string unmet_range(const ValueStore<S> &v) const = 0;
  // What the realized program holds for the domain beyond its elements
  // (ir::DomainRealization: its choices' reasons and costs, packing chains
  // and Ligero parameters, and its scheduled circuit): none when its
  // circuit does not fit the record.
  virtual std::optional<ir::DomainRealization> realization() const = 0;
  // Whether the domain was built from a realized program (DomainSource).
  virtual bool loaded() const = 0;
  // Why the realized program given to the domain did not build it ("" when
  // it did, or none was given).
  virtual std::string misfit() const = 0;
};

// The face of a domain that the system's compiler sees, typed by the
// system's field set S: its compiler and its range lowering. The rest is
// DomainCore (system_core.h).
template <class S>
class DomainBase : public virtual DomainCore {
 public:
  // The domain compiled under PLAN. With SOURCE, the domain built from the
  // realized program (DomainSource): its predicates' placements, its
  // batches and Boolean checks from the program's elements, the rest of its
  // decisions and its scheduled circuit from the program's realization of
  // the domain, in place of the placement rule, the counting kernels, the
  // chain choice, the tableau search, emission and scheduling. Without it,
  // the domain's compiler: it decides and emits, and the realized program
  // is built from it (compiler/program_builder.h).
  virtual std::unique_ptr<CompiledDomainBase<S>> compile(
      const CompilePlan &plan, const DomainSource *source) const = 0;
  // The domain's part of the compile cache's key: its field, profile and
  // declarations. Returns "" or why the domain cannot be cached.
  virtual std::string describe_key(std::vector<uint8_t> &out) const = 0;
  // Runs the range lowering over this domain's requests.
  virtual void lower_ranges(compiler::ConstraintSystemBuilder<S> &b) = 0;
};

// The profile of a domain: its field, Reed-Solomon factory and Ligero
// parameters, where its subfields live, and the protocol hash (commitments,
// circuit ids, the Fiat-Shamir transcript): SHA-256 at the ROM parameters,
// SHA-384 at the QROM parameters. Every domain of a system has the same
// hash. A domain supports one source subfield: the field's own subfield
// (Field::kSubFieldBits), committed in Ligero's subfield rows.
template <class F, class RSF, class Hash>
struct DomainProfile {
  const F *f = nullptr;
  const RSF *rsf = nullptr;
  std::string field_name;
  size_t rate = 4, nreq = 128;
  // Ligero at list-decoding radius (LigeroMode): the low-degree round right
  // after the commitments, T opened columns and blinding width r = T in
  // place of NREQ, and the masking of the responses (untested, or split
  // masks, which need 2T <= k).  Off: the original protocol at NREQ.
  bool list_radius = false;
  size_t t = 0;
  LigeroMasking masking = LigeroMasking::kUntested;
  // The opened columns and the Ligero options of the profile; MASKING
  // applies with LIST_RADIUS only.
  size_t opened() const { return list_radius ? t : nreq; }
  LigeroMode ligero_mode() const {
    return LigeroMode{list_radius,
                      list_radius ? masking : LigeroMasking::kUntested};
  }
  // block_enc from (circuit, committed size, quadratic count); null
  // selects 0, the power-of-two search inside LigeroParam.
  std::function<size_t(const Circuit<F> &, size_t, size_t)> block_enc;
  // The per-round target of the domain's Ligero (compiler/ligero_choice.h).
  // Set, the compiler chooses list-radius Ligero for the tableau it builds:
  // block_enc over BLOCK_GRID (at most MAX_BLOCK_ENC when nonzero) at RATE,
  // and for each candidate the opened columns, the masking and the
  // agreement threshold that meet the target; NREQ, LIST_RADIUS, T,
  // MASKING and BLOCK_ENC are then unread. Unset, those explicit
  // parameters.
  std::optional<compiler::LigeroTarget> target;
  // TARGET in half bits (compiler::target_half), 0 when unset.
  size_t target_half() const {
    return target ? compiler::target_half(*target) : 0;
  }
  compiler::BlockGrid block_grid = compiler::BlockGrid::kGeometric8;
  size_t max_block_enc = 0;
  // Under a target: the only block_enc the size search considers (0: the
  // block grid's). A system whose tableau is fixed elsewhere (the SHA-256
  // comparison's table) still takes t, the masking and the repetitions from
  // the planner.
  size_t block_enc_fixed = 0;
  // Execution policy of the domain's GKR kernel (same proofs either way).
  OptimizationOptions optimizations = OptimizationOptions::optimized();
  bool has_subfield = true;
  // Where the prime field lives. kPrime: GF(2), in characteristic 2 (the
  // default there). kSubfield: the subfield is the prime field (Goldilocks
  // in its quartic extension; the default in odd characteristic). kField:
  // the field is prime. compile() checks the choice against F.
  Space prime = F::kCharacteristicTwo ? Space::kPrime : Space::kSubfield;
  // The packing tree's largest edge degree (tree.h) in its default chains:
  // longer edges get intermediate fields; with measured RATES, the
  // compiler weighs other chains by their stage rates (compiled_domain.h's
  // choose_chains).
  size_t d_max = 16;
  // The measured cost rates of the field's domains (placement.h), which
  // place the Boolean checks of Bit cells and every predicate the compiler
  // is free to place. Unset (unmeasured): unit rates
  // (PlacementRates::unit).
  compiler::PlacementRates rates;
  // Test-only ablation:
  // commit the designated subfield's values (GF(2^16) words, bit-packed or not)
  // one per cell in Ligero's subfield rows, as Longfellow does, in place of
  // packing them [K : S0] to an ambient cell under the root stage S0 < K. Bits
  // still pack sixteen to a word. Membership in S0 comes from the subfield
  // rows' prefix test (PrefixSubfieldTest), which then covers those rows too.
  bool unpacked_s0 = false;
  // Test-only ablation: every batch the placement rule places runs its
  // zerocheck at skip width 1, so its first round is no univariate skip but one
  // more multilinear round per skipped variable. The placement, the operands,
  // the masking and the terminal opening are unchanged. A declared batch
  // (Domain::batch), whose operands fix their width at declaration, is a
  // compile error under it.
  bool no_skip = false;
  // The bit-index sumcheck (the Lean's Batch.bitSumcheck): every bit batch the
  // placement rule places on 16-bit table words reduces its opening claim by a
  // masked sumcheck over the words' bit-index variables (compiler/bit_phase.h)
  // before the bit node's stage opens it. The program records it
  // (DomainPlan::Batch::bit_phase, bitSumcheck). Declared batches
  // (Domain::batch) and bit batches on other word sizes keep the opening row of
  // the operand map's Frobenius forms. On by default; false is the ablation
  // that opens every bit batch at that opening row.
  bool bit_phase = true;
  // Test-only ablation: no
  // bit packing. In characteristic 2 a Bit cell is one coordinate of the
  // designated subfield S0 (GF(2^16)), relatively packed with S0's other
  // values, instead of one of sixteen bits of a GF(2^16) word under the bit
  // stage GF(2) < GF(2^16); no Bit value is stored as words and no bit view
  // exists. A Bit cell's Boolean check (b * b = b) is placed as in odd
  // characteristic (a circuit constraint or a field batch), and batches read
  // the cells as GF(2^16) values (the field-batch evaluator, not the bit-sliced
  // one). Relative packing, ring switching, the prefix rows and the subfield
  // test are unchanged. No effect in odd characteristic, whose bits are not bit
  // packed.
  bool no_bit_packing = false;
};
// A range request (Domain::assert_range): every coordinate of V lies below the
// selected bound N, n <= N <= m (m = n for an exact request).
template <class F>
struct RangeRequest {
  Lin<F> v;
  Bound n = 0, m = 0;
  bool interval = false;
  std::string name;
  // Established by interval propagation only (assert_range_implied): never
  // looked up.
  bool implied_only = false;
  // A Slack request: its maximum m is the compiler's, unset (pending)
  // until the integer equality that reads V derives it (mod.h); a pending
  // request bounds nothing in interval propagation.
  bool slack = false;
  bool pending() const { return slack && !interval; }
  bool lowered = false;
  RangeRealization realization;
  // The table cap of this request (RangeHandle::max_table), 0 when unset.
  std::shared_ptr<Bound> max_table = std::make_shared<Bound>(0);
};
// One lookup table [0, T) of a domain after the range lowering: its needle
// coordinates by phase and the size of its dynamic histogram.
struct RangeTableStats {
  Bound table = 0;
  size_t static_needles = 0, dynamic_needles = 0;
  Bound s_dyn = 0;
  size_t alpha = SIZE_MAX, m0 = SIZE_MAX, m1 = SIZE_MAX;
  // The range group of the table (0 unless the table is split).
  size_t group = 0;
  // The group's label, its needle capacity, and whether one late
  // histogram of T counts every needle.
  std::string name;
  size_t capacity = 0;
  bool merged = false;
  // The plan export's records: the group's LogUp circuit, and its needles
  // in the order the sum reads them, each a coordinate range [b, e) of the
  // needle node NODE of range request REQ (an index into the domain's
  // requests).
  std::string circuit;
  struct Member {
    size_t req = 0, node = 0, b = 0, e = 0;
  };
  std::vector<Member> members;
};

// A member of a Statement or Witness struct (relation.h).
template <class M>
class In;

// The generator of a node of field F, as a domain declares it: closures
// over the run's values (ValueReader) and the field's elements, which the
// system wraps for its field set.
template <class F>
struct NodeGen {
  using Elts = std::vector<typename F::Elt>;
  std::function<Elts(const ValueReader &)> eval;
  // A challenge's sampler: its stream, and the values of earlier phases.
  std::function<Elts(RandomEngine &, const ValueReader &)> sample;
  std::function<long(const Elts &)> accepts;
  std::function<long(const std::vector<uint8_t> &)> accepts_bytes;
};

// A domain over the field F: its values and predicates, typed by F alone.
// The profile's Reed-Solomon factory and Ligero parameters, and the
// system's field set, belong to the system's implementation of it
// (DomainImpl), so a library function that declares values or predicates
// takes a Domain<F>& and is templated on F only. Lowerings work on a
// Domain<F>, which they reach from a handle's field type alone.
// A host function for D.priv(nm, e, step) (predicates.h): E's value
// computed as FN of the value of BASE, an expression E is a function of,
// both as packed bits (bit i % 64 of word i / 64). FN reads BASE's words
// and writes E's (zeroed); it must compute E's value with no branch on the
// bits (keccak_f's rounds on lanes, keccak.h). The relation is E's: the
// value's node, its predicate and the plan are priv(nm, e)'s.
// A Bit value's bits as a priv closure may return them, 64 to a word: bit
// i of the value is bit i % 64 of word i / 64, the bits past the value's
// zero. A value stored as words (Domain::word_stored) packs its words from
// them directly.
struct PackedBits {
  std::vector<uint64_t> w;
};

template <class F>
struct HostStep {
  ExprPtr<F> base;
  std::function<void(const uint64_t *in, uint64_t *out)> fn;
};

template <class F>
class Domain : public virtual DomainCore {
 public:
  using Elt = typename F::Elt;
  using Backend = CompilerBackend<F>;
  using CLogic = Logic<F, Backend>;
  using Wires = std::vector<size_t>;
  // The type of a bit-packed word (bit views, batch tables): the domain's
  // source subfield, GF(2^16) where bits are packed. This and type_of's
  // Subfield are where the one-subfield-per-domain assumption lives on the
  // API side.
  using PackedWord = Subfield<>;
  static_assert(is_subfield_v<PackedWord>, "a packed word is a Subfield value");

  // A predicate (assert_zero, assert_true) has an entry in both lists, at
  // its declaration's place (PRED, its index); compile keeps the entry of
  // its placement.
  struct CircuitDecl {
    std::string name;
    std::vector<size_t> reads;
    std::function<void(const CLogic &, const std::vector<Wires> &)> emit;
    long pred = -1;
    // A closure's description for the compile cache's key: what the
    // closure's circuit depends on beyond the compiler's code and its
    // reads (compiler/compile_cache.h). A closure without one makes the
    // system uncacheable.
    std::optional<std::vector<uint8_t>> key = std::nullopt;
  };
  struct AffineDecl {
    std::string name;
    Lin<F> e;
    long pred = -1;
  };
  struct PredDecl {
    std::string name;
    ExprPtr<F> e;
    bool truth = false;  // assert_true: e = 1
    std::shared_ptr<Placement> pin;
  };
  struct QuadDecl {
    size_t a, b, c;
  };
  // A batched relation: its operands and skip width, which the domain's
  // compiler makes a kernel of (BatchKernel, under the protocol hash).
  struct BatchDecl {
    std::string name;
    std::vector<size_t> tables;
    std::shared_ptr<const compiler::BatchOperands<F>> ops;  // null: none
    unsigned width = 0;
    std::string missing;  // why there is no realization (compile error)
  };

  // The domain NM of index IDX of system SYS over the nodes G, its field F
  // of index FIELD_ID in the system's field set.
  Domain(Graph *g, SystemCore *sys, const F *f, std::string nm, int idx,
         size_t field_index, bool sub, Space pr)
      : g_(g), sys_(sys), f_(f) {
    index = idx;
    name = std::move(nm);
    field_id = field_index;
    fobj = f;
    ftag = field_tag<F>();
    has_subfield = sub;
    prime = pr;
  }

  const F &field() const { return *f_; }
  // The measured cost rates of the domain's profile (placement.h); none
  // (unmeasured) for a domain without a profile.
  virtual const compiler::PlacementRates &rates() const {
    static const compiler::PlacementRates kNone;
    return kNone;
  }

  // The domain's lookup-table cap (RangePolicy::max_table): its range
  // requests and public tables may use tables of up to T rows. 0 (the
  // default) keeps the policy's.
  Domain &max_table(Bound T) {
    max_table_ = T;
    return *this;
  }
  Bound max_table() const { return max_table_; }

  // A slot of a record generator (System::advice_record): a value of this
  // domain, of type T and shape SHAPE, that the record's closure fills; NAT
  // slots receive canonical integers.
  template <class T, bool kNatSlot>
  struct Slot {
    Domain *d;
    std::string name;
    Shape shape;
    using field_type = F;
    using type_tag = T;
    static constexpr bool kNat = kNatSlot;
    // What the record's closure fills for this slot.
    using Out = std::conditional_t<kNatSlot, std::vector<NatInt>,
                                   std::vector<Elt>>;
    using Handle = Ref<F, T, Committed>;
  };
  template <class T>
  Slot<T, false> slot(T, std::string nm, Shape shape) {
    static_assert(is_value_type_v<T>,
                  "slot: the type is Bit, Subfield or Field");
    return Slot<T, false>{this, std::move(nm), std::move(shape)};
  }
  template <class T>
  Slot<T, true> nat_slot(T, std::string nm, Shape shape) {
    static_assert(is_value_type_v<T>,
                  "nat_slot: the type is Bit, Subfield or Field");
    static_assert(!F::kCharacteristicTwo,
                  "nat_slot: canonical integers exist in odd characteristic "
                  "only");
    return Slot<T, true>{this, std::move(nm), std::move(shape)};
  }
  // Declares slot S of a record whose closure runs once per proof (EVAL
  // returns this slot's value from the record's outputs).
  template <class T, bool kNatSlot>
  Ref<F, T, Committed> add_record_slot(
      const Slot<T, kNatSlot> &s, std::vector<size_t> deps,
      std::function<std::vector<Elt>(const ValueReader &)> eval) {
    if constexpr (is_bit_v<T> && F::kCharacteristicTwo) {
      if (word_stored(s.shape.size(), deps, MaskedBy{}))
        return word_bits(s.name, s.shape, std::move(deps), std::move(eval));
    }
    Node nd = base(Kind::kAdvice, s.name, type_in<F, T>(), s.shape);
    nd.deps = std::move(deps);
    NodeGen<F> gen;
    gen.eval = std::move(eval);
    return ref<T, Committed>(add_node(std::move(nd), std::move(gen)), s.shape);
  }

  // The canonical integers of X, or a run-time error naming LABEL and
  // dependency K, raised after the whole conversion (ct.h: no branch on a
  // coordinate, and the error does not name one).
  template <class G>
  static std::vector<NatInt> integers(const G &g,
                                   const std::vector<typename G::Elt> &x,
                                   const std::string &label, size_t k) {
    std::vector<NatInt> out(x.size());
    uint64_t ok = 1;
    for (size_t i = 0; i < x.size(); ++i) out[i] = nat_of_ct(g, x[i], ok);
    if (!ok)
      throw std::runtime_error("advice '" + label + "': dependency " +
                               std::to_string(k) +
                               " has a coordinate outside the prime field");
    return out;
  }
  // The element of F of each integer of OUT, each below p; the check runs
  // once, after the conversion. A p beyond 128 bits (F_p256) exceeds every
  // NatInt, so only a narrower p is compared (a public choice).
  template <class I>
  static std::vector<Elt> elements(const F &f, const Bound &p,
                                   const std::vector<I> &out,
                                   const std::string &label) {
    std::vector<Elt> y(out.size());
    uint64_t ok = 1;
    const bool wide = !p.fits128();
    const NatInt pn = wide ? NatInt(0) : static_cast<NatInt>(p);
    for (size_t i = 0; i < out.size(); ++i) {
      const uint64_t below = wide ? 1 : ct::lt128(NatInt(out[i]), pn);
      ok &= below;
      // An integer at or above p converts as 0 (of_scalar may refuse it).
      y[i] = elt_of_nat(f, NatInt(out[i]) & ct::mask128(below));
    }
    if (!ok)
      throw std::runtime_error("advice '" + label +
                               "': an output is not below p");
    return y;
  }

  // ------------------------------------------------------------ values
  // The value forms, named at the root scope (sc[D].priv(...) names them in
  // the scope sc):
  //   priv(T{}, nm, shape)                       chosen by the prover;
  //   priv(T{}, nm, shape, depends_on(y...), fn) computed by the prover as
  //                                              fn(y...) (Scope::priv_in);
  //   pub(T{}, nm, shape[, codec])               a statement value;
  //   pub(T{}, nm, shape, depends_on(y...), fn_id, fn)
  //                                              computed by both parties
  //                                              from public values;
  //   pub_bytes(nm, n[, codec])                  a byte-string statement,
  //                                              which only a computed pub
  //                                              (or a priv) reads;
  //   constant(nm, values)                       fixed by the system;
  //   challenge([label[, Subfield{}][, n][, depends_on(...)]])
  //                                              verifier randomness of the
  //                                              field or its designated
  //                                              subfield.
  // T is Bit{}, Subfield{}, Subfield<GF<d>>{} or Field{}.
  template <class T, class... A>
  Ref<F, T, Committed> priv(T t, const std::string &nm, A &&...a) {
    return ScopedDomain<F>(*this, root()).priv(t, nm, std::forward<A>(a)...);
  }
  // The value forms without a name: each is named after its node (priv<k> or
  // pub<k> for node k), and a public computation without a function id is
  // identified as "pub".
  template <class T>
  Ref<F, T, Committed> priv(T t, Shape shape) {
    return priv(t, auto_name("priv"), std::move(shape));
  }
  template <class T, class... R, class Fn>
  Ref<F, T, Committed> priv(T t, Shape shape, Deps<R...> deps, Fn fn) {
    return priv(t, auto_name("priv"), std::move(shape), std::move(deps),
                std::move(fn));
  }
  template <class T>
  Ref<F, T, Public> pub(T t, Shape shape) {
    return pub(t, auto_name("pub"), std::move(shape));
  }
  template <class T, class... R, class Fn>
  Ref<F, T, Public> pub(T t, Shape shape, Deps<R...> deps, Fn fn) {
    return pub(t, auto_name("pub"), std::move(shape), std::move(deps),
               computes("pub"), std::move(fn));
  }
  // A member of a Witness struct (relation.h), committed under its name,
  // its shape from its type: priv(m) commits bytes and bools as Bit and
  // field elements as Field; priv(T{}, m) as type T (relation.h lists the
  // conversions).
  template <class M>
  auto priv(const In<M> &m);
  template <class T, class M>
  Ref<F, T, Committed> priv(T t, const In<M> &m);
  // Whether X is an expression argument of priv(e): an expression or an
  // affine expression of this domain's field, not a handle.
  template <class X, class = void>
  struct ExprArg : std::false_type {};
  template <class X>
  struct ExprArg<X, std::enable_if_t<kIsPoly<X>>>
      : std::bool_constant<!IsRef<std::decay_t<X>>::value &&
                           std::is_same_v<PolyField<X>, F>> {};
  template <class X>
  static constexpr bool kIsExprArg = ExprArg<X>::value;
  // priv(e), priv(nm, e) for an expression E of this domain's field: a
  // private value y of E's shape and type whose honest witness is E's
  // value (the compiler evaluates E), constrained by assert_equal(y, e),
  // placed as any other predicate. Unlike priv(m) for a Witness member,
  // which leaves the prover free, it adds the equality. Its phase is the
  // largest among E's leaves. Defined in predicates.h.
  template <class X, class = std::enable_if_t<kIsExprArg<X>>>
  Ref<F, PolyType<X>, Committed> priv(const X &e);
  template <class X, class = std::enable_if_t<kIsExprArg<X>>>
  Ref<F, PolyType<X>, Committed> priv(const std::string &nm, const X &e);
  // priv(nm, e) whose honest witness STEP computes (HostStep), in
  // characteristic 2 where E and STEP's base have word-level programs;
  // E's program otherwise. The same value, node and predicate.
  Ref<F, Bit, Committed> priv(const std::string &nm, const Expr<F, Bit> &e,
                              const HostStep<F> &step);
  // copy_of(x), copy_of(nm, x) for a Bit value X of another field: this
  // domain's private Bit copy y of X's shape, filled by copying the bits,
  // and the cross-field assert_equal(y, x), this domain's side first (the
  // MAC names its members in that order); returns y. x.to(D) is the same
  // copy with the equality x's side first. NM names the copy (unnamed:
  // priv<k>). Defined in predicates.h.
  template <class G, class T, class P>
  Ref<F, Bit, Committed> copy_of(const Ref<G, T, P> &x);
  template <class G, class T, class P>
  Ref<F, Bit, Committed> copy_of(const std::string &nm, const Ref<G, T, P> &x);
  // A handle is a value already: priv(x) would only copy it under an
  // equality. Within a domain read x itself; across domains, x.to(D) or
  // D.copy_of(x).
  template <class G, class T, class P>
  void priv(const Ref<G, T, P> &x) = delete;
  template <class G, class T, class P>
  void priv(const std::string &nm, const Ref<G, T, P> &x) = delete;
  template <class T, class... A>
  Ref<F, T, Public> pub(T t, const std::string &nm, A &&...a) {
    return ScopedDomain<F>(*this, root()).pub(t, nm, std::forward<A>(a)...);
  }
  template <class... A>
  Ref<F, Bytes, Public> pub_bytes(const std::string &nm, A &&...a) {
    return ScopedDomain<F>(*this, root()).pub_bytes(nm, std::forward<A>(a)...);
  }
  Ref<F, Field, Public> constant(const std::string &nm, std::vector<Elt> v) {
    return ScopedDomain<F>(*this, root()).constant(nm, std::move(v));
  }
  template <class... A>
  Ref<F, Field, Public> challenge(A &&...a) {
    return ScopedDomain<F>(*this, root()).challenge(std::forward<A>(a)...);
  }
  // challenge_outside(label, reads, in_u): a challenge uniform in F minus
  // the set U whose membership test IN_U builds from the public values
  // READS (challenge_outside_in).
  Ref<F, Field, Public> challenge_outside(std::string label,
                                          std::vector<size_t> reads,
                                          ExcludedSet<F> in_u) {
    return ScopedDomain<F>(*this, root())
        .challenge_outside(std::move(label), std::move(reads),
                           std::move(in_u));
  }

  // An affine view: no storage, no message; its relation is part of the
  // system. Its phase is the largest among what it reads.
  //
  // derive(Bit{}, ...) is a derived Bit: the core adds the circuit check
  // x (x - 1) = 0 on each coordinate (so the view must be circuit-readable),
  // and the value is a Bit wherever a Bit is read (the MAC equality, the
  // selection's stream). Without a tag the view is Field.
  Ref<F, Field, Committed> derive(std::string nm, const Lin<F> &e) {
    return derive(Field{}, std::move(nm), e);
  }
  template <class T>
  Ref<F, T, Committed> derive(T, std::string nm, const Lin<F> &e) {
    static_assert(is_field_v<T> || is_bit_v<T>,
                  "derive: a derived value is Field, or Bit with a Boolean "
                  "check");
    return derived<T>(std::move(nm), e, is_bit_v<T> ? kCheckedBit : kPlain);
  }
  // An uncommitted Bit whose 0/1-ness is the caller's responsibility (an
  // argument outside this system shows it, as MemoryShuffle.sound does for
  // ML-DSA's decoded c): no check is added, and the compile report lists it.
  Ref<F, Bit, Committed> bit_from_unchecked(std::string nm, const Lin<F> &e) {
    return derived<Bit>(std::move(nm), e, kUncheckedBit);
  }
  // A handle is read as its affine expression (a handle is also an
  // Expr, which the overload below takes).
  template <class T, class P>
  Ref<F, Bit, Committed> bit_from_unchecked(std::string nm,
                                            const Ref<F, T, P> &e) {
    return bit_from_unchecked(std::move(nm), Lin<F>(e));
  }
  // The same over any expression (expr.h), such as ML-DSA's c_enc^2 +
  // c_enc. It has no committed coordinate: a circuit reads it, emitting the
  // expression in place, and an affine row cannot (CircuitOnly). Generators
  // read its value, which the host computes with the same emitter.
  template <class T>
  Ref<F, Bit, CircuitOnly> bit_from_unchecked(std::string nm,
                                              const Expr<F, T> &x) {
    const ExprPtr<F> e = x.node;
    if (e->f != f_) fail("bit_from_unchecked '" + nm + "': another field");
    if (e->structured)
      fail("bit_from_unchecked '" + nm + "': the expression applies the "
           "operator '" + e->structured_op + "', which a circuit cannot "
           "expand");
    const Shape shape(e->dims());
    Node nd = base(Kind::kDerived, std::move(nm), Bit{}, shape);
    nd.deps = expr_deps(e);
    describe_expr<F>(
        e, [this](const Lin<F> &l) { return describe_lin(l); }, nd.descr);
    put_u64(nd.descr, kUncheckedBit);
    NodeGen<F> gen;
    gen.eval = [e](const ValueReader &v) {
      return eval_expr(e, v);
    };
    const size_t id = add_node(std::move(nd), std::move(gen));
    exprs_[id] = e;
    unchecked_bits_.push_back(id);
    return ref<Bit, CircuitOnly>(id, shape);
  }
  // Whether node ID is defined by a non-affine expression (no affine row
  // reads it).
  bool circuit_only(size_t id) const { return exprs_.count(id) != 0; }

  // A range request: every coordinate of V is below N.
  // assert_range(v, n) establishes N = n; assert_range(v, n, MaxBound{m}) some N with
  // n <= N <= m, which the range lowering selects. The honest value is
  // below n in both forms.
  RangeHandle<F> assert_range(const Lin<F> &v, Bound n, std::string nm = "") {
    return add_request(v, n, n, false, std::move(nm));
  }
  RangeHandle<F> assert_range(const Lin<F> &v, Bound n, MaxBound m,
                         std::string nm = "") {
    return add_request(v, n, m.m, true, std::move(nm));
  }
  // assert_range(v, n, Slack{}): m is derived at compile (RangeRequest::
  // slack).
  RangeHandle<F> assert_range(const Lin<F> &v, Bound n, Slack,
                              std::string nm = "") {
    RangeHandle<F> h = add_request(v, n, n, false, std::move(nm));
    requests_.back().slack = true;
    return h;
  }
  // A request that interval propagation must establish (kImplied): the
  // integer interval of V, from its terms' proven bounds and constants,
  // lies in [0, N) for some n <= N <= m. The planner searches the terms'
  // realizations for it, and compile fails when none admits it (the MAC's
  // no-wrap condition).
  RangeHandle<F> assert_range_implied(const Lin<F> &v, Bound n, MaxBound m,
                                 std::string nm) {
    RangeHandle<F> h = add_request(v, n, m.m, true, std::move(nm));
    requests_.back().implied_only = true;
    return h;
  }

  // The affine constraint e = 0, one row per coordinate.
  void affine(std::string nm, const Lin<F> &e) {
    affine_.push_back(AffineDecl{std::move(nm), e});
  }

  // A constant of this domain's field that stands alone, with no other
  // operand to take a field from (an operand of +, -, *, the gates, the
  // comparisons or mux lifts its plain C++ constants itself): VALUES
  // (integers below the characteristic in absolute value, or field
  // elements) in SHAPE (rank 1 by default). An expression, never committed;
  // its values enter each predicate's description, as every constant's do.
  // constant(Bit{}, values) is a Bit constant, its values 0 or 1. VALUES
  // is a std::vector of integers or elements, or a std::array or C array of
  // integers of any rank (its shape, unless SHAPE is given). In
  // characteristic 2 an integer constant is 0 or 1, a Bit.
  template <class K>
  auto constant(const K &values, Shape shape = Shape()) const {
    if constexpr (is_bit_v<expr_internal::LiftType<F, K>>) {
      return constant(Bit{}, values, std::move(shape));
    } else {
      return Expr<F, Field>(
          expr_internal::lift_array(*f_, values, shape.dims));
    }
  }
  template <class K>
  Expr<F, Bit> constant(Bit, const K &values, Shape shape = Shape()) const {
    return Expr<F, Bit>(
        expr_internal::lift_bits(*f_, values, shape.dims, "constant"));
  }

  // E = 0 at every coordinate, for any expression (expr.h). The domain
  // places it when it compiles (Placement): affine rows when E is affine
  // (a constraint that reads a structured operator must be), otherwise the
  // cheapest admissible target by the profile's rates (placement.h):
  // quadratic triples for a b - c on committed phase-0 Field cells, a field
  // batch for a degree-2 polynomial in relatively packed subfield cells, or
  // the circuit. pin() on the returned predicate fixes the placement.
  template <class T>
  Predicate assert_zero(std::string nm, const Expr<F, T> &e) {
    return add_predicate(std::move(nm), e.node, false);
  }
  // B = 1 at every coordinate of the Bit expression B (Logic::assert1 in a
  // circuit, the row 1 - b = 0 when B is affine).
  Predicate assert_true(std::string nm, const Expr<F, Bit> &b) {
    return add_predicate(std::move(nm), b.node, true);
  }
  const std::vector<PredDecl> &predicates() const { return preds_; }
  // Fixes where the Boolean checks of this domain's phase-0 Bit cells go,
  // in place of the placement rule: kQuadratic (b b = b, without relative
  // packing), kCircuit, or kBatch (one field batch, under relative packing
  // in odd characteristic). kAuto restores the rule.
  void pin_bit_checks(Placement where) {
    if (where == Placement::kAffine)
      fail("domain " + name + ": a Boolean check is not affine");
    bit_pin_ = where;
  }

  // Elementwise a * b = c on committed phase-0 variables. Quadratic rows
  // read ambient coordinates, which only Field cells have: relative packing
  // gives a Subfield or Bit cell none of its own, so their products are
  // circuit constraints.
  template <class A, class B, class C>
  void quadratic(A, B, C) {
    static_assert(kTypeError<A, B, C>,
                  "quadratic: a triple reads Field cells (Ref<F, Field, "
                  "Committed>); write a product of Bit or Subfield values as "
                  "a circuit constraint");
  }
  void quadratic(Ref<F, Field, Committed> a, Ref<F, Field, Committed> b,
                 Ref<F, Field, Committed> c) {
    check(a.n == b.n && b.n == c.n, "quadratic: length mismatch");
    quads_.push_back(QuadDecl{a.id, b.id, c.id});
  }

  // The words that the computed Bit value V is committed as when it is
  // stored as words (V is their bit view), or none: a bit view of some of
  // the words (bits(nm, words, select)) is then read without the others.
  std::optional<Ref<F, Subfield<>, Committed>> words_of(
      const Ref<F, Bit, Committed> &v) const {
    const Node &n = g_->nodes.at(v.id);
    if (n.kind != Kind::kBitView || n.deps.size() != 1) return std::nullopt;
    const Node &w = g_->nodes.at(n.deps[0]);
    if (w.type.base != Base::kSubfield || w.type.degree != 0 ||
        16 * w.n != v.n)
      return std::nullopt;
    return ref<Subfield<>, Committed>(n.deps[0], Shape(w.n));
  }

  // A bit view: the canonical bits of the phase-0 Subfield words SELECT of
  // WORDS (every word by default), d per word for words of GF(2^d), bit j
  // of a word as the coefficient of the subfield's basis element j
  // (SubfieldInfo; beta_j for the designated subfield). It allocates no
  // second witness: each viewed word's d wires alias the committed word,
  // whose bits the packing tree's bit stage decodes. Circuits and affine
  // rows read it (its bits are packed coordinates of the bit node). The
  // words may lie in any node on the path from the bit node up, below K: a
  // word above the bit node's parent is decoded through the nodes between
  // (ComposedBits, tree_zk.h), and its view still holds its canonical bits.
  template <class W, class... Rest>
  Ref<F, Bit, Committed> bits(std::string, W, Rest...) {
    static_assert(kTypeError<W>,
                  "bits: a bit view reads committed Subfield words "
                  "(Ref<F, Subfield<S>, Committed>)");
    return {};
  }
  template <class Sb>
  Ref<F, Bit, Committed> bits(std::string nm,
                              Ref<F, Subfield<Sb>, Committed> words) {
    std::vector<size_t> all(words.n);
    for (size_t i = 0; i < all.size(); ++i) all[i] = i;
    return bits(std::move(nm), words, std::move(all));
  }
  template <class Sb>
  Ref<F, Bit, Committed> bits(std::string nm,
                              Ref<F, Subfield<Sb>, Committed> words,
                              std::vector<size_t> select) {
    for (size_t y : select) check(y < words.n, "bit view: word index");
    static_assert(F::kCharacteristicTwo || kTypeError<Sb>,
                  "bits: a bit view reads words of a binary field; bits of "
                  "words exist in characteristic 2");
    const size_t d =
        subfield_degree<F>(g_->nodes.at(words.id).type.degree);
    if (d > 64) fail("bit view '" + nm + "': words above 64 bits");
    Node nd = base(Kind::kBitView, std::move(nm), Bit{}, d * select.size());
    nd.deps = {words.id};
    put_u64(nd.descr, select.size());
    for (size_t y : select) put_u64(nd.descr, y);
    const F *pf = f_;
    const size_t wid = words.id;
    NodeGen<F> gen;
    gen.eval = [pf, wid, select, d](const ValueReader &v) {
      const auto &w = v.template get<F>(wid);
      std::vector<Elt> out;
      out.reserve(d * select.size());
      if constexpr (F::kCharacteristicTwo) {
        const auto &sub = SubfieldInfo<F>::get(*pf, d);
        for (size_t y : select) {
          const uint64_t u = sub.bits(*pf, w.at(y));
          for (size_t j = 0; j < d; ++j)
            out.push_back(ct::bit_elt(*pf, u >> j));
        }
      }
      return out;
    };
    const size_t id = add_node(std::move(nd), std::move(gen));
    views_[id] = std::move(select);
    return ref<Bit, Committed>(id, d * views_[id].size());
  }

  // A batched relation (batch.h): for every instance, the relation's
  // polynomial of the operands MAP reads from TABLES (phase-0 Subfield
  // tables of this domain, words concatenated in order) is zero, proved by
  // the masked skip with skip WIDTH. The operand map picks the realization:
  //   - a BitOperandMap<F, R, W> reads the bits of GF(2^W) words
  //     (characteristic 2), and the relation is a tag R (SkipChi{}) with
  //     coefficients in GF(2); the first round is bit-sliced;
  //   - a FieldOperandMap reads field elements (any characteristic), and
  //     the relation is a FieldRelation; the first round is evaluated in F.
  template <class Rel, class Map>
  void batch(std::string nm,
             std::vector<Ref<F, Subfield<>, Committed>> tables, Rel rel,
             std::shared_ptr<const Map> map,
             unsigned width = default_batch_width<Map>()) {
    batch<Designated, Rel, Map>(std::move(nm), std::move(tables),
                                std::move(rel), std::move(map), width);
  }
  template <class Sb, class Rel, class Map>
  void batch(std::string nm,
             std::vector<Ref<F, Subfield<Sb>, Committed>> tables, Rel rel,
             std::shared_ptr<const Map> map,
             unsigned width = default_batch_width<Map>()) {
    if constexpr (std::is_base_of_v<compiler::FieldOperandMap<F>, Map>) {
      static_assert(std::is_same_v<Rel, compiler::FieldRelation<F>>,
                    "a batch over a FieldOperandMap takes a FieldRelation");
      batch(std::move(nm), std::move(tables),
            std::vector<compiler::FieldBatchPart<F>>{
                compiler::FieldBatchPart<F>{std::move(rel), std::move(map)}},
            width);
    } else {
      batches_.push_back(
          batch_decl(rel, std::move(nm), std::move(tables), map, width));
    }
  }
  // Several relations on field-element operands with the same instances
  // and skip width, merged into one zerocheck of Q_1 + gamma Q_2 + ...;
  // MAP i reads its part of TABLES (the parts' words concatenated in order).
  void batch(std::string nm, std::vector<Ref<F, Subfield<>, Committed>> tables,
             std::vector<compiler::FieldBatchPart<F>> parts,
             unsigned width = 4) {
    batch<Designated>(std::move(nm), std::move(tables), std::move(parts),
                      width);
  }
  template <class Sb>
  void batch(std::string nm,
             std::vector<Ref<F, Subfield<Sb>, Committed>> tables,
             std::vector<compiler::FieldBatchPart<F>> parts,
             unsigned width = 4) {
    BatchDecl b{std::move(nm), {}, nullptr, width, ""};
    for (const auto &t : tables) b.tables.push_back(t.id);
    const size_t d = subfield_degree<F>(type_in<F, Subfield<Sb>>().degree);
    b.missing = compiler::field_batch_error(*f_, parts, width);
    if (b.missing.empty())
      b.ops = compiler::field_batch_operands(*f_, std::move(parts), d);
    batches_.push_back(std::move(b));
  }
  // The default skip width: 16 for bit operands, 4 for field operands.
  template <class Map>
  static constexpr unsigned default_batch_width() {
    return std::is_base_of_v<compiler::FieldOperandMap<F>, Map> ? 4 : 16;
  }
  // A bit-operand batch's declaration.
  template <class R, class Map, class Sb>
  BatchDecl batch_decl(R, std::string nm,
                       std::vector<Ref<F, Subfield<Sb>, Committed>> tables,
                       std::shared_ptr<const Map> map, unsigned width) {
    BatchDecl b{std::move(nm), {}, nullptr, width, ""};
    for (const auto &t : tables) b.tables.push_back(t.id);
    if constexpr (F::kCharacteristicTwo) {
      constexpr size_t W = Map::kWordBits;
      static_assert(std::is_base_of_v<compiler::BitOperandMap<F, R, W>, Map>,
                    "a bit-operand batch takes a BitOperandMap<F, R, W>");
      b.missing = compiler::relation_error<R>(width);
      if (b.missing.empty())
        b.ops = compiler::bit_batch_operands(
            *f_,
            std::static_pointer_cast<const compiler::BitOperandMap<F, R, W>>(
                map),
            width);
    } else {
      static_assert(kTypeError<R, Map>,
                    "batch: a relation tag reads bit operands, which exist in "
                    "characteristic 2; in an odd-characteristic domain, "
                    "declare the relation as a FieldRelation over a "
                    "FieldOperandMap");
    }
    return b;
  }

  size_t wire(const ViewSource &src) override {
    const size_t id =
        wiring("view" + std::to_string(g_->nodes.size()), src).id;
    g_->nodes.at(id).auto_view = true;
    return id;
  }

  // Each predicate's name and its degree in each challenge it reads
  // (challenge_degrees), which compile() sums into degree bounds.
  std::vector<std::pair<std::string, std::vector<std::pair<size_t, size_t>>>>
  predicate_degrees() const override {
    std::vector<std::pair<std::string, std::vector<std::pair<size_t, size_t>>>>
        out;
    for (const auto &p : preds_)
      out.push_back({p.name, challenge_degrees(p.e, g_->nodes)});
    return out;
  }

  std::vector<std::pair<std::string, std::vector<size_t>>> constraint_reads()
      const override {
    std::vector<std::pair<std::string, std::vector<size_t>>> out;
    for (const auto &c : circuits_) out.push_back({c.name, c.reads});
    for (const auto &a : affine_)
      if (a.pred < 0) out.push_back({a.name, a.e.deps()});
    for (const auto &q : quads_) out.push_back({"quadratic", {q.a, q.b, q.c}});
    for (const auto &b : batches_) out.push_back({b.name, b.tables});
    return out;
  }
  std::vector<size_t> bound_ids() const override {
    std::vector<size_t> out;
    for (const auto &[id, v] : bound_) out.push_back(id);
    return out;
  }
  const RangeRealization *find_request(const std::string &nm,
                                       bool &lowered) const override {
    for (const auto &r : requests_)
      if (r.name == nm) {
        lowered = r.lowered;
        return &r.realization;
      }
    return nullptr;
  }
  size_t pending_requests() const override {
    size_t k = 0;
    for (const auto &r : requests_) k += r.lowered ? 0 : 1;
    return k;
  }

  // The requests and their realizations (after lowering).
  const std::vector<RangeRequest<F>> &requests() const { return requests_; }
  // The view a bound node is read through, and its report line.
  const std::map<size_t, Lin<F>> &bindings() const { return bound_; }
  // The affine expression of a derived node.
  const Lin<F> &lin(size_t id) const { return lins_.at(id); }
  // The coordinates a view node of this domain reads ((node, index), or
  // kZeroCoordinate), or null when ID is no view.
  const std::vector<std::pair<size_t, size_t>> *view_sources(size_t id) const {
    auto it = wiring_.find(id);
    return it == wiring_.end() ? nullptr : &it->second;
  }
  // B2 of a binding: X is no batch table, bit-view source or quadratic
  // operand, and is not bound yet.
  bool bindable_shape(size_t x) const {
    if (bound_.count(x)) return false;
    for (const auto &b : batches_)
      for (size_t t : b.tables)
        if (t == x) return false;
    for (const auto &[v, sel] : views_)
      if (g_->nodes.at(v).deps.at(0) == x) return false;
    for (const auto &q : quads_)
      if (q.a == x || q.b == x || q.c == x) return false;
    return true;
  }
  // The range lowering's tables, after lowering.
  const std::vector<RangeTableStats> &range_tables() const {
    return range_tables_;
  }
 protected:
  template <class, class, class>
  friend class compiler::CompiledDomain;
  friend class compiler::Lowering;
  friend class Scope;
  template <class>
  friend class ScopedDomain;
  template <class, class...>
  friend class BasicConstraintSystem;

  // A GKR circuit constraint. FN(lc, wires_1, ..., wires_k) builds gates
  // with the Logic object over this domain's QuadCircuit, reading the
  // declared values as wire vectors, and asserts with lc.assert0 /
  // lc.assert_eq. Compiler tier: lowerings reach it through Lowering::gkr;
  // applications state predicates pinned to the circuit instead.
  template <class... R, class Fn>
  void gkr(std::string nm, Deps<R...> r, Fn fn,
           std::optional<std::vector<uint8_t>> key = std::nullopt) {
    static_assert((IsRef<R>::value && ...),
              "gkr: a circuit reads value handles (depends_on of a "
              "host input is for generators)");
    static_assert((!is_bytes_v<typename R::type_tag> && ...),
              "gkr: a constraint reads no Bytes statement; read it "
              "through a public computation");
    static_assert((std::is_same_v<typename R::field_type, F> && ...),
              "gkr: every value a circuit reads lies in its domain's "
              "field");
    static_assert(std::is_invocable_v<
                  const Fn &, const CLogic &,
                  const std::conditional_t<true, Tensor<size_t>, R> &...>,
              "gkr: the closure must take the Logic object and one "
              "wire tensor (Tensor<size_t>, or const "
              "std::vector<size_t>&) per depends_on entry, in order");
    std::vector<std::vector<size_t>> dims;
    std::apply([&](const auto &...x) { (dims.push_back(x.dims()), ...); },
           r.refs);
    circuits_.push_back(CircuitDecl{
        std::move(nm), r.ids(),
        [fn, dims](const CLogic &lc, const std::vector<Wires> &w) {
          call(fn, lc, w, dims, std::index_sequence_for<R...>{});
        },
        -1, std::move(key)});
  }
  // A circuit over a data-dependent list of reads of this field: FN(lc, w)
  // receives one wire vector per read. KEY describes what FN's circuit
  // depends on beyond the compiler's code and R (the compile cache's key).
  template <class Fn>
  void gkr(std::string nm, const std::vector<Ref<F>> &r, Fn fn,
           std::optional<std::vector<uint8_t>> key = std::nullopt) {
    static_assert(std::is_invocable_v<const Fn &, const CLogic &,
                                  const std::vector<Wires> &>,
              "gkr over a list of reads: the closure must take the "
              "Logic object and a const std::vector<std::vector<size_t>>&, "
              "one wire vector per read");
    std::vector<size_t> ids;
    for (const auto &x : r) ids.push_back(x.id);
    circuits_.push_back(CircuitDecl{
        std::move(nm), ids,
        [fn](const CLogic &lc, const std::vector<Wires> &w) { fn(lc, w); },
        -1, std::move(key)});
  }

  // Adds node ND with the generator GEN to the system's graph; the system's
  // implementation wraps GEN for its field set.
  virtual size_t add_node(Node nd, NodeGen<F> gen) const = 0;

  // The system's root scope, which names the value forms.
  // The name of an unnamed value form, KIND<k> for the node k it adds.
  std::string auto_name(const char *kind) const {
    return std::string(kind) + std::to_string(g_->nodes.size());
  }
  const Scope &root() const {
    if (sys_ == nullptr) fail("domain " + name + " belongs to no system");
    return sys_->root();
  }

  // ------------------------------------------------- value forms (impl)
  // The value forms' implementations, each named NM in the scope SC
  // (D.priv(...) at the root scope, sc[D].priv(...) in sc).

  // A public node of this domain's field (domain -1) named NM in SC.
  Node pub_node(const Scope &sc, Kind k, std::string nm,
                const Shape &n) const {
    Node nd;
    nd.kind = k;
    nd.name = sc.scoped(nm);
    nd.field = field_id;
    nd.fobj = fobj;
    nd.n = n.size();
    nd.shape = n.dims;
    return nd;
  }

  // pub(T{}, nm, shape): a statement value of type T (Bit{}, Subfield{},
  // Field{} or Bytes{}), supplied per proof and absorbed before any
  // commitment; phase 0. A value outside its type (a coordinate that is not
  // 0 or 1, or outside the subfield) is a malformed statement: verify()
  // returns false and prove() throws.
  template <class T, class = std::enable_if_t<is_statement_type_v<T>>>
  Ref<F, T, Public> pub_in(const Scope &sc, T, std::string nm,
                           Shape n) const {
    Node nd = pub_node(sc, Kind::kPublicInput, std::move(nm), n);
    nd.type = type_in<F, T>();
    const size_t id = add_node(std::move(nd), {});
    if constexpr (is_bytes_v<T>) bytes_record(id, n, 0, nullptr);
    return ref<T, Public>(id, n);
  }

  // The same with a codec: ACCEPTS(v) decides whether v is well formed
  // (canonical coordinates, a valid key). A statement it refuses makes
  // verify() return false and prove() throw; nothing reads the value first,
  // so a public computation may assume it. CHECK_ID names the codec and its
  // parameters for the system digest. A Bytes statement's codec takes its
  // bytes.
  template <class T, class Pred,
            class = std::enable_if_t<is_statement_type_v<T>>>
  Ref<F, T, Public> pub_in(const Scope &sc, T, std::string nm, Shape n,
                           const Computes &check_id, Pred accepts) const {
    using Arg = std::conditional_t<is_bytes_v<T>, std::vector<uint8_t>,
                                   std::vector<Elt>>;
    static_assert(std::is_invocable_r_v<bool, const Pred &, const Arg &>,
                  "pub: the codec must take a const std::vector<Elt>& of the "
                  "value's field (bytes for a Bytes statement) and return "
                  "bool");
    Node nd = pub_node(sc, Kind::kPublicInput, std::move(nm), n);
    nd.type = type_in<F, T>();
    put_str(nd.descr, check_id.name);
    put_u64(nd.descr, check_id.params.size());
    nd.descr.insert(nd.descr.end(), check_id.params.begin(),
                    check_id.params.end());
    NodeGen<F> gen;
    if constexpr (is_bytes_v<T>) {
      gen.accepts_bytes = [accepts](const std::vector<uint8_t> &v) {
        return accepts(v) ? kAccepted : kRejected;
      };
    } else {
      gen.accepts = [accepts](const std::vector<Elt> &v) {
        return accepts(v) ? kAccepted : kRejected;
      };
    }
    const size_t id = add_node(std::move(nd), std::move(gen));
    if constexpr (is_bytes_v<T>) bytes_record(id, n, 1, &check_id);
    return ref<T, Public>(id, n);
  }
  // A shaped statement with a per-row codec (per_row(id, pred)): PRED
  // checks each row of the leading axis, a Tensor of elements (the row's
  // bytes for a Bytes statement); one malformed row rejects the statement,
  // and Prepared::rejected_row() names it.
  template <class T, class Pred,
            class = std::enable_if_t<is_statement_type_v<T>>>
  Ref<F, T, Public> pub_in(const Scope &sc, T, std::string nm, Shape n,
                           PerRow<Pred> codec) const {
    using Arg = std::conditional_t<is_bytes_v<T>, std::vector<uint8_t>,
                                   Tensor<Elt>>;
    static_assert(std::is_invocable_r_v<bool, const Pred &, const Arg &>,
                  "pub: a per-row codec takes a row (a Tensor of elements, "
                  "or a std::vector<uint8_t> of a Bytes statement's row) and "
                  "returns bool");
    Node nd = pub_node(sc, Kind::kPublicInput, std::move(nm), n);
    nd.type = type_in<F, T>();
    put_str(nd.descr, "per_row");
    put_str(nd.descr, codec.id.name);
    put_u64(nd.descr, codec.id.params.size());
    nd.descr.insert(nd.descr.end(), codec.id.params.begin(),
                    codec.id.params.end());
    const std::vector<size_t> dims = n.dims;
    const size_t rows = dims.at(0), per = n.size() / dims.at(0);
    auto pred = codec.pred;
    NodeGen<F> gen;
    if constexpr (is_bytes_v<T>) {
      gen.accepts_bytes = [pred, rows, per](const std::vector<uint8_t> &v) {
        for (size_t i = 0; i < rows; ++i)
          if (!pred(std::vector<uint8_t>(v.begin() + long(i * per),
                                         v.begin() + long((i + 1) * per))))
            return long(i);
        return kAccepted;
      };
    } else {
      gen.accepts = [pred, rows, dims](const std::vector<Elt> &v) {
        const Tensor<Elt> t(v, dims);
        for (size_t i = 0; i < rows; ++i)
          if (!pred(t.row(i))) return long(i);
        return kAccepted;
      };
    }
    const size_t id = add_node(std::move(nd), std::move(gen));
    if constexpr (is_bytes_v<T>) bytes_record(id, n, 2, &codec.id);
    return ref<T, Public>(id, n);
  }

  // pub(T{}, nm, shape, depends_on(y...), fn_id, fn): a public value both
  // parties compute from public values (statement, challenges, constants);
  // its phase is the largest among the ys. FN_ID names the function FN
  // computes and its parameters (a basis, a count), so the system digest
  // identifies it. Every y is a public value: a committed handle is a C++
  // compile error. FN takes one const std::vector<Elt>& per dependency and
  // returns std::vector<Elt>; or, in odd characteristic, the same over
  // canonical integers (NatInt or uint64_t), as priv's closures read them.
  template <class T, class... R, class Fn>
  Ref<F, T, Public> pub_in(const Scope &sc, T, std::string nm, Shape n,
                           Deps<R...> deps, const Computes &fn_id,
                           Fn fn) const {
    static_assert(is_value_type_v<T>,
                  "pub: the type is Bit, Subfield or Field");
    static_assert(!(IsHost<R>::value || ...),
                  "pub: a host input is private; only generators "
                  "read it");
    static_assert(((std::is_same_v<typename R::place_tag, Public> ||
                    std::is_same_v<typename R::place_tag, AnyPlace>) &&
                   ...),
                  "pub: every dependency is a public value");
    constexpr bool kSignature = std::is_invocable_r_v<
        std::vector<Elt>, Fn, const typename DepArg<R>::type &...>;
    // A closure over canonical integers (NatInt or uint64_t), read as such
    // from its parameters, as advice reads it.
    using I0 = nat_internal::Integer<Fn, R...>;
    using I = std::conditional_t<std::is_void_v<I0>, NatInt, I0>;
    constexpr bool kNat = !kSignature && !std::is_void_v<I0> &&
                          nat_internal::kVector<I, Fn, R...>;
    static_assert(kSignature || kNat,
                  "pub: the closure must take one const "
                  "std::vector<Elt>& per depends_on entry, in order, each in "
                  "that entry's field, and return std::vector<Elt> of the "
                  "computation's field; or the same over canonical integers "
                  "(const std::vector<NatInt>& or const "
                  "std::vector<uint64_t>&, returning a std::vector of them)");
    static_assert(!kNat || (!F::kCharacteristicTwo &&
                            ((IsBytesArg<R>::value ||
                              !R::field_type::kCharacteristicTwo) &&
                             ...)),
                  "pub over integers: canonical integers exist in "
                  "odd characteristic only");
    // An expression's leaves are checked here: its type does not track
    // them.
    std::apply(
        [&](const auto &...r) {
          (
              [&](const auto &x) {
                if constexpr (IsExprDep<std::decay_t<decltype(x)>>::value)
                  for (size_t id : x.ids())
                    if (!is_public(g_->nodes.at(id).kind))
                      fail("pub '" + sc.scoped(nm) + "': a dependency reads '" +
                           g_->nodes.at(id).name +
                           "', which is not a public value");
              }(r),
              ...);
        },
        deps.refs);
    Node nd = pub_node(sc, Kind::kPublicCompute, nm, n);
    nd.type = type_in<F, T>();
    nd.deps = deps.ids();
    // A closure the application or a library function declares, or one a
    // lowering declares inside a core realization ((Pub-chal) in compile()).
    nd.origin =
        sys_->lowering().empty() ? "application" : sys_->lowering();
    put_str(nd.descr, fn_id.name);
    put_u64(nd.descr, fn_id.params.size());
    nd.descr.insert(nd.descr.end(), fn_id.params.begin(), fn_id.params.end());
    NodeGen<F> gen;
    if constexpr (kSignature) {
      auto refs = deps.refs;
      gen.eval = [refs, fn](const ValueReader &v) {
        std::vector<Elt> out = std::apply(
            [&](const auto &...r) { return fn(record_arg(v, r)...); }, refs);
        return out;
      };
    } else if constexpr (kNat) {
      if constexpr (std::is_same_v<I, uint64_t>) {
        if (field_characteristic(*f_) > (Bound(1) << 64))
          fail("pub '" + sc.scoped(nm) + "': uint64_t integers hold "
               "no canonical integer of a field of characteristic above 2^64; "
               "take NatInt");
      }
      auto refs = deps.refs;
      const F *pf = f_;
      const std::string label = sc.scoped(nm);
      gen.eval = [refs, fn, pf, label](const ValueReader &v) {
        size_t k = 0;
        auto in = std::apply(
            [&](const auto &...r) {
              return std::make_tuple(nat_record_arg<I>(v, r, label, k++)...);
            },
            refs);
        const std::vector<I> out = std::apply(
            [&](const auto &...x) { return fn(nat_tensor(x)...); }, in);
        return elements(*pf, field_characteristic(*pf), out, label);
      };
    }
    return ref<T, Public>(add_node(std::move(nd), std::move(gen)), n);
  }

  // priv(T{}, nm, shape): a value of this domain of type T (Bit{},
  // Subfield{}, Subfield<GF<d>>{} or Field{}) chosen by the prover and
  // supplied in the assignment by its handle; phase 0.
  template <class T>
  Ref<F, T, Committed> priv_in(const Scope &sc, T, const std::string &nm,
                               Shape shape) {
    return declare_input(T{}, sc.scoped(nm), std::move(shape));
  }
  // priv(T{}, nm, shape, depends_on(y...), fn): a value the prover chooses
  // as FN(y...), the ys values of any domain, public values or host inputs.
  // Its phase is the largest among the ys; a value of phase 1 or more
  // (late) is sent masked by a pad, which the core allocates. The value is
  // unconstrained: a relation between it and the ys holds only where a
  // predicate states it. FN is one of:
  //   vector, field     FN(Tensor<Elt_1>, ...) -> std::vector<Elt> of the
  //                     shape's size (a Tensor converts to const
  //                     std::vector<Elt>&; a host input arrives as const
  //                     std::vector<uint8_t>&);
  //   elementwise, field  FN(Elt_1, ...) -> Elt per coordinate, each
  //                     dependency broadcast to SHAPE (NumPy's rules);
  //   integers          the same two forms over canonical integers of
  //                     prime-field values (NatInt or uint64_t), in odd
  //                     characteristic: a dependency element outside the
  //                     prime field and an output of at least p are run-time
  //                     errors naming the value. FN is read this way when
  //                     its parameters are integers, and nat(FN) states it.
  // The elementwise form is chosen when FN accepts it; Bound when FN reads
  // Bound, uint64_t otherwise.
  template <class T, class... R, class Fn>
  Ref<F, T, Committed> priv_in(const Scope &sc, T, const std::string &nm,
                               Shape shape, Deps<R...> deps, Fn fn) {
    return declare_advice(T{}, sc.scoped(nm), std::move(shape),
                          std::move(deps), std::move(fn));
  }
  // The same over a data-dependent list of dependencies of this field: FN
  // receives a std::vector<const std::vector<Elt> *>, one per dependency.
  template <class T, class Fn>
  Ref<F, T, Committed> priv_in(const Scope &sc, T, const std::string &nm,
                               Shape shape, const std::vector<Ref<F>> &deps,
                               Fn fn) {
    return declare_advice(T{}, sc.scoped(nm), std::move(shape), deps,
                          std::move(fn));
  }

  // constant(nm, values): a public value fixed by the system (part of the
  // system digest).
  Ref<F, Field, Public> constant_in(const Scope &sc, std::string nm,
                                    std::vector<Elt> v) const {
    const size_t n = v.size();
    Node nd = pub_node(sc, Kind::kConstant, std::move(nm), Shape(n));
    nd.descr = FieldValues<F>::bytes(*f_, v);
    NodeGen<F> gen;
    gen.eval = [v](const ValueReader &) { return v; };
    return ref<Field, Public>(add_node(std::move(nd), std::move(gen)),
                              Shape(n));
  }

  // challenge([label][, Subfield{}][, n][, depends_on(...)]): a random input
  // of F, N elements of F or of its designated subfield (TAG Subfield{}).
  // Its phase is one more than the largest phase among the tested values:
  // the declared ones (depends_on(...), an ordering hint) and those
  // compile() infers. Without depends_on, compile() infers what it tests
  // from the constraints that read it (internal::infer_phases). LABEL names
  // it (its decoding stream's label, which is distinct per challenge);
  // empty, it is challenge.<k>.
  Ref<F, Field, Public> challenge_in(const Scope &sc,
                                     std::string label = "") const {
    return challenge_at(sc, std::move(label), false, 1, Deps<>{});
  }
  template <class... T>
  Ref<F, Field, Public> challenge_in(const Scope &sc, std::string label,
                                     Deps<T...> t) const {
    return challenge_at(sc, std::move(label), false, 1, t);
  }
  template <class Tag, class = std::enable_if_t<is_value_type_v<Tag>>>
  Ref<F, Field, Public> challenge_in(const Scope &sc, std::string label, Tag,
                                     size_t n = 1) const {
    return challenge_at(sc, std::move(label), sampled_in<Tag>(), n, Deps<>{});
  }
  template <class Tag, class... T,
            class = std::enable_if_t<is_value_type_v<Tag>>>
  Ref<F, Field, Public> challenge_in(const Scope &sc, std::string label, Tag,
                                     Deps<T...> t) const {
    return challenge_at(sc, std::move(label), sampled_in<Tag>(), 1, t);
  }
  template <class Tag, class... T,
            class = std::enable_if_t<is_value_type_v<Tag>>>
  Ref<F, Field, Public> challenge_in(const Scope &sc, std::string label, Tag,
                                     size_t n, Deps<T...> t) const {
    return challenge_at(sc, std::move(label), sampled_in<Tag>(), n, t);
  }
  // Whether TAG asks for a subfield sample: Field{} the whole field,
  // Subfield{} its designated subfield.
  template <class Tag>
  static constexpr bool sampled_in() {
    static_assert(is_field_v<Tag> || std::is_same_v<Tag, Subfield<>>,
                  "challenge: a sample of the field (Field{}) or of its "
                  "designated subfield (Subfield{})");
    return !is_field_v<Tag>;
  }
  template <class... T>
  Ref<F, Field, Public> challenge_at(const Scope &sc, std::string label,
                                     bool sub, size_t n,
                                     Deps<T...> t) const {
    static_assert((kIsValueDep<T> && ...),
                  "challenge: depends_on lists the value handles and "
                  "expressions it tests");
    if (label.empty())
      label = "challenge." + std::to_string(g_->nodes.size());
    Node nd = pub_node(sc, Kind::kChallenge, std::move(label), Shape(n));
    nd.tests = t.ids();
    nd.sampler = sub ? "subfield" : "field";
    nd.origin =
        sys_->lowering().empty() ? "application" : sys_->lowering();
    const F *pf = f_;
    NodeGen<F> gen;
    gen.sample = [pf, n, sub](RandomEngine &rng, const ValueReader &) {
      std::vector<Elt> v(n);
      for (auto &x : v) x = sub ? subfield_sample(*pf, rng) : rng.elt(*pf);
      return v;
    };
    return ref<Field, Public>(add_node(std::move(nd), std::move(gen)),
                              Shape(n));
  }
  // challenge_outside(label, reads, in_u): one element uniform in F minus a
  // set U of public values (LogUp's alpha, outside the points of its
  // tables). IN_U builds U's membership test from the values READS, which
  // compile() requires to be public and drawn or computed before the
  // challenge. The challenge tests what challenge(label) would; its
  // sampler is "field-minus-tables".
  Ref<F, Field, Public> challenge_outside_in(const Scope &sc,
                                             std::string label,
                                             std::vector<size_t> reads,
                                             ExcludedSet<F> in_u) const {
    Node nd = pub_node(sc, Kind::kChallenge, std::move(label), Shape(1));
    nd.sampler = "field-minus-tables";
    nd.excludes = std::move(reads);
    nd.origin =
        sys_->lowering().empty() ? "application" : sys_->lowering();
    const F *pf = f_;
    NodeGen<F> gen;
    gen.sample = [pf, in_u](RandomEngine &rng, const ValueReader &v) {
      const std::function<bool(const Elt &)> in = in_u(v);
      // Rejection sampling: draw as challenge() does (rng.elt, itself
      // rejection sampling into F) and redraw while the element lies in U.
      // Every element of F minus U has as many accepting streams as under
      // rng.elt alone, so the result is uniform in F minus U, and prover and
      // verifier, running this on the same stream, agree on it.
      //
      // The stream budget. The challenge reads its own stream (a
      // sub-transcript of system.h's challenges()) of fs_stream_budget
      // bytes, k + kFSStreamExtraBytes, and this draw is the stream's only
      // one. fs_budget.py sets the budget for stream reads that each
      // succeed with probability at least 1/2 (the coordinate samplers of
      // rng.elt); the rejection of U adds whole redraws of rng.elt, each
      // with probability |U|/|F|. U lies in the rows of the domain's tables
      // (the lowerings keep it below 2^32 points) and |F| is at least 2^122
      // for every domain field of the instantiations (Fp14^9 is the
      // smallest), so |U|/|F| <=
      // 2^-90 and four redraws occur with probability at most 2^-360. Five
      // draws of rng.elt are at most 5 * 32 coordinates of at most 32 bytes,
      // whose Geometric(1/2) attempts exceed kFSStreamExtraBytes = 206848
      // bytes with probability far below 2^-256. The redraws therefore add
      // a negligible overrun probability, and no extend_point_budget grant
      // (which serves points with one draw per row) is needed.
      Elt x = rng.elt(*pf);
      while (in(x)) x = rng.elt(*pf);
      return std::vector<Elt>{x};
    };
    return ref<Field, Public>(add_node(std::move(nd), std::move(gen)),
                              Shape(1));
  }

  // The plan export's record of the Bytes statement ID of shape N: its
  // bytes, rows and bytes per row, its codec (0 none, 1 the whole value,
  // 2 per row, 3 member checks, which relation.h sets) and the codec's
  // integer parameters (computes()).
  void bytes_record(size_t id, const Shape &n, int codec,
                    const Computes *c) const {
    PlanRecords::Gadget rec;
    rec.name = g_->nodes.at(id).name;
    rec.kind = "bytes-codec";
    const size_t rows = n.dims.size() >= 2 ? n.dims[0] : 1;
    rec.params = {{"bytes", SignedInt(n.size())},
                  {"rows", SignedInt(rows)},
                  {"rowBytes", SignedInt(n.size() / rows)},
                  {"codec", codec}};
    if (c != nullptr && c->params.size() % 8 == 0)
      for (size_t i = 0; i < c->params.size() / 8; ++i) {
        uint64_t v = 0;
        for (size_t b = 0; b < 8; ++b)
          v |= uint64_t(c->params[8 * i + b]) << (8 * b);
        rec.params.push_back({"arg" + std::to_string(i), SignedInt(v)});
      }
    g_->records.gadgets.push_back(std::move(rec));
  }

  // A public computation's dependency argument: a Tensor of a value's
  // elements, or a host input's (Bytes statement's) bytes.
  template <class R>
  static decltype(auto) record_arg(const ValueReader &v, const R &r) {
    if constexpr (IsBytesArg<R>::value) {
      return dep_bytes(v, r);
    } else {
      return Tensor<typename R::field_type::Elt>(dep_values(v, r), r.dims());
    }
  }
  // A dependency of a public computation over integers I: (its canonical
  // integers, dims), or a pointer to its bytes.
  template <class I, class R>
  static auto nat_record_arg(const ValueReader &v, const R &r,
                             const std::string &label, size_t k) {
    if constexpr (IsBytesArg<R>::value) {
      return std::make_pair(std::vector<uint8_t>(dep_bytes(v, r)),
                            std::vector<size_t>{});
    } else {
      using G = typename R::field_type;
      const std::vector<NatInt> x =
          Domain<G>::integers(*r.f, dep_values(v, r), label, k);
      return std::make_pair(std::vector<I>(x.begin(), x.end()), r.dims());
    }
  }
  template <class I>
  static Tensor<I> nat_tensor(
      const std::pair<std::vector<I>, std::vector<size_t>> &x) {
    return Tensor<I>(x.first, x.second);
  }
  static const std::vector<uint8_t> &nat_tensor(
      const std::pair<std::vector<uint8_t>, std::vector<size_t>> &x) {
    return x.first;
  }

  // Scope::priv's declarations (and Lowering::priv's, with a pad).
  // An input, supplied by the prover, of type T (the tag Bit{}, Subfield{},
  // Subfield<GF<d>>{} or Field{}); phase 0.
  template <class T>
  Ref<F, T, Committed> declare_input(T, std::string nm, Shape shape) {
    static_assert(is_value_type_v<T>,
                  "priv: the type is Bit, Subfield or Field");
    Node nd = base(Kind::kPrivateInput, std::move(nm), type_in<F, T>(), shape);
    return ref<T, Committed>(add_node(std::move(nd), {}), shape);
  }

  // A value the prover computes as FN of DEPS (Scope::priv), masked
  // by the pad MB when it is late (Lowering::masked_by).
  template <class T, class... R, class Fn>
  Ref<F, T, Committed> declare_advice(T, std::string nm, Shape shape,
                                      Deps<R...> deps, Fn fn,
                                      MaskedBy mb = {}) {
    static_assert(is_value_type_v<T>,
                  "priv: the type is Bit, Subfield or Field");
    // A Bit value's closure may return its bits packed (PackedBits).
    constexpr bool kPacked =
        is_bit_v<T> && std::is_invocable_r_v<PackedBits, const Fn &,
                                             const VecArg<R> &...>;
    // Or as bytes (0 or 1).
    constexpr bool kBytes =
        is_bit_v<T> &&
        std::is_invocable_r_v<std::vector<uint8_t>, const Fn &,
                              const VecArg<R> &...> &&
        !std::is_invocable_r_v<std::vector<Elt>, const Fn &,
                               const VecArg<R> &...>;
    if constexpr (kPacked) {
      const size_t n = shape.size();
      auto refs = deps.refs;
      const std::string label = nm;
      std::function<std::vector<uint64_t>(const ValueReader &)> packed =
          [fn, refs, n, label](const ValueReader &v) {
            PackedBits out = std::apply(
                [&](const auto &...r) { return fn(field_arg(v, r)...); },
                refs);
            if (out.w.size() != (n + 63) / 64)
              throw std::runtime_error("advice '" + label + "': " +
                                       std::to_string(out.w.size()) +
                                       " packed words for " +
                                       std::to_string(n) + " bits");
            return std::move(out.w);
          };
      if constexpr (F::kCharacteristicTwo) {
        if (word_stored(n, deps.ids(), mb))
          return word_bits(nm, shape, deps.ids(), packed);
      }
      Node nd = base(Kind::kAdvice, nm, type_in<F, T>(), shape);
      nd.deps = deps.ids();
      nd.masked_by = mb.pad();
      NodeGen<F> gen;
      const F *pf = f_;
      // The elements in chunks under a runner (util/parallel.h).
      gen.eval = [pf, packed, n](const ValueReader &v) {
        const std::vector<uint64_t> b = packed(v);
        std::vector<Elt> out(n);
        const Elt zero = pf->zero(), one = pf->one();
        parallel::for_chunks(
            n, parallel::grain_for(n, parallel::kChunks),
            [&](size_t lo, size_t hi) {
              for (size_t i = lo; i < hi; ++i)
                out[i] = ct::select(ct::mask(b[i / 64] >> (i % 64)), one, zero);
            });
        return out;
      };
      return ref<T, Committed>(add_node(std::move(nd), std::move(gen)),
                               shape);
    } else if constexpr (kBytes) {
      const size_t n = shape.size();
      auto refs = deps.refs;
      const std::string label = nm;
      std::function<std::vector<uint8_t>(const ValueReader &)> bytes =
          [fn, refs, n, label](const ValueReader &v) {
            std::vector<uint8_t> out = std::apply(
                [&](const auto &...r) { return fn(field_arg(v, r)...); },
                refs);
            if (out.size() != n)
              throw std::runtime_error("advice '" + label + "': " +
                                       std::to_string(out.size()) +
                                       " outputs, the shape has " +
                                       std::to_string(n));
            return out;
          };
      if constexpr (F::kCharacteristicTwo) {
        if (word_stored(n, deps.ids(), mb))
          return word_bits(nm, shape, deps.ids(), bytes);
      }
      Node nd = base(Kind::kAdvice, nm, type_in<F, T>(), shape);
      nd.deps = deps.ids();
      nd.masked_by = mb.pad();
      NodeGen<F> gen;
      const F *pf = f_;
      gen.eval = [pf, bytes](const ValueReader &v) {
        const std::vector<uint8_t> b = bytes(v);
        std::vector<Elt> out(b.size());
        for (size_t i = 0; i < b.size(); ++i)
          out[i] = ct::bit_elt(*pf, b[i]);
        return out;
      };
      return ref<T, Committed>(add_node(std::move(nd), std::move(gen)),
                               shape);
    } else {
      if constexpr (is_bit_v<T> && F::kCharacteristicTwo) {
        if (word_stored(shape.size(), deps.ids(), mb))
          return word_bits(nm, shape, deps.ids(),
                           make_generator(nm, shape, deps, std::move(fn)));
      }
      Node nd = base(Kind::kAdvice, nm, type_in<F, T>(), shape);
      nd.deps = deps.ids();
      nd.masked_by = mb.pad();
      NodeGen<F> gen;
      gen.eval = make_generator(nm, shape, deps, std::move(fn));
      return ref<T, Committed>(add_node(std::move(nd), std::move(gen)),
                               shape);
    }
  }
  // Whether a computed Bit value of N coordinates over the nodes DEPS is
  // stored as the designated subfield's words: in characteristic 2 with
  // bit packing and a 16-bit subfield, for whole words of a value no
  // challenge precedes (phase 0, so a bit view may read it) and no
  // declared pad masks. A Bit cell of the packed run is a circuit input
  // per bit, which the circuit's input layer and the bit stage pay for
  // whether or not a circuit constraint reads it; a word is one input, and
  // a bit view gives wires only to the words a circuit or an affine row
  // reads (aliased onto them). Batches read either form's bits.
  bool word_stored(size_t n, const std::vector<size_t> &deps,
                   const MaskedBy &mb) const {
    if constexpr (!F::kCharacteristicTwo || F::kSubFieldBits != 16) {
      return false;
    } else {
      if (!has_subfield || !compiler::relative_packing<F>() ||
          no_bit_packing || n == 0 || n % 16 != 0 || mb.pad() >= 0)
        return false;
      for (size_t d : deps)
        if (after_challenge(d)) return false;
      return true;
    }
  }
  // Whether node ID is a challenge or computed from one (memoized over the
  // graph, whose nodes only read earlier ones).
  bool after_challenge(size_t id) const {
    const auto &N = g_->nodes;
    for (size_t x = chal_memo_.size(); x < N.size(); ++x) {
      bool c = N[x].kind == Kind::kChallenge;
      for (size_t d : N[x].deps) c = c || (d < x && chal_memo_[d]);
      chal_memo_.push_back(c ? 1 : 0);
    }
    return chal_memo_.at(id) != 0;
  }
  // A computed Bit value NM of SHAPE stored as words (word_stored): the
  // words NM.words, each 16 bits of GEN's output (bit c the coefficient of
  // beta_c), and NM, their bit view, which the returned handle names.
  // GEN_BITS returns the bits as field elements, as bytes (0 or 1) or
  // packed, 64 to a uint64_t (BitProgram::run_packed).
  template <class Gen>
  Ref<F, Bit, Committed> word_bits(const std::string &nm, const Shape &shape,
                                   std::vector<size_t> deps, Gen gen_bits) {
    const size_t n = shape.size();
    Node wd = base(Kind::kAdvice, nm + ".words", type_in<F, Subfield<>>(),
                   Shape(n / 16));
    wd.deps = std::move(deps);
    NodeGen<F> wg;
    const F *pf = f_;
    // A word is the sum of the basis elements beta_c of its set bits; in
    // characteristic 2 a sum is the XOR of the elements' units, so each
    // word is a masked XOR of the basis' units, branch-free in the bits.
    using U = ct::unit_of<Elt>;
    constexpr size_t kUnits = ct::units_of<Elt>();
    std::array<std::array<U, kUnits>, 16> basis{};
    if constexpr (F::kCharacteristicTwo) {
      for (size_t c = 0; c < 16; ++c) {
        const Elt b = f_->beta(c);
        std::memcpy(basis[c].data(), &b, sizeof(Elt));
      }
      // The units' XOR is the field's sum.
      std::array<U, kUnits> s{};
      for (size_t i = 0; i < kUnits; ++i) s[i] = basis[1][i] ^ basis[2][i];
      Elt x;
      std::memcpy(&x, s.data(), sizeof(Elt));
      check(x == f_->addf(f_->beta(1), f_->beta(2)),
            "word storage: the field's sum is not the XOR of its units");
    }
    const auto packer = std::make_shared<const SubfieldWordPacker<Elt>>(basis);
    wg.eval = [pf, gen_bits, packer, n](const ValueReader &v) {
      const auto &b = gen_bits(v);
      using B = std::decay_t<decltype(b[0])>;
      const size_t nw = n / 16;
      std::vector<Elt> w(nw);
      // Groups G0 .. G1 - 1 of 64 bits (four words each) of the N bits
      // from SRC (GEN_BITS' output; packed when it is uint64_t) into the
      // words W, through BITS (unpacked output only). It captures nothing,
      // so a call with one range compiles as a plain loop.
      const auto pack_range = [](const auto *src, size_t n, size_t nw,
                                 const F *pf, const SubfieldWordPacker<Elt> &pk,
                                 uint64_t *bits, Elt *w, size_t g0,
                                 size_t g1) {
        using T = std::decay_t<decltype(src[0])>;
        const size_t q1 = std::min(nw, 4 * g1);
        if constexpr (std::is_same_v<T, uint64_t>) {
          // GEN_BITS' packed bits (BitProgram::run_packed, a HostStep).
          pk.pack(src + g0, q1 - 4 * g0, w + 4 * g0);
          return;
        } else if constexpr (std::is_same_v<T, Elt>) {
          // Element i is 1 when its units equal one's (ct::bit_of).
          const Elt one = pf->one();
          std::array<U, kUnits> o;
          std::memcpy(o.data(), &one, sizeof(Elt));
          for (size_t i0 = 64 * g0; i0 < n && i0 < 64 * g1; i0 += 64) {
            uint64_t word = 0;
            const size_t e = std::min(n, i0 + 64);
            for (size_t i = i0; i < e; ++i) {
              std::array<U, kUnits> u;
              std::memcpy(u.data(), &src[i], sizeof(Elt));
              uint64_t d = 0;
              for (size_t k = 0; k < kUnits; ++k) d |= uint64_t(u[k] ^ o[k]);
              word |= (ct::nonzero(d) ^ 1) << (i - i0);
            }
            bits[i0 / 64] = word;
          }
        } else {
          // 64 bits at a time in a register (a byte store could alias).
          for (size_t i0 = 64 * g0; i0 < n && i0 < 64 * g1; i0 += 64) {
            uint64_t word = 0;
            const size_t e = std::min(n, i0 + 64);
            for (size_t i = i0; i < e; ++i)
              word |= (uint64_t(src[i]) & 1) << (i - i0);
            bits[i0 / 64] = word;
          }
        }
        pk.pack(bits + g0, q1 - 4 * g0, w + 4 * g0);
      };
      // The groups in chunks of at least kMinGrain under a runner
      // (util/parallel.h), each chunk packing its own bits and words; a
      // smaller value runs as one call. The boundaries depend on N only.
      constexpr size_t kMinGrain = 512;
      const size_t ng = (n + 63) / 64;
      const size_t grain =
          std::max(parallel::grain_for(ng, parallel::kChunks), kMinGrain);
      // The unpacked bits in the calling thread's buffer, which a worker
      // reaches through BITS (a thread_local named in a chunk would be the
      // worker's own).
      static thread_local std::vector<uint64_t> buffer;
      uint64_t *bits = nullptr;
      if constexpr (!std::is_same_v<B, uint64_t>) {
        buffer.assign(ng, 0);
        bits = buffer.data();
      }
      const auto *src = b.data();
      if (ng <= grain) {
        pack_range(src, n, nw, pf, *packer, bits, w.data(), 0, ng);
      } else {
        Elt *const wd = w.data();
        const SubfieldWordPacker<Elt> &pk = *packer;
        parallel::for_chunks(ng, grain, [&](size_t g0, size_t g1) {
          pack_range(src, n, nw, pf, pk, bits, wd, g0, g1);
        });
      }
      return w;
    };
    const auto words = ref<Subfield<>, Committed>(
        add_node(std::move(wd), std::move(wg)), Shape(n / 16));
    const auto view = bits(nm, words);
    g_->nodes.at(view.id).shape = shape.dims;
    return ref<Bit, Committed>(view.id, shape);
  }
  // Over a data-dependent list of dependencies of this field: FN receives a
  // std::vector<const std::vector<Elt> *>, one per dependency.
  template <class T, class Fn>
  Ref<F, T, Committed> declare_advice(T, std::string nm, Shape shape,
                                      const std::vector<Ref<F>> &deps, Fn fn,
                                      MaskedBy mb = {}) {
    static_assert(is_value_type_v<T>,
                  "priv: the type is Bit, Subfield or Field");
    constexpr bool kSignature =
        std::is_invocable_r_v<std::vector<Elt>, Fn,
                              const std::vector<const std::vector<Elt> *> &>;
    static_assert(kSignature,
                  "priv over a list of dependencies: the closure must "
                  "take a const std::vector<const std::vector<Elt> *>&, one "
                  "pointer per dependency, and return std::vector<Elt> of "
                  "the value's field");
    Node nd = base(Kind::kAdvice, std::move(nm), type_in<F, T>(), shape);
    std::vector<size_t> ids;
    for (const auto &r : deps) ids.push_back(r.id);
    nd.deps = ids;
    nd.masked_by = mb.pad();
    NodeGen<F> gen;
    if constexpr (kSignature) {
      gen.eval = [ids, fn](const ValueReader &v) {
        std::vector<const std::vector<Elt> *> in;
        for (size_t id : ids) in.push_back(&v.template get<F>(id));
        return fn(in);
      };
    }
    return ref<T, Committed>(add_node(std::move(nd), std::move(gen)), shape);
  }

  // The public value NM equal to E, whose leaves are all public (statement
  // values, constants, public computations, challenges, public messages):
  // both parties evaluate it with the host emitter, outside the circuit
  // (compiler/public_expr.h). Its phase is the largest among its leaves.
  Ref<F, Field, Public> public_expr(std::string nm, const ExprPtr<F> &e) {
    const Shape shape(e->dims());
    Node nd;
    nd.kind = Kind::kPublicCompute;
    nd.name = std::move(nm);
    nd.field = field_id;
    nd.fobj = fobj;
    nd.n = shape.size();
    nd.shape = shape.dims;
    nd.deps = expr_deps(e);
    nd.expression = true;
    nd.origin = "expression";
    nd.challenge_degrees = challenge_coord_degrees(e, g_->nodes);
    put_str(nd.descr, "expression");
    describe_expr<F>(
        e, [this](const Lin<F> &l) { return describe_lin(l); }, nd.descr);
    NodeGen<F> gen;
    gen.eval = [e](const ValueReader &v) {
      return eval_expr(e, v);
    };
    const size_t id = add_node(std::move(nd), std::move(gen));
    pub_exprs_[id] = e;
    return ref<Field, Public>(id, shape);
  }

  // An advice value of type T equal to E, computed by the host emitter
  // (priv(e)'s value, without its predicate). It may be late.
  // STEP, when set, computes the value from its base's (HostStep).
  template <class T>
  Ref<F, T, Committed> expr_advice(T, std::string nm, const ExprPtr<F> &e,
                                   const HostStep<F> *step = nullptr) {
    static_assert(is_value_type_v<T>,
                  "priv(e): the type is Bit, Subfield or Field");
    if (e->f != f_) fail("priv '" + nm + "': an expression of another field");
    const Shape shape(e->dims());
    Node nd = base(Kind::kAdvice, std::move(nm), type_in<F, T>(), shape);
    nd.deps = expr_deps(e);
    NodeGen<F> gen;
    gen.eval = [e](const ValueReader &v) {
      return eval_expr(e, v);
    };
    // A Boolean function of bits, in characteristic 2: its word-level
    // program (bit_eval.h), which computes the same values and keeps them
    // packed for the programs that read this node.
    auto self = std::make_shared<size_t>(SIZE_MAX);
    if constexpr (F::kCharacteristicTwo) {
      auto prog = BitProgram<F>::compile(*f_, e, *g_);
      if (prog)
        gen.eval = [prog, self](const ValueReader &v) {
          return prog->run(v, *self);
        };
      // The packed bits of E's value, by E's program or by STEP's host
      // function from its base's program, kept under the node (and read
      // there: the host step writes them in place).
      std::function<const std::vector<uint64_t> &(const ValueReader &)> packed;
      if (prog)
        packed = [prog, self](const ValueReader &v)
            -> const std::vector<uint64_t> & {
          prog->run_packed(v, *self);
          return *v.packed_bits.find(*self);
        };
      if (prog && step != nullptr) {
        auto bprog = BitProgram<F>::compile(*f_, step->base, *g_);
        if (bprog) {
          const size_t nw = (shape.size() + 63) / 64;
          packed = [bprog, fn = step->fn, nw, self](const ValueReader &v)
              -> const std::vector<uint64_t> & {
            const uint64_t *in = bprog->run_in_place(v);
            std::vector<uint64_t> &out = v.packed_bits[*self];
            out.assign(nw, 0);
            fn(in, out.data());
            return out;
          };
          gen.eval = [packed, pf = f_, n = shape.size()](const ValueReader &v) {
            const std::vector<uint64_t> &r = packed(v);
            const Elt zero = pf->zero(), one = pf->one();
            std::vector<Elt> out;
            out.reserve(n);
            for (size_t i = 0; i < n; ++i)
              out.push_back(
                  ct::select(ct::mask(r[i / 64] >> (i % 64)), one, zero));
            return out;
          };
        }
      }
      // A Bit value of whole words is stored as its words and read through
      // its bit view, as a closure's is (word_stored); the program keeps
      // its packed bits under the view, which the programs reading it read.
      if constexpr (is_bit_v<T>) {
        if (word_stored(shape.size(), nd.deps, MaskedBy{})) {
          if (!prog) {
            const auto view = word_bits(nd.name, shape, nd.deps, gen.eval);
            *self = view.id;
            return view;
          }
          // The program's packed bits, which the words pack. A leaf that
          // is such a value's bit view the program reads from its packed
          // bits, which its words' program keeps: the value depends on the
          // words, and the view is computed only for its other readers.
          std::vector<size_t> deps;
          for (size_t d : nd.deps)
            deps.push_back(packed_views_.count(d) ? g_->nodes.at(d).deps.at(0)
                                                  : d);
          std::sort(deps.begin(), deps.end());
          deps.erase(std::unique(deps.begin(), deps.end()), deps.end());
          const auto view = word_bits(nd.name, shape, std::move(deps), packed);
          *self = view.id;
          packed_views_.insert(view.id);
          return view;
        }
      }
    }
    *self = add_node(std::move(nd), std::move(gen));
    return ref<T, Committed>(*self, shape);
  }

  // An advice value equal to E, computed by the host emitter (the value an
  // assert_range over a non-affine expression reads). It may be late.
  Ref<F, Subfield<>, Committed> expr_value(std::string nm,
                                           const ExprPtr<F> &e) {
    const Shape shape(e->dims());
    Node nd = base(Kind::kAdvice, std::move(nm), type_in<F, Subfield<>>(),
                   shape);
    nd.deps = expr_deps(e);
    NodeGen<F> gen;
    gen.eval = [e](const ValueReader &v) {
      return eval_expr(e, v);
    };
    return ref<Subfield<>, Committed>(add_node(std::move(nd), std::move(gen)),
                                      shape);
  }

  // A batch whose tables grow as it is used (keccak_batch): a slot in the
  // declaration order, named NM, that is a CompileError with MISSING until
  // set_batch declares its relation. The domain compiles the relation the
  // slot holds when it compiles.
  size_t reserve_batch(std::string nm, std::string missing) {
    batches_.push_back(
        BatchDecl{std::move(nm), {}, nullptr, 0, std::move(missing)});
    return batches_.size() - 1;
  }
  template <class R, class Map, class Sb>
  void set_batch(size_t slot, R r,
                 std::vector<Ref<F, Subfield<Sb>, Committed>> tables,
                 std::shared_ptr<const Map> map, unsigned width = 16) {
    BatchDecl &b = batches_.at(slot);
    b = batch_decl(r, b.name, std::move(tables), map, width);
  }
  // A handle on node ID (Lowering::ref_of).
  Ref<F> ref_of(size_t id) const {
    const Node &n = g_->nodes.at(id);
    return ref(id, n.shape.empty() ? Shape(n.n) : Shape(n.shape));
  }

  Predicate add_predicate(std::string nm, ExprPtr<F> e, bool truth,
                          std::shared_ptr<Placement> pin = nullptr) {
    const char *kind = truth ? "assert_true" : "assert_zero";
    if (e->f != f_)
      fail(std::string(kind) + " '" + nm + "' of domain " + name +
           " lies in another field");
    if (truth && !e->bit)
      fail(std::string(kind) + " '" + nm + "': the expression is not a Bit");
    const std::vector<size_t> deps = expr_deps(e);
    for (size_t id : deps)
      if (g_->nodes.at(id).domain >= 0 && g_->nodes.at(id).domain != index)
        fail(std::string(kind) + " '" + nm + "' of domain " + name +
             " reads '" + g_->nodes.at(id).name + "' of another domain");
    if (pin == nullptr) pin = std::make_shared<Placement>(Placement::kAuto);
    const long k = static_cast<long>(preds_.size());
    preds_.push_back(PredDecl{nm, e, truth, pin});
    circuits_.push_back(CircuitDecl{nm, deps, nullptr, k});
    affine_.push_back(AffineDecl{nm, Lin<F>{}, k});
    return Predicate(pin);
  }

  RangeHandle<F> add_request(const Lin<F> &v, Bound n, Bound m, bool interval,
                             std::string nm) {
    if (v.f == nullptr || v.n == 0 || v.terms.empty())
      fail("assert_range: an empty expression");
    if (nm.empty()) nm = "r" + std::to_string(requests_.size());
    if (n < 1) fail("assert_range '" + nm + "': the bound n is 0");
    if (m < n)
      fail("assert_range '" + nm + "': the interval [" + bound_str(n) + ", " +
           bound_str(m) + "] is empty");
    for (const auto &t : v.terms)
      if (g_->nodes.at(t.node).domain >= 0 &&
          g_->nodes.at(t.node).domain != index)
        fail("assert_range '" + nm + "' of domain " + name + " reads '" +
             g_->nodes.at(t.node).name + "' of another domain");
    RangeRequest<F> r;
    r.v = v;
    r.n = n;
    r.m = m;
    r.interval = interval;
    r.name = std::move(nm);
    auto cap = r.max_table;
    requests_.push_back(std::move(r));
    return RangeHandle<F>{index, requests_.size() - 1, cap};
  }

  // Lowering::bind_view: X has no cell; constraints read VIEW in its place.
  void bind_view(Ref<F> x, const Lin<F> &view, std::string note) {
    if (bound_.count(x.id))
      fail("'" + g_->nodes.at(x.id).name + "' is bound twice");
    if (view.n != x.n) fail("bind_view: the view's length differs");
    bound_[x.id] = view;
    bound_note_[x.id] = std::move(note);
  }

  // A committed phase-0 copy of the pad P through the declared map MAP,
  // whose value the core computes (Lowering::pad_copy). P may belong to
  // another domain (the MAC blind B of H, copied into A as bits).
  template <class FS, class T, class P>
  Ref<F, AnyType, Committed> pad_copy(std::string nm, Ref<FS, T, P> p,
                                      const PadMap<FS, F> &map) {
    const size_t n = map.out_n(p.n);
    Node nd = base(Kind::kPadCopy, std::move(nm), map.type(), n);
    nd.deps = {p.id};
    nd.copy_keeps_space = map.keeps_space();
    nd.copy_same_field = map.same_field();
    put_str(nd.descr, map.name());
    put_u64(nd.descr, map.params().size());
    nd.descr.insert(nd.descr.end(), map.params().begin(), map.params().end());
    const size_t pid = p.id;
    NodeGen<F> gen;
    gen.eval = [map, pid](const ValueReader &v) {
      return map(v.template get<FS>(pid));
    };
    return ref<AnyType, Committed>(add_node(std::move(nd), std::move(gen)), n);
  }

  template <class Fn, size_t... I>
  static void call(const Fn &fn, const CLogic &lc, const std::vector<Wires> &w,
                   const std::vector<std::vector<size_t>> &dims,
                   std::index_sequence<I...>) {
    fn(lc, Tensor<size_t>(w[I], dims[I])...);
  }

  Node base(Kind k, std::string nm, Type t, const Shape &shape) const {
    Node nd;
    nd.kind = k;
    nd.name = std::move(nm);
    nd.domain = index;
    nd.field = field_id;
    nd.fobj = fobj;
    nd.n = shape.size();
    nd.type = t;
    nd.shape = shape.dims;
    return nd;
  }
  template <class T = AnyType, class P = AnyPlace>
  Ref<F, T, P> ref(size_t id, const Shape &shape) const {
    return Ref<F, T, P>{id, shape.size(), f_, g_, shape.dims};
  }

  // The compile cache's description of the declarations the domain's
  // compiler reads beyond the graph's nodes (compiler/compile_cache.h), in
  // declaration order: circuit constraints (a closure by the key its
  // lowering gave), predicates with their expressions and pins, affine
  // rows, quadratic triples, batched relations, derived and expression
  // values, wiring and bit views, bindings, Boolean checks and range
  // requests. Returns "" or, for a closure without a key, why the domain
  // cannot be cached.
  std::string describe_declarations(std::vector<uint8_t> &out) const {
    std::string uncacheable;
    auto put_expr = [this, &out](const ExprPtr<F> &e) {
      describe_expr<F>(
          e, [this](const Lin<F> &l) { return describe_lin(l); }, out);
    };
    auto put_lin = [this, &out](const Lin<F> &e) {
      const auto d = describe_lin(e);
      put_u64(out, d.size());
      out.insert(out.end(), d.begin(), d.end());
    };
    auto put_ids = [&out](const std::vector<size_t> &v) {
      put_u64(out, v.size());
      for (size_t x : v) put_u64(out, x);
    };
    put_u64(out, circuits_.size());
    for (const auto &c : circuits_) {
      put_str(out, c.name);
      put_ids(c.reads);
      put_u64(out, uint64_t(c.pred + 1));
      put_u64(out, c.emit ? 1 : 0);
      if (c.emit && !c.key && uncacheable.empty())
        uncacheable = "the circuit constraint '" + c.name + "' of domain " +
                      this->name + " is a closure without a key";
      if (c.key) put_str(out, std::string(c.key->begin(), c.key->end()));
    }
    put_u64(out, preds_.size());
    for (const auto &p : preds_) {
      put_str(out, p.name);
      put_u64(out, p.truth ? 1 : 0);
      put_u64(out, uint64_t(p.pin ? *p.pin : Placement::kAuto));
      put_expr(p.e);
    }
    put_u64(out, affine_.size());
    for (const auto &a : affine_) {
      put_str(out, a.name);
      put_u64(out, uint64_t(a.pred + 1));
      put_lin(a.e);
    }
    put_u64(out, quads_.size());
    for (const auto &q : quads_) put_ids({q.a, q.b, q.c});
    put_u64(out, batches_.size());
    for (const auto &b : batches_) {
      put_str(out, b.name);
      put_ids(b.tables);
      put_u64(out, b.width);
      put_str(out, b.missing);
      put_u64(out, b.ops ? 1 : 0);
      if (b.ops) b.ops->describe(out, b.width);
    }
    put_u64(out, lins_.size());
    for (const auto &[id, e] : lins_) {
      put_u64(out, id);
      put_lin(e);
    }
    put_u64(out, exprs_.size());
    for (const auto &[id, e] : exprs_) {
      put_u64(out, id);
      put_expr(e);
    }
    put_u64(out, pub_exprs_.size());
    for (const auto &[id, e] : pub_exprs_) {
      put_u64(out, id);
      put_expr(e);
    }
    put_ids(checked_derived_);
    put_u64(out, uint64_t(bit_pin_));
    put_ids(unchecked_bits_);
    put_u64(out, views_.size());
    for (const auto &[id, words] : views_) {
      put_u64(out, id);
      put_ids(words);
    }
    put_u64(out, wiring_.size());
    for (const auto &[id, src] : wiring_) {
      put_u64(out, id);
      put_u64(out, src.size());
      for (const auto &[node, k] : src) {
        put_u64(out, node);
        put_u64(out, k);
      }
    }
    put_u64(out, bound_.size());
    for (const auto &[id, e] : bound_) {
      put_u64(out, id);
      put_lin(e);
    }
    put_u64(out, requests_.size());
    for (const auto &r : requests_) {
      put_str(out, r.name);
      put_lin(r.v);
      put_bound(out, r.n);
      put_bound(out, r.m);
      put_u64(out, (r.interval ? 1 : 0) | (r.implied_only ? 2 : 0) |
                       (r.slack ? 4 : 0) | (r.lowered ? 8 : 0));
      put_bound(out, r.max_table ? *r.max_table : 0);
      put_u64(out, uint64_t(r.realization.kind));
      put_bound(out, r.realization.table);
      put_u64(out, r.realization.k);
      put_bound(out, r.realization.established);
    }
    put_bound(out, max_table_);
    return uncacheable;
  }

  std::vector<uint8_t> describe_lin(const Lin<F> &e) const {
    std::vector<uint8_t> out;
    put_u64(out, e.n);
    put_u64(out, e.terms.size());
    for (const auto &t : e.terms) {
      uint8_t b[F::kBytes];
      f_->to_bytes_field(b, t.scale);
      out.insert(out.end(), b, b + F::kBytes);
      put_u64(out, t.node);
      put_u64(out, t.chain.size());
      for (const auto &op : t.chain) {
        put_str(out, op->name);
        put_u64(out, op->rows);
        put_u64(out, op->cols);
        put_u64(out, op->params.size());
        out.insert(out.end(), op->params.begin(), op->params.end());
        put_u64(out, op->deps.size());
        for (size_t d : op->deps) put_u64(out, d);
      }
    }
    return out;
  }

  // A dependency's argument: a Tensor of a value's elements (field form),
  // of its canonical integers (nat form), or a host input's bytes.
  // A host input or a Bytes statement: the closure receives its bytes.
  template <class R>
  static constexpr bool kHost = IsBytesArg<R>::value;
  template <class R, class = void>
  struct DepElt {
    using type = uint8_t;
  };
  template <class R>
  struct DepElt<R, std::enable_if_t<kIsValueDep<R>>> {
    using type = typename R::field_type::Elt;
  };
  template <class R>
  using VecArg = std::conditional_t<kHost<R>, std::vector<uint8_t>,
                                    Tensor<typename DepElt<R>::type>>;
  // Whether a depends_on entry lies in one of the system's fields, and in
  // odd characteristic: a host input has no field, so it passes both
  // without naming R::field_type.
  template <class R, class = void>
  struct DepField {
    static constexpr bool kInSystem = true, kOdd = true;
  };
  template <class R>
  struct DepField<R, std::enable_if_t<kIsValueDep<R>>> {
    using G = typename R::field_type;
    static constexpr bool kInSystem = true;
    static constexpr bool kOdd = !G::kCharacteristicTwo;
  };

  // Whether FN takes field elements: one per depends_on entry (elementwise)
  // or one Tensor per entry (vector).
  template <class Fn, class... R>
  static constexpr bool kFieldForm =
      (!(kHost<R> || ...) &&
       std::is_invocable_r_v<Elt, const Fn &,
                             const typename DepElt<R>::type &...>) ||
      std::is_invocable_r_v<std::vector<Elt>, const Fn &, const VecArg<R> &...>;

  // The generator of a closure over canonical integers (nat(...), or a
  // closure whose parameters are integers): NatInt when FN reads NatInt,
  // uint64_t otherwise.
  template <class... R, class Fn>
  std::function<std::vector<Elt>(const ValueReader &)> nat_generator(
      const std::string &nm, const Shape &shape, const Deps<R...> &deps,
      Fn inner) {
    using I0 = nat_internal::Integer<Fn, R...>;
    using I = std::conditional_t<std::is_void_v<I0>, NatInt, I0>;
    static_assert(!F::kCharacteristicTwo && (DepField<R>::kOdd && ...),
                  "advice over integers: canonical integers exist in odd "
                  "characteristic only");
    static_assert(!std::is_void_v<I0>,
                  "advice over integers: the closure must take one integer "
                  "(NatInt or uint64_t) per depends_on entry and return one "
                  "(elementwise), or take one Tensor of them (or const "
                  "std::vector&; a host input as const std::vector<uint8_t>&) "
                  "per entry and return a std::vector of them");
    constexpr bool kElementwise = nat_internal::kElementwise<I, Fn, R...>;
    const size_t n = shape.size();
    std::vector<std::vector<size_t>> maps;
    auto refs = deps.refs;
    const std::string label = nm;
    const F *pf = f_;
    // Outputs are checked below p.
    const Bound p = field_characteristic(*f_);
    if constexpr (std::is_same_v<I, uint64_t>) {
      if (p > (Bound(1) << 64))
        fail("advice '" + nm + "': uint64_t integers hold no canonical "
             "integer of a field of characteristic above 2^64; take NatInt");
    }
    if constexpr (kElementwise)
      std::apply(
          [&](const auto &...r) {
            (maps.push_back(broadcast_map(shape.dims, r.dims(),
                                          "advice '" + nm + "'")),
             ...);
          },
          refs);
    return [inner, refs, maps, pf, p, n, label](const ValueReader &v) {
      // Each dependency as integers (owned), or its bytes.
      size_t k = 0;
      auto in = std::apply(
          [&](const auto &...r) {
            return std::make_tuple(nat_input<I>(v, r, label, k++)...);
          },
          refs);
      std::vector<I> out;
      if constexpr (kElementwise) {
        out.resize(n);
        for (size_t i = 0; i < n; ++i)
          out[i] = nat_at(inner, in, maps, i, std::index_sequence_for<R...>{});
      } else {
        out = std::apply(
            [&](const auto &...x) { return inner(nat_arg(x)...); }, in);
      }
      if (out.size() != n)
        throw std::runtime_error("advice '" + label + "': " +
                                 std::to_string(out.size()) +
                                 " outputs, the shape has " +
                                 std::to_string(n));
      return elements(*pf, p, out, label);
    };
  }

  // The generator of a declaration (advice).
  template <class... R, class Fn>
  std::function<std::vector<Elt>(const ValueReader &)> make_generator(
      const std::string &nm, const Shape &shape, const Deps<R...> &deps,
      Fn fn) {
    static_assert((DepField<R>::kInSystem && ...),
        "advice: a depends_on entry lies in a field that is not one of the "
        "system's fields");
    const size_t n = shape.size();
    std::vector<std::vector<size_t>> maps;
    auto refs = deps.refs;
    const std::string label = nm;
    if constexpr (IsNat<Fn>::value) {
      return nat_generator(nm, shape, deps, fn.fn);
    } else if constexpr (!kFieldForm<Fn, R...> &&
                         !std::is_void_v<nat_internal::Integer<Fn, R...>>) {
      // Integer parameters: the nat form, without the wrapper.
      return nat_generator(nm, shape, deps, std::move(fn));
    } else {
      constexpr bool kElementwise =
          !(kHost<R> || ...) &&
          std::is_invocable_r_v<Elt, const Fn &,
                                const typename DepElt<R>::type &...>;
      constexpr bool kVector = std::is_invocable_r_v<std::vector<Elt>,
                                                     const Fn &,
                                                     const VecArg<R> &...>;
      static_assert(kElementwise || kVector,
                    "advice: the closure must take one Tensor (or const "
                    "std::vector<Elt>&; a host input as const "
                    "std::vector<uint8_t>&) per depends_on entry, in order, "
                    "each in that entry's field, and return std::vector<Elt> "
                    "of the value's field; or one element per entry and "
                    "return an element (elementwise); or the same over "
                    "canonical integers (NatInt or uint64_t; Tensor<NatInt>, "
                    "Tensor<uint64_t> or const std::vector& of them)");
      if constexpr (kElementwise)
        std::apply(
            [&](const auto &...r) {
              (maps.push_back(broadcast_map(shape.dims, r.dims(),
                                            "advice '" + nm + "'")),
               ...);
            },
            refs);
      return [fn, refs, maps, n, label](const ValueReader &v) {
        std::vector<Elt> out;
        if constexpr (kElementwise) {
          out.resize(n);
          for (size_t i = 0; i < n; ++i)
            out[i] = field_at(fn, v, refs, maps, i,
                              std::index_sequence_for<R...>{});
        } else {
          out = std::apply(
              [&](const auto &...r) { return fn(field_arg(v, r)...); }, refs);
        }
        if (out.size() != n)
          throw std::runtime_error("advice '" + label + "': " +
                                   std::to_string(out.size()) +
                                   " outputs, the shape has " +
                                   std::to_string(n));
        return out;
      };
    }
  }
  static size_t at(const std::vector<size_t> &map, size_t i) {
    return map.empty() ? i : map[i];
  }
  template <class Fn, class Tup, size_t... I>
  static auto nat_at(const Fn &fn, const Tup &in,
                     const std::vector<std::vector<size_t>> &maps, size_t i,
                     std::index_sequence<I...>) {
    return fn(std::get<I>(in).first[at(maps[I], i)]...);
  }
  template <class Fn, class Tup, size_t... I>
  static Elt field_at(const Fn &fn, const ValueReader &v, const Tup &refs,
                      const std::vector<std::vector<size_t>> &maps, size_t i,
                      std::index_sequence<I...>) {
    return fn(dep_values(v, std::get<I>(refs))[at(maps[I], i)]...);
  }
  template <class R>
  static decltype(auto) field_arg(const ValueReader &v, const R &r) {
    if constexpr (kHost<R>) {
      return dep_bytes(v, r);
    } else {
      return Tensor<typename R::field_type::Elt>(dep_values(v, r), r.dims());
    }
  }
  // A nat-form dependency: (integers of type I, dims), or a pointer to host
  // bytes.
  template <class I, class R>
  static auto nat_input(const ValueReader &v, const R &r,
                        const std::string &label, size_t k) {
    if constexpr (kHost<R>) {
      return std::make_pair(std::vector<uint8_t>(dep_bytes(v, r)),
                            std::vector<size_t>{});
    } else {
      std::vector<NatInt> x = integers(*r.f, dep_values(v, r), label, k);
      if constexpr (std::is_same_v<I, NatInt>) {
        return std::make_pair(std::move(x), r.dims());
      } else {
        return std::make_pair(std::vector<I>(x.begin(), x.end()), r.dims());
      }
    }
  }
  template <class I>
  static Tensor<I> nat_arg(
      const std::pair<std::vector<I>, std::vector<size_t>> &x) {
    return Tensor<I>(x.first, x.second);
  }
  static const std::vector<uint8_t> &nat_arg(
      const std::pair<std::vector<uint8_t>, std::vector<size_t>> &x) {
    return x.first;
  }

  enum DerivedBit : uint8_t { kPlain = 0, kCheckedBit = 1, kUncheckedBit = 2 };
  template <class T>
  Ref<F, T, Committed> derived(std::string nm, const Lin<F> &e,
                               DerivedBit bit) {
    Node nd = base(Kind::kDerived, std::move(nm), type_in<F, T>(), Shape(e.dims()));
    nd.deps = e.deps();
    nd.descr = describe_lin(e);
    // The Boolean check enters the description.
    if (bit != kPlain) put_u64(nd.descr, bit);
    NodeGen<F> gen;
    gen.eval = [e](const ValueReader &v) {
      return eval_lin(e, v);
    };
    const size_t id = add_node(std::move(nd), std::move(gen));
    lins_[id] = e;
    if (bit == kCheckedBit) checked_derived_.push_back(id);
    if (bit == kUncheckedBit) unchecked_bits_.push_back(id);
    return ref<T, Committed>(id, Shape(e.dims()));
  }

  // A derived view whose coordinate i is SRC[i] = (node, index), or zero
  // for kZeroCoordinate: the Lin sum over its source nodes of
  // Gather(node)(node), and a generator that copies. A source that is itself
  // a wiring view is read through to its own sources, so chained views
  // never nest. Its type is the parts' common type (Bit, Subfield), Field
  // otherwise.
  Ref<F> wiring(std::string nm, std::vector<std::pair<size_t, size_t>> src) {
    if (src.empty()) fail("view '" + nm + "' has no coordinates");
    for (auto &[id, k] : src) {
      if (id == kZeroCoordinate) continue;
      auto w = wiring_.find(id);
      if (w != wiring_.end()) std::tie(id, k) = w->second.at(k);
    }
    std::vector<size_t> order;
    std::map<size_t, std::vector<size_t>> idx;
    std::optional<Base> common;
    bool mixed = false;
    for (size_t i = 0; i < src.size(); ++i) {
      const size_t id = src[i].first;
      if (id == kZeroCoordinate) continue;
      const Node &p = g_->nodes.at(id);
      if (p.domain != index || p.fobj != fobj)
        fail("view '" + nm + "' reads '" + p.name +
             "', which is not a value of domain " + name);
      if (common && *common != p.type.base) mixed = true;
      common = p.type.base;
      auto it = idx.find(id);
      if (it == idx.end()) {
        order.push_back(id);
        it = idx.emplace(id, std::vector<size_t>(src.size(), kGatherNone))
                 .first;
      }
      it->second[i] = src[i].second;
    }
    if (order.empty()) fail("view '" + nm + "' reads no value");
    Lin<F> e;
    for (size_t id : order) {
      const Lin<F> t =
          Gather(*f_, idx.at(id), g_->nodes.at(id).n)(ref_of(id));
      e = e.terms.empty() ? t : e + t;
    }
    const Type type =
        !mixed && (*common == Base::kBit || *common == Base::kSubfield)
            ? Type{*common}
            : Type{Base::kField};
    Node nd = base(Kind::kDerived, std::move(nm), type, src.size());
    nd.deps = e.deps();
    nd.descr = describe_lin(e);
    NodeGen<F> gen;
    const F *pf = f_;
    // Each source node is looked up once per run of coordinates it fills.
    gen.eval = [src, pf](const ValueReader &v) {
      std::vector<Elt> out(src.size());
      size_t last = kZeroCoordinate;
      const std::vector<Elt> *x = nullptr;
      for (size_t i = 0; i < src.size(); ++i) {
        const size_t id = src[i].first;
        if (id == kZeroCoordinate) {
          out[i] = pf->zero();
          continue;
        }
        if (id != last) {
          x = &v.template get<F>(id);
          last = id;
        }
        out[i] = x->at(src[i].second);
      }
      return out;
    };
    const size_t id = add_node(std::move(nd), std::move(gen));
    lins_[id] = e;
    wiring_[id] = std::move(src);
    return ref(id, e.n);
  }

  Graph *g_;
  SystemCore *sys_;
  const F *f_;
  std::vector<CircuitDecl> circuits_;
  std::vector<AffineDecl> affine_;
  std::vector<PredDecl> preds_;
  std::vector<QuadDecl> quads_;
  std::vector<BatchDecl> batches_;
  std::map<size_t, Lin<F>> lins_;
  // Derived values defined by an expression (bit_from_unchecked over a
  // non-affine expression): circuits only.
  std::map<size_t, ExprPtr<F>> exprs_;
  // Public values defined by an expression (public_expr), by node.
  std::map<size_t, ExprPtr<F>> pub_exprs_;
  std::vector<size_t> checked_derived_;  // derive(Bit{}): x (x - 1) = 0
  Placement bit_pin_ = Placement::kAuto;  // pin_bit_checks
  std::vector<size_t> unchecked_bits_;   // bit_from_unchecked
  std::map<size_t, std::vector<size_t>> views_;  // bit view -> its words
  // after_challenge's memo, by node id.
  mutable std::vector<uint8_t> chal_memo_;
  // The bit views of priv(e) values stored as words whose words a program
  // fills, keeping its packed bits under the view (expr_advice).
  std::set<size_t> packed_views_;
  // Wiring views (concat, gather): each coordinate's (node, index).
  std::map<size_t, std::vector<std::pair<size_t, size_t>>> wiring_;
  std::vector<RangeRequest<F>> requests_;
  std::map<size_t, Lin<F>> bound_;            // bound node -> its view
  std::map<size_t, std::string> bound_note_;  // report line of a binding
  std::vector<RangeTableStats> range_tables_;
  // The domain's LogUp challenge alpha:<D>, which the assert_in and range
  // lowerings share: declared by
  // the first of them, and T_max, the range tables' bound its excluded set
  // reads (0 until the range lowering sets it).
  std::optional<Ref<F, Field, Public>> logup_alpha_;
  std::shared_ptr<Bound> logup_tmax_ = std::make_shared<Bound>(0);
  Bound max_table_ = 0;
  // Each costed predicate's circuit cost (quad terms, layers), by its
  // expression and assert_true flag: a system compiled again (a bench
  // compiles its relation, then its system) costs no predicate twice
  // (compiler/compiled_domain.h, place_predicates).
  mutable std::map<std::pair<const ExprNode<F> *, bool>,
                   std::pair<size_t, size_t>>
      pred_terms_;
};

template <class F, class RSF, class S>
class DomainImpl;

// A domain's generator GEN as the system of field set S runs it: each
// closure's elements wrapped in S::Value, an empty closure left empty.
template <class S, class F>
Generator<S> wrap_generator(NodeGen<F> gen) {
  Generator<S> g;
  if (gen.eval)
    g.eval = [e = std::move(gen.eval)](const ValueStore<S> &v) {
      return S::template wrap<F>(e(v));
    };
  if (gen.sample)
    g.sample = [s = std::move(gen.sample)](RandomEngine &rng,
                                           const ValueStore<S> &v) {
      return S::template wrap<F>(s(rng, v));
    };
  if (gen.accepts)
    g.accepts = [a = std::move(gen.accepts)](const typename S::Value &v) {
      return a(S::template get<F>(v));
    };
  g.accepts_bytes = std::move(gen.accepts_bytes);
  return g;
}

// The domain of field F in a system of field set S, with its profile's
// Reed-Solomon factory RSF and Ligero parameters: the implementation
// ConstraintSystem::domain creates, which compiles the domain.
template <class F, class RSF, class S>
class DomainImpl final : public Domain<F>, public DomainBase<S> {
 public:
  using Hash = typename S::Hash;
  static_assert(S::template kListed<F>,
                "a domain's field is one of the system's fields: list its "
                "type in System<Fields...>");
  DomainImpl(BasicGraph<S> *g, SystemCore *sys,
             const DomainProfile<F, RSF, Hash> &p, std::string nm, int idx)
      : Domain<F>(g, sys, p.f, std::move(nm), idx, S::template index<F>(),
                  p.has_subfield, p.prime),
        bg_(g),
        p_(p) {
    this->no_bit_packing = p.no_bit_packing;
  }

  const DomainProfile<F, RSF, Hash> &profile() const { return p_; }
  std::string field_name() const override { return p_.field_name; }
  const compiler::PlacementRates &rates() const override { return p_.rates; }

  std::unique_ptr<CompiledDomainBase<S>> compile(
      const CompilePlan &plan, const DomainSource *source) const override;
  std::string describe_key(std::vector<uint8_t> &out) const override {
    put_str(out, this->name);
    put_u64(out, uint64_t(this->index + 1));
    put_u64(out, this->field_id);
    const auto id = FieldValues<F>::identity(*p_.f);
    put_u64(out, id.size());
    out.insert(out.end(), id.begin(), id.end());
    put_str(out, p_.field_name);
    put_u64(out, p_.rate);
    put_u64(out, p_.nreq);
    put_u64(out, p_.list_radius ? 1 : 0);
    put_u64(out, p_.t);
    put_u64(out, uint64_t(p_.masking));
    put_u64(out, p_.block_enc ? 1 : 0);
    // The Ligero chooser's inputs (compiler/ligero_choice.h): the target,
    // the block grid and its cap; its outputs (block_enc, t, the masking)
    // are computed again on a hit and checked through the system digest.
    // The target's whole bits, and its half bits when it has a half.
    put_u64(out, p_.target_half() / 2);
    if (p_.target_half() % 2 != 0) {
      put_str(out, "ligero.target_half_bits");
      put_u64(out, p_.target_half());
    }
    put_u64(out, uint64_t(p_.block_grid));
    put_u64(out, p_.max_block_enc);
    if (p_.block_enc_fixed != 0) {
      put_str(out, "ligero.block_enc_fixed");
      put_u64(out, p_.block_enc_fixed);
    }
    put_u64(out, p_.has_subfield ? 1 : 0);
    put_u64(out, uint64_t(p_.prime));
    put_u64(out, p_.d_max);
    put_u64(out, p_.unpacked_s0 ? 1 : 0);
    if (p_.no_skip) put_str(out, "batch.no_skip");
    if (!p_.bit_phase) put_str(out, "batch.no_bit_phase");
    if (p_.no_bit_packing) put_str(out, "no-bit-packing");
    // The placement rates as IEEE-754 bit patterns.
    auto put_double = [&out](double x) {
      uint64_t b;
      std::memcpy(&b, &x, sizeof(b));
      put_u64(out, b);
    };
    const compiler::PlacementRates &r = p_.rates;
    put_str(out, r.source);
    for (double x : {r.commit_full, r.commit_sub, r.gkr_term, r.triple,
                     r.triple_b, r.triple_row, r.triple_row_b,
                     r.triple_hash, r.triple_fixed, r.triple_fixed_b})
      put_double(x);
    put_u64(out, r.batch.size());
    for (const auto &b : r.batch) {
      put_u64(out, uint64_t(b.eval));
      for (double x : {b.fixed, b.mul, b.add, b.mac, b.lane_lookup,
                       b.lane_mul, b.lane_term, b.lin, b.map_mul, b.map_add,
                       b.map_mac, b.region})
        put_double(x);
    }
    put_u64(out, r.stage.chains.size());
    for (const auto &c : r.stage.chains) {
      put_u64(out, c.chain.size());
      for (size_t d : c.chain) put_u64(out, d);
      for (double x : {c.fixed_p, c.coord_p, c.other_p, c.fixed_v, c.coord_v,
                       c.other_v})
        put_double(x);
    }
    return this->describe_declarations(out);
  }
  void lower_ranges(compiler::ConstraintSystemBuilder<S> &b) override {
    compiler::lower_ranges(static_cast<Domain<F> &>(*this), b);
  }

 protected:
  size_t add_node(Node nd, NodeGen<F> gen) const override {
    return bg_->add(std::move(nd), wrap_generator<S>(std::move(gen)));
  }

 private:
  friend class compiler::CompiledDomain<F, RSF, S>;
  BasicGraph<S> *bg_;
  DomainProfile<F, RSF, Hash> p_;
};

}  // namespace proofs::gordiehowe

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_DOMAIN_H_
