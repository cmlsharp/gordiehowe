// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the realized program, one in-memory structure.
//
// ir::Program mirrors the Lean schema `GordieHowe.RealizedProgram`
// (formal/GordieHowe/Language/RealizedProgram.lean) element for element:
// fields, domains, values, the expression DAG with its shared entries,
// predicates with their targets and roles, lookup tables and their groups,
// challenges, messages, batches with their parts, GKR circuits with their
// entries and input layouts, and the realization circuits. The compiler's
// last stage builds it (program_builder.h); the backend's runtime objects
// are built from it (each check the verifier runs comes from one of its
// elements); the Lean export is its printer (program_printer.h); the
// compile cache stores it.
//
// Identifiers are positions in their lists, as in Lean: value v is
// values[v], predicate p is predicates[p], and so on. A field element is
// the natural of its C++ encoding, written in decimal (Nat).
//
// Expressions are nodes of one arena, Program::nodes, each a Lean `Expr`
// constructor whose operands are node ids. Program::exprs lists the shared
// entries (Lean `RealizedProgram.exprs`): entry k is the root node
// exprs[k], read elsewhere through a node of kind kRef with x = k. A node
// may be the operand of several nodes; the printer writes it inline each
// time, as Lean reads a tree. Index maps are interned in
// Program::index_maps (the Lean definitions idx<k>), coefficients and
// named operators in their own tables.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_REALIZED_PROGRAM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_REALIZED_PROGRAM_H_

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace proofs::gordiehowe::ir {

using Id = uint32_t;
inline constexpr Id kNone = ~Id(0);

// A natural number, in decimal (field elements, bounds, constants).
using Nat = std::string;

// ------------------------------------------------------------ fields --

struct FieldDecl {
  std::string name;
  Nat characteristic;
  size_t degree = 0;
  bool operator==(const FieldDecl &o) const {
    return name == o.name && characteristic == o.characteristic &&
           degree == o.degree;
  }
};

struct DomainDecl {
  std::string name;
  Id field = 0;
};

// A space of field elements (Lean `Space`): the whole field, or the
// packing-tree node NAME.
struct Space {
  bool full = true;
  std::string node;
};

// -------------------------------------------------------- expressions --

// A coefficient (Lean `Coef`): a constant, or coordinate I of value V.
struct Coef {
  bool is_const = true;
  Nat c;
  Id v = kNone;
  size_t i = 0;
};

// A named operator (Lean `NamedOp`). Value parameters (h, a, t, M, r, d,
// c) are value ids; field-element parameters (psi, base) naturals.
struct NamedOp {
  enum Kind : uint8_t {
    kNegacyclicConv,
    kPolyMatVec,
    kPolyBroadcast,
    kNtt,
    kInverseNtt,
    kNttTranspose,
    kRowDot,
    kMacConv,
    kAcyclicConv,
    kDiagonal,
    kScale,
    kConstDiagonal,
    kSum,
    kFromDigits,
    kBatched,
  };
  Kind kind = kSum;
  // The value parameter (h, a, t, M, r, d, c), kNone when the operator has
  // none.
  Id value = kNone;
  // Natural parameters in the Lean constructor's order, after the value
  // parameter: polyMatVec K L, polyBroadcast K, ntt n, inverseNtt n,
  // nttTranspose n, rowDot R W, macConv w nch, acyclicConv lx, sum w,
  // fromDigits k, batched b.
  std::vector<size_t> nats;
  // A transform's root psi, or fromDigits' base.
  Nat elt;
  // A convolution's form: the coefficients, or the transform at PSI
  // (elt); ntt's order.
  bool ntt_form = false;
  bool natural_order = false;
  // macConv's taps.
  std::vector<size_t> taps;
  // batched's inner operator (an id in Program::ops).
  Id inner = kNone;
};

enum class LogicOp : uint8_t { kLt, kLeq, kEq, kAny, kAll };

// A node of the expression arena (Lean `Expr`).
struct Expr {
  enum Op : uint8_t {
    kLeaf,     // x: the value
    kAdd,      // a + b
    kSub,      // a - b
    kScale,    // x: the coefficient (Program::coefs), a: the operand
    kMul,      // a * b
    kReindex,  // x: the index map (Program::index_maps), a
    kConcat,   // a, then b
    kLinear,   // x: the rows (Program::linears), a
    kProd,     // x: n, a
    kMux,      // a b + (1 - a) c
    kApply,    // x: the operator (Program::ops), a
    kRef,      // x: the shared entry
    kLogic,    // logic: the builder, x: w, args
  };
  Op op = kLeaf;
  LogicOp logic = LogicOp::kLt;
  uint64_t x = 0;
  Id a = kNone, b = kNone, c = kNone;
  std::vector<Id> args;
  // The number of coordinates (Lean `Expr.len`).
  size_t n = 0;
};

// The sparse rows of a linear map: rows[j] = [(column, coefficient id)].
using LinearRows = std::vector<std::vector<std::pair<size_t, Id>>>;

// ------------------------------------------------------------- values --

enum class VType : uint8_t { kBit, kSub, kField };

// What a value or a predicate reads (Lean `Read`): the challenge, the late
// value, or the pad of a late value.
struct Read {
  enum Kind : uint8_t { kChal, kLate, kPad };
  Kind kind = kChal;
  Id id = 0;
  bool operator<(const Read &o) const {
    return kind != o.kind ? kind < o.kind : id < o.id;
  }
  bool operator==(const Read &o) const { return kind == o.kind && id == o.id; }
};

struct Value {
  // Lean `Kind` with `PubDef` folded in.
  enum Kind : uint8_t {
    kPriv,
    kInput,      // .pub .input
    kOpaque,     // .pub (.opaque opaque args)
    kPubExpr,    // .pub (.expr expr)
    kConstant,   // entries
    kChallenge,  // ref: the challenge
    kLate,
    kBits,       // ref: the words' value, select: the index map
    kPadCopy,    // ref: the late value (map "polynomialBits")
    kMessage,    // ref: the late value
    kBound,      // expr: its definition over the digits
  };
  std::string name;
  // The domain; a value of a field no domain commits has DOMAIN = kNone and
  // FIELD set.
  Id domain = 0;
  Id field = kNone;
  std::vector<size_t> shape;
  Kind kind = kPriv;
  VType type = VType::kField;
  // The subfield's name of a kSub type.
  std::string sub;
  size_t phase = 0;
  // The packing-tree node of a committed value (priv, bits, padCopy).
  std::string node;
  // Where the type is enforced: none, the node, or predicate type_pred.
  enum class TypeSource : uint8_t { kNone, kNode, kPred };
  TypeSource type_source = TypeSource::kNone;
  Id type_pred = kNone;
  // A late value's closed reads and pad space.
  std::vector<Read> reads;
  Space pad_space;
  // A public expression's degree in each challenge.
  std::vector<std::pair<Id, size_t>> degree;
  // A statement value's bound N (0: none), in decimal.
  Nat bound;
  // The role: source (owner = kNone), or the realization of predicate
  // OWNER.
  Id owner = kNone;
  // Kind payloads.
  std::string opaque;
  std::vector<Id> args;
  Id expr = kNone;
  std::vector<Nat> entries;
  Id ref = kNone;
  Id select = kNone;
  // The C++ node, kNone for a constant the builder added.
  Id cnode = kNone;
  // The values a public view's expression reads (the export test's).
  std::vector<Id> sources;
  // Why the structure has no description of the value's definition (""
  // when it has one); the printer refuses it.
  std::string unmodeled;
  size_t size() const {
    size_t s = 1;
    for (size_t x : shape) s *= x;
    return s;
  }
};

// --------------------------------------------------------- predicates --

// The target of a field equal (Lean `Target`): affine rows, the quadratic
// test, a batch, a GKR circuit, or realized by predicate ID (a source
// predicate that reads a spectrally realized convolution: its realized
// form, kRealized's predicate, is what the backend places).
struct Target {
  enum Kind : uint8_t { kAffine, kQuadratic, kBatch, kGkr, kRealized };
  Kind kind = kAffine;
  Id id = kNone;
};

enum class LookupKind : uint8_t {
  kDirect,
  kScaled,
  kShifted,
  kDigits,
  kTwoSided,
  kComplement
};

struct LookupRealization {
  Id table = 0, group = 0;
  LookupKind kind = LookupKind::kDirect;
  size_t digits = 0;
  Nat base;
  std::vector<Id> digit_values, second;
  std::vector<Id> needles;
  Nat honest, max;
};

// An in predicate's set is a range [0, n) in every program the compiler
// writes; its realization is lookups or an implied interval.
struct InRealization {
  bool implied = false;
  std::string lo, hi;  // signed decimal (implied)
  LookupRealization lookup;
};

enum class ModForm : uint8_t {
  kField,
  kConstant,
  kBit,
  kOneDigit,
  kDigits,
  kCommittedDigits,
  kGrouped,
  kInteger
};

struct GroupedMod {
  Nat base;
  size_t digit_count = 0;
  std::vector<std::pair<size_t, size_t>> groups;
  Nat group_bound;
  Id group_digits = kNone, residues = kNone;
  Id accumulators = kNone;
};

struct ModRealization {
  ModForm form = ModForm::kField;
  // The sides' intervals, written when HAS_INTERVAL (the integer form
  // always has them).
  bool has_interval = false;
  std::string lhs_lo, lhs_hi, rhs_lo, rhs_hi;
  std::string quotient_lo;
  Nat qmax;
  Id quotient = kNone;
  std::vector<Id> digits;
  Nat radix;
  // The in predicates bounding the quotient or its digits, with (n, N, m).
  std::vector<Id> ranges;
  std::vector<std::array<Nat, 3>> bounds;
  std::optional<GroupedMod> grouped;
  std::optional<Target> target;
  // The integer form's span.
  Nat span;
};

struct MacRealization {
  Id mac_field = 0, key = 0;
  Id blind = kNone, blind_x = kNone;
  Id tag = 0;
  Id h_predicate = kNone;
  size_t chunks = 0, width = 0;
  std::vector<Id> accumulators, quotient_digits;
};

// The declaration of the compiled system an element realizes, which the
// backend binds it to (not printed): a domain predicate (assert_zero,
// assert_true, assert_int_equal; INDEX its position in the domain's
// predicates), a lowering's affine row (in the domain's affine rows), a
// declared quadratic triple, the Boolean check of node INDEX, a range
// request, an assert_mod (in the mod equalities' records), or a MAC (its
// first record).
struct Origin {
  enum Kind : uint8_t {
    kNone,
    kDecl,
    kAffineRow,
    kQuad,
    kTypeCheck,
    kRange,
    kMod,
    kCross
  };
  Kind kind = kNone;
  Id domain = 0;
  uint64_t index = 0;
};

struct Predicate {
  enum Body : uint8_t { kEqual, kMem, kMod, kCross };
  std::string name;
  Body body = kEqual;
  // equal, mod, mem: the domain; cross: dx, with dy.
  Id domain = 0, dy = 0;
  // equal, mod: lhs, rhs; cross: x, y; mem: the record (lhs) and the
  // needles (rhs, not printed).
  Id lhs = kNone, rhs = kNone;
  Target target;
  // mem: the set, the range [0, N) (RANGE) or the entries of SET (an
  // expression, kNone for a range), and its realization.
  Nat range;
  Id set = kNone;
  InRealization in;
  // mod: q and the realization.
  Nat q;
  ModRealization mod;
  // cross: the width and the MAC.
  size_t width = 1;
  MacRealization mac;
  std::vector<Read> reads;
  std::vector<std::pair<Id, size_t>> degree;
  // The role: source, realization of OWNER, or type check of value OWNER.
  enum class Role : uint8_t { kSource, kRealization, kType };
  Role role = Role::kSource;
  Id owner = kNone;
  // The values its expressions read (the export test's), and an in
  // predicate's needles per coordinate and coordinates.
  std::vector<Id> values;
  size_t needles = 0, size = 0;
  Origin origin;
  // Why the structure has no description of the predicate's sides ("" when
  // it has one): the backend binds it by its origin and target, the
  // printer refuses it.
  std::string unmodeled;
};

// --------------------------------------------------- tables, challenges --

struct TableGroup {
  size_t capacity = 0;
  Id static_mult = kNone, late_mult = kNone;
  bool merged = false;
  // (pred, needle, first, count), in sum order.
  std::vector<std::array<size_t, 4>> members;
};

struct Table {
  std::string name;
  Id domain = 0;
  // The rows: .range size, or the coordinates of ROWS_EXPR (.expr).
  Nat size;
  Id rows_expr = kNone;
  Id alpha = 0;
  std::vector<TableGroup> groups;
};

struct Challenge {
  std::string name;
  Id field = 0;
  size_t phase = 0, size = 1;
  // The sampler: full, a packing-tree node, or the field minus [0, tmax).
  enum class Sampler : uint8_t { kFull, kNode, kMinusRange };
  Sampler sampler = Sampler::kFull;
  std::string node;
  Nat tmax;
  // The role: source, realization of OWNER, or unmodeled.
  enum class Role : uint8_t { kSource, kRealization, kUnmodeled };
  Role role = Role::kSource;
  Id owner = kNone;
};

struct Message {
  Id value = 0;
  Id domain = 0, field = kNone;
  size_t phase = 0, size = 0;
  Space space;
  bool subfield_message = false;
  std::string pad;
};

// ------------------------------------------------- batches and circuits --

struct Batch {
  std::string name;
  Id domain = 0;
  bool bit_operands = false;
  size_t degree = 0, instances = 0, width = 0, rounds = 0, pads = 0;
  bool bit_sumcheck = false;
  bool char2 = false;  // skipDomain gf256, else integers
  std::vector<Id> parts;
};

// A realization circuit (Lean `RealCircuit`) or input (`RealPub`).
struct RealRef {
  enum Kind : uint8_t { kLogup, kMacH, kWeights, kUnmodeled };
  Kind kind = kUnmodeled;
  Id a = 0, b = 0;
  // The C++ name.
  std::string name;
};

struct InputBlock {
  enum Kind : uint8_t {
    kPub,
    kRealizationPub,
    kCommitted,
    kPad,
    kView,
    kBatchPads,
    kFiller
  };
  Kind kind = kFiller;
  // The value (pub, committed, pad: the late value, view), or the batch.
  Id value = kNone;
  RealRef real;
  size_t at = 0, n = 0;
  std::string name;
};

struct CircuitEntry {
  enum Kind : uint8_t { kTypeCheck, kAlignment, kPred, kRealization };
  Kind kind = kPred;
  // typeCheck, pred: the predicate; alignment: the count.
  size_t id = 0;
  RealRef real;
};

struct Circuit {
  std::string name;
  Id domain = 0;
  std::vector<Id> predicates;
  std::vector<CircuitEntry> entries;
  std::vector<InputBlock> inputs;
  size_t public_inputs = 1, input_count = 1, layers = 0, wires = 0, terms = 0;
};

// ------------------------------------------------------------ program --

// A convolution realized spectrally (Lean `SpectralConv`, compiler/conv.h's
// batch form): the shared source conv(a, b) (SOURCE) and its reading
// INTT_M(z)[0, lc) (READ), the products predicate NTT(a) NTT(b) = z, the
// blocks, the operands' lengths, M and the root.
struct SpectralConv {
  Id source = 0, read = 0, products = 0;
  size_t blocks = 0, left = 0, right = 0, length = 0;
  Nat root;
};

struct MemberCheck {
  std::string member;
  size_t offset = 0, bytes = 0;
  std::string check;
  std::vector<uint64_t> args;
};

// What the backend builds a domain from beyond the program's elements (not
// printed): its choices with their reasons and costs, packing chains and
// Ligero parameters (DECISIONS, compiled_domain.h's realization record),
// and its GKR circuit as the scheduler returned it (CIRCUIT,
// compile_cache.h's circuit_record; empty without GKR). The placement of
// every predicate, the triples' operands, the batches' parts and widths and
// the Boolean checks' target are the program's own (its predicates'
// targets and its batches).
struct DomainRealization {
  std::vector<uint8_t> decisions;
  std::vector<uint8_t> circuit;
};

// A predicate's derivation (Lean `Derivation`, CERTIFYING_COMPILER.md):
// the steps by which the predicates its lowering wrote imply it, each step
// one rule (Lean `Step`) whose premises are earlier steps by index. The
// lowerings record them when they emit a realization (compiler/
// derivation.h); the builder resolves their names to ids.
//
// A step's expressions are entries of Certificates::exprs, which is not
// part of the program: a program node (the program's own text), a value's
// leaf, or a sum, difference, product or constant scaling of entries.
struct DExpr {
  enum Kind : uint8_t { kProgram, kLeaf, kAdd, kSub, kMul, kScale, kRef };
  Kind kind = kProgram;
  // kProgram: the node of Program::nodes; kLeaf: the value; kRef: the
  // shared entry.
  Id id = kNone;
  Id a = kNone, b = kNone;
  // kScale: the coefficient, a natural below the characteristic.
  Nat c;
  size_t n = 0;
};

struct DStep {
  enum Rule : uint8_t {
    kRealized,
    kSubst,
    kLinear,
    kLookup,
    kRangeNat,
    kHoldsIn,
    kSrc,
    kIvlNat,
    kIvlExpr,
    kIvlSolve,
    kIvlMeet,
    kNatIvl,
    kNatComp,
    kNatBool,
    kNatLin,
    kLiftConst,
    kFieldDvd,
    kGroupedMod,
    kIvlApply,
    kIvlLogic,
    kFact,
    kTransport,
    kLift,
    kDigits,
    kCongr,
    kMac,
    kLinop,
    kConclude,
    kHyp,
    kIvlDisjoint
  };
  // An interval source (Lean `IvlSrc`).
  enum Src : uint8_t { kConst, kDeclared, kNat, kPrime, kOpaqueBit, kQuadRoot, kRootSet, kShift };
  Rule rule = kConclude;
  // The domain the step reads in when not its predicate's (Lean inDom).
  Id in_dom = kNone;
  // Earlier steps, by index (kLinear: with COEFFS, signed decimals).
  std::vector<size_t> premises;
  std::vector<std::string> coeffs;
  // kRealized: the predicate; kSrc: the value, its source SRC with its
  // argument SRC_ARG (kDeclared: the entry of the value ranges, kNat: the
  // premise).
  Id id = kNone;
  Src src = kConst;
  size_t src_arg = 0;
  // kMac: the tails (predicate ids) and the H predicate (kNone: none);
  // kSrc kQuadRoot, kRootSet: the root predicates (quadRoot's one).
  std::vector<Id> tails;
  Id h = kNone;
  // kLookup: the members (table, group, member index), in order.
  std::vector<std::array<size_t, 3>> members;
  // The expressions (entries of Certificates::exprs): kSubst, kLinear e1
  // e2; kIvlExpr e; kIvlSolve a.
  std::vector<Id> exprs;
  // Signed decimals: kIvlExpr, kIvlSolve lo hi; kDigits T.
  std::vector<std::string> ints;
};

// The certificates of a program's Lean export (Lean `HonestCert`, the
// derivations), aligned with its lists: per predicate its MAC site (ROLES:
// 0, or 2 pid + 1 for the check over cross predicate pid's y field,
// 2 pid + 2 for its x field) and the digit lookups
// of a committed-digits mod_q (COMM_DIGITS); per value the lookup whose
// record a bound value is (BOUND_RECS). They are computed by the compiler
// from its lowerings' records at export time and are not part of the
// program: the compile cache does not store them.
// A shared fact (Lean `SharedEntry`): ivl DOM EXPR LO HI, stated by STEPS
// (their premises local to the entry) at rank RANK; a derivation cites it
// by `fact k`.
struct SharedFact {
  Id dom = 0;
  Id expr = kNone;
  std::string lo, hi;
  size_t rank = 0;
  std::vector<DStep> steps;
};

struct Certificates {
  // Per predicate, its derivation, and the expressions they read; and
  // why a predicate has none (a gap: "" when it has one).
  std::vector<std::vector<DStep>> derivations;
  std::vector<DExpr> exprs;
  std::vector<std::string> deriv_gaps;
  // Each predicate's rank (Lean `Derivations.ranks`): above the rank of
  // every predicate its derivation cites (hyp), a cross equal above every
  // other predicate.
  std::vector<size_t> deriv_ranks;
  // The derivations the check refused, by predicate (empty where none),
  // printed as comments for diagnosis.
  std::vector<std::vector<DStep>> deriv_refused;
  // The shared facts (Lean `Derivations.shared`) and their entries' order.
  std::vector<SharedFact> shared;
  std::vector<size_t> roles;
  std::vector<std::vector<Id>> comm_digits;
  std::vector<Id> bound_recs;
  // The honest checks' shared tables (Lean `HonestTables`): per predicate
  // the values it reads, sorted, each once (PRED_VALS); per value whether
  // its reads hold a late value (LATE_BAD) or a generated late value
  // (GEN_BAD); the digits of the two-sided and digit lookups in predicate
  // order (LOOKUP_OWNERS: the digit set SECOND, position IDX); the digits of
  // the digit lookups bounding a source committed-digits mod_q's quotient
  // digits, in lookup order (COMM_OWNERS: quotient digit J of MOD, position
  // K among lookup LK's digits).
  struct LookupDigit {
    Id value = 0, pid = 0;
    bool second = false;
    size_t idx = 0;
  };
  struct CommDigit {
    Id value = 0, mod = 0;
    size_t j = 0;
    Id lk = 0;
    size_t k = 0;
  };
  std::vector<std::vector<Id>> pred_vals;
  // Per shared entry, the values it reads, sorted, each once (Lean
  // `refClosure Expr.directNodes`, printed packed as `closures`).
  std::vector<std::vector<Id>> expr_vals;
  // The shared entries' structural annotations (Lean `ExprAnn`): one past
  // the largest value each entry's closure reads (0: none), the set of
  // fields of the values it reads in its own field (bit f), whether every
  // coefficient value it reads is public, and its length.
  std::vector<uint64_t> expr_max, expr_fields, expr_len;
  std::vector<bool> expr_pub;
  // Per shared entry, its degree in the committed cells (Lean `degT
  // cellNdT`) and whether it vanishes at zero (Lean `zeroT`).
  std::vector<uint64_t> expr_deg;
  std::vector<bool> expr_zero;
  // Per challenge, the degree of every value's and every shared entry's
  // coordinates in it (Lean `DegAnn`: `Expr.deg` at the values' degrees,
  // the largest over the coordinates; a value of the challenge 1, a public
  // expression its expression's).
  std::vector<std::vector<uint64_t>> deg_vals, deg_refs;
  // Per value, the codes of what it reads from the run (Lean `ReadsAnn`,
  // `Read.code`: 3 c for challenge c, 3 u + 1 for late value u), sorted,
  // each once.
  std::vector<std::vector<uint64_t>> val_reads;
  std::vector<bool> late_bad, gen_bad;
  std::vector<LookupDigit> lookup_owners;
  std::vector<CommDigit> comm_owners;
  // The completeness certificate (Lean `Gens`, `CDerivations`): per value
  // its generator (GENS: the item it names in A, B, C, D, SECOND), per
  // predicate its completeness derivation (COMP_DERIVS) and rank
  // (COMP_RANKS).
  struct Gen {
    enum Kind : uint8_t {
      kNone,
      kSource,
      kLookupDigit,
      kCommDigit,
      kSpec,
      kStaticHist,
      kTag,
      kAcc,
      kQuotDigit,
      kDigitsAcc,
      kLowDigit,
      kLateHist
    };
    Kind kind = kNone;
    size_t a = 0, b = 0, c = 0, d = 0;
    bool second = false;
  };
  struct CStep {
    enum Kind : uint8_t {
      kSource,
      kQuotIn,
      kDigitRow,
      kMacRow,
      kPadBool,
      kHyp,
      kCommIn,
      kCommRow,
      kSpecProd,
      kSpecRow,
      kFieldRow,
      kTwoTail
    };
    Kind kind = kSource;
    size_t id = 0;
    // kMacRow, kTwoTail: the site's side (the check over x's field).
    bool x_side = false;
    // kCommIn: the position of the quotient digit the lookup's record is.
    size_t j = 0;
    // kCommRow: per quotient digit, the digit lookup whose record it is.
    std::vector<size_t> lks;
  };
  std::vector<Gen> gens;
  std::vector<std::vector<CStep>> comp_derivs;
  std::vector<size_t> comp_ranks;
};

struct Program {
  size_t phases = 0;
  size_t msg_len = 0, ctx_len = 0;
  std::vector<MemberCheck> checks;
  std::vector<FieldDecl> fields;
  std::vector<DomainDecl> domains;
  std::vector<Value> values;
  // The shared entries' roots.
  std::vector<Id> exprs;
  std::vector<Predicate> predicates;
  std::vector<Table> tables;
  std::vector<Challenge> challenges;
  // In MsgBefore order.
  std::vector<Message> messages;
  std::vector<Batch> batches;
  std::vector<Circuit> circuits;
  std::vector<std::pair<RealRef, Id>> realization_circuits;
  std::vector<SpectralConv> convs;
  // Per domain, what the backend builds it from beyond the elements.
  std::vector<DomainRealization> realizations;
  // The parts of the compiled system the structure cannot describe (a
  // lowering's row with no owner, a reference to a node that is no value):
  // the printer refuses a program with any. Elements with no description
  // carry their own (Value::unmodeled, Predicate::unmodeled).
  std::vector<std::string> unmodeled;

  // The arenas.
  std::vector<Expr> nodes;
  std::vector<std::vector<size_t>> index_maps;
  // Each index map's named form (an `IndexMap.*` definition of Lean's
  // Encoding.lean whose entries are the map, "IndexMap.convLeft B la lb"),
  // "" for a map written by its runs; aligned with index_maps.
  std::vector<std::string> index_map_forms;
  std::vector<Coef> coefs;
  std::vector<NamedOp> ops;
  std::vector<LinearRows> linears;
};

}  // namespace proofs::gordiehowe::ir

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_REALIZED_PROGRAM_H_
