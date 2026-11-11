-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Derivation.Pure
public import GordieHoweNative.Language.RealizedProgram.Reader

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.Source`

The definitions of `GordieHowe.Language.Honest.Source` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/Source.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram}

/-- **A `mod_q` realized in the ungrouped digit form** (compiler/mod.h, `kDigits`): the digits, the
top one derived, with no grouping. -/
def _root_.GordieHowe.RealizedProgram.ModRealization.isDigitsTail (real : ModRealization) : Bool :=
  real.form == .digits && real.grouped.isNone

/-- **A `mod_q` realized in the one-digit form with no grouping** (compiler/mod.h, `kOneDigit`):
its quotient derived, from an accumulator of the left side (`quotDerivedAccB`) where it has one. -/
def _root_.GordieHowe.RealizedProgram.ModRealization.isOneDigitTail (real : ModRealization) : Bool :=
  real.form == .oneDigit && real.grouped.isNone

variable (ir) in
/-- **Member `m`'s needle reads a late value of the program.** -/
def memberReadsLate (m : Member) : Bool :=
  (ir.exprNodes (ir.needleExpr m.pred m.needle)).any fun w =>
    (ir.nodeReads ir.fuel w).any fun r =>
      match r with
      | .late u => decide (u < ir.values.length ∧ ir.IsLate u)
      | _ => false

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

variable (ir) in
/-- **The committed values value `v` reads**, with `n` levels (as `RealizedProgram.read`): a committed
value, a pad copy or a value bound to its digits itself, a public expression, an opaque value or a
bit view what the values it reads read; nothing for a late value, a message, a statement value, a
constant or a challenge. A value bound to its digits is read whole (`RealizedProgram.asgReads` reads its
digits instead). -/
def valReads : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, v =>
    match (ir.value v).kind with
    | .priv => [v]
    | .padCopy _ _ => [v]
    | .bound _ => [v]
    | .pub (.expr e) => (ir.exprNodes e).flatMap (valReads n)
    | .pub (.opaque _ args) => args.flatMap (valReads n)
    | .bits w _ => valReads n w
    | _ => []

/-- **The late values' messages** (`Structure.messages`), keyed by the late value, as a table built
once. -/
def _root_.GordieHowe.RealizedProgram.Structure.messageTab (S : Structure) : NatTrie ℕ :=
  NatTrie.ofList S.messages

variable (ir) in
/-- **An entry `(u, m)` of `messages` names `u`'s message**: value `m` exists and is the message of
`u`, as a check whose failure names the key and the value (`notMessage`). -/
def messageEntryE (e : ℕ × ℕ) : Except StructFailure Unit :=
  Twin.guardE (decide (e.2 < ir.values.length) &&
      match (ir.value e.2).kind with
      | .message u => u == e.1
      | _ => false) ⟨e.1, e.2, .notMessage⟩

/-- **A message value is its late value's entry** (value `m`, visited as `x`; the entries through
the table `MT`), as a check whose failure names the value and the late value (`uncovered`). -/
def messageCoverE (MT : NatTrie ℕ) (m : ℕ) (x : Value) : Except StructFailure Unit :=
  match x.kind with
  | .message u => Twin.guardE (MT.get? u == some m) ⟨m, u, .uncovered⟩
  | _ => .ok ()

variable (ir) in
/-- **The `messages` records check**: every entry names its key's message (a sweep of the
entries), and every message value is its late value's entry (a sweep of the values). -/
def messageRecsE (S : Structure) : Except StructFailure Unit :=
  Twin.seqE (Twin.allE (fun _ e => ir.messageEntryE e) 0 S.messages)
    (Twin.allE (messageCoverE S.messageTab) 0 ir.values)

variable (ir) in
/-- **`messageRecsE` as a `Bool`.** -/
def messageRecsB (S : Structure) : Bool := Twin.okB (ir.messageRecsE S)

/-- **`NoLateRead`, through the reads table**, at a program reader. -/
def PReader.noLateReadB (ir : RealizedProgram) [r : PReader] (v : ℕ) : Bool :=
  (r.reads v).all fun rd =>
    match rd with
    | .late u => !decide (u < r.nValues ∧ PReader.IsLate ir u)
    | _ => true

variable (ir) in
/-- **`NoLateRead`, through the reads table** (`PReader.noLateReadB` at the program). -/
def noLateReadB (v : ℕ) : Bool := @PReader.noLateReadB ir (PReader.ofProgram ir) v

/-- **`SrcCovered`, through the reads tables**, at a program reader. -/
def PReader.srcCoveredB (ir : RealizedProgram) [r : PReader] (MT : NatTrie ℕ) (rs : List Read) (w : ℕ) : Bool :=
  decide (w < r.nValues) &&
    (r.reads w).all (fun rd =>
      match rd with
      | .chal j => rs.contains (.chal j)
      | .late u => (!(MT.get? u).isSome || rs.contains (.pad u)) &&
          (!decide (PReader.IsSourceValue u) || (r.value u).reads.all fun rd =>
            match rd with
            | .chal j => rs.contains (.chal j)
            | _ => true)
      | .pad _ => true) &&
    (r.asgReads w).all fun u =>
      match (r.value u).kind with
      | .padCopy w' _ => rs.contains (.pad w')
      | _ => true

variable (ir) in
/-- **`SrcCovered`, through the reads tables** (`PReader.srcCoveredB` at the program). -/
def srcCoveredB (MT : NatTrie ℕ) (rs : List Read) (w : ℕ) : Bool :=
  @PReader.srcCoveredB ir (PReader.ofProgram ir) MT rs w

variable (ir) in
/-- **`GroupedMacC.digitsRoom`, as a check**: every lookup of the single record `gq` into a range
`[0, N)` is of domain `dy` with `0 < base ≤ N`. -/
def digitsRoomB (gq dy base : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [.leaf g] (.range N) (.lookup _) => !(g == gq) || (d == dy && decide (0 < base) && decide (base ≤ N))
    | _ => true

variable (ir) in
/-- **`GroupedMacC.finalRoom`, as a check**: every lookup of a single record `D` with
`D.beq Q` into a range `[0, N)` is of domain `dy` with `groups + 1 < 2N`. -/
def finalRoomB (Q : Expr) (dy groups : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [D] (.range N) (.lookup _) => !(D.beq Q) || (d == dy && decide (groups + 1 < 2 * N))
    | _ => true

variable (ir) in
/-- **Whether value `v` is the pad copy `m` of late value `w`**, as a check. -/
def isPadCopyB (v w : ℕ) (m : String) : Bool :=
  match (ir.value v).kind with
  | .padCopy w' m' => w' == w && m' == m
  | _ => false

variable (ir) in
/-- **Value `v` is a committed value of a domain of the program with a cell at each coordinate**,
as a check. -/
def privCellB (v : ℕ) : Bool :=
  (match (ir.value v).kind with
    | .priv => true
    | _ => false) &&
    decide (v < ir.values.length) && decide ((ir.value v).domain < ir.domains.length) &&
    ir.isCellValue (ir.value v).domain v

/-- A private value with valid value and domain indices has committed cells. -/
theorem privCellB_of_kind_priv {v : ℕ} (hv : v < ir.values.length)
    (hd : (ir.value v).domain < ir.domains.length) (hk : (ir.value v).kind = .priv) :
    ir.privCellB v = true := by
  simp [privCellB, hk, hv, hd, ir.isCellValue_self_of_kind_priv hk]

end

end GordieHowe.RealizedProgram
