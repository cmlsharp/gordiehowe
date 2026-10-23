-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Basic

@[expose] public section

/-!
# GordieHowe: the honest strategy from the source

The honest late values the realization generates (compiler/mac.h, compiler/mod.h, the LogUp
tables), as functions of the honest committed values, the challenges and the pads:

* **the tag of a MAC** (`GordieHowe.RealizedProgram.tagGen`): `U = Σ_c β^(c+1) · chunk_c(X_H)`, the MAC of the H
  operand at the key (`MacHHoldsAt`);
* **the accumulators of a grouped `mod_q`** (`GordieHowe.RealizedProgram.accNat`): per group and output coordinate,
  the sum of the integer convolutions of the group's chunks (`chunkTerm`);
* **the quotient digits of a grouped `mod_q`** (`GordieHowe.RealizedProgram.digitNat`): the base-`T` digits of the
  accumulator divided by `q`;
* **the late histogram of a table group** (`GordieHowe.RealizedProgram.histNat`): the histogram of the group's needles,
  for a group without a static histogram.

Each generated value is found by its owner (`tagOwner?`, `accOwner?`, `digitsOwner?`,
`histOwner?`). The generators read the source environment (`srcEnv`: the honest committed values
with their pad copies, the challenges, no late value); a late histogram reads the other generated
values as late values (`histEnv`).

* The generated values read only their exported reads, when each generator's inputs
  read only listed challenges and pads and no bound value reads a pad copy (`BoundNoCopy`).
* At the honest environment a MAC with a grouped tail (`GroupedMac`) satisfies its predicates, where its operands are bits.
* The MAC facts every tail form shares are `MacBase`, one MAC check over a field with its tail
  (`GordieHowe.RealizedProgram.MacFieldCheck`: the check over `y`'s field for a hosted MAC, or the
  check over either field for a MAC no domain hosts); the realization's facts over the MACs of both tail
  forms are in `HonestDigits.lean`.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp}

/-! ## The owners of the generated values -/

/-- **The first owner of each key**: entry `(k, a)` of `es` sets key `k` to `a` where no earlier
entry sets it. -/
def firstOwnerTab {α : Type} (es : List (ℕ × α)) : NatTrie α :=
  es.foldr (fun e t => t.set e.1 e.2) .nil

variable (ir) in
/-- **The keys the predicates own**: `(k, p)` for every key `k` that `keys` gives predicate `p`'s
body. -/
def predKeys {α : Type} (keys : ℕ → PredBody → List (ℕ × α)) : List (ℕ × α) :=
  ir.predicates.zipIdx.flatMap fun pp => keys pp.2 pp.1.body

/-- The key of a cross-field `equal`'s MAC tag. -/
def tagKeys (p : ℕ) : PredBody → List (ℕ × ℕ)
  | .cross _ _ _ _ _ real => [(real.tag, p)]
  | _ => []

variable (ir) in
/-- **The cross-field `equal` whose MAC tag is value `v`** (a table of the predicates' tags). -/
def tagOwner? (v : ℕ) : Option ℕ := (firstOwnerTab (ir.predKeys tagKeys)).get? v

/-- The key of a grouped `mod_q`'s accumulators. -/
def accKeys (p : ℕ) : PredBody → List (ℕ × ℕ)
  | .mod _ _ _ _ real =>
    match real.grouped with
    | some G =>
      match G.accumulators with
      | some (.leaf a) => [(a, p)]
      | _ => []
    | none => []
  | _ => []

variable (ir) in
/-- **The grouped `mod_q` whose accumulators are value `v`** (a table of the predicates'). -/
def accOwner? (v : ℕ) : Option ℕ := (firstOwnerTab (ir.predKeys accKeys)).get? v

/-- The key of a grouped `mod_q`'s quotient digits. -/
def digitsKeys (p : ℕ) : PredBody → List (ℕ × ℕ)
  | .mod _ _ _ _ real =>
    match real.grouped with
    | some G =>
      match G.groupDigits with
      | .leaf g => [(g, p)]
      | _ => []
    | none => []
  | _ => []

variable (ir) in
/-- **The grouped `mod_q` whose quotient digits are value `v`** (a table of the predicates'). -/
def digitsOwner? (v : ℕ) : Option ℕ := (firstOwnerTab (ir.predKeys digitsKeys)).get? v

/-- **A `mod_q` realized in the ungrouped digit form** (compiler/mod.h, `kDigits`): the digits, the
top one derived, with no grouping. -/
def _root_.GordieHowe.RealizedProgram.ModRealization.isDigitsTail (real : ModRealization) : Bool :=
  real.form == .digits && real.grouped.isNone

/-- **A `mod_q` realized in the one-digit form with no grouping** (compiler/mod.h, `kOneDigit`):
its quotient derived, from an accumulator of the left side (`quotDerivedAccB`) where it has one. -/
def _root_.GordieHowe.RealizedProgram.ModRealization.isOneDigitTail (real : ModRealization) : Bool :=
  real.form == .oneDigit && real.grouped.isNone

/-- **The lower digits of a `mod_q` in the digit form**: every digit but the derived top one. -/
def _root_.GordieHowe.RealizedProgram.ModRealization.lowerDigits (real : ModRealization) : List Expr := real.digits.dropLast

variable (ir) in
/-- The key of an ungrouped digit-form or one-digit `mod_q`'s accumulator (`digitsAcc`,
`oneDigitAcc`). -/
def digitsAccKeys (p : ℕ) : PredBody → List (ℕ × ℕ)
  | .mod _ _ _ _ real =>
    (if real.isDigitsTail then [(ir.digitsAcc real, p)] else []) ++
      (if real.isOneDigitTail then [(ir.oneDigitAcc real, p)] else [])
  | _ => []

variable (ir) in
/-- **The ungrouped digit-form or one-digit `mod_q` whose accumulator is value `v`** (a table of the
predicates'). -/
def digitsAccOwner? (v : ℕ) : Option ℕ := (firstOwnerTab (ir.predKeys ir.digitsAccKeys)).get? v

/-- The keys of an ungrouped digit-form `mod_q`'s lower digits: `(v, (p, j))` for lower digit `j`
the leaf `v`. -/
def lowDigitKeys (p : ℕ) : PredBody → List (ℕ × (ℕ × ℕ))
  | .mod _ _ _ _ real =>
    if real.isDigitsTail then
      (real.lowerDigits.zipIdx.filterMap fun Dj =>
        match Dj.1 with
        | .leaf v => some (v, (p, Dj.2))
        | _ => none)
    else []
  | _ => []

variable (ir) in
/-- **The ungrouped digit-form `mod_q` one of whose lower digits is value `v`**, as
`(predicate, digit index)` (a table of the predicates'). -/
def lowDigitOwner? (v : ℕ) : Option (ℕ × ℕ) := (firstOwnerTab (ir.predKeys lowDigitKeys)).get? v

variable (ir) in
/-- **The table group whose late histogram is value `v`**, the first such group, as
`(table, group)`. -/
def histOwner? (v : ℕ) : Option (ℕ × ℕ) :=
  ((List.range ir.tables.length).flatMap fun t =>
    (List.range (ir.groupCountOf t)).map fun g => (t, g)).find? fun tg =>
      (ir.groupOf tg.1 tg.2).lateMult == some v

variable (ir) in
/-- **Value `v` is generated by the realization**: a MAC tag, the accumulators or the quotient
digits of a grouped `mod_q`, a late histogram, or the accumulator or a lower digit of an ungrouped
digit-form `mod_q`. -/
def IsGenerated (v : ℕ) : Prop :=
  (ir.tagOwner? v).isSome ∨ (ir.accOwner? v).isSome ∨ (ir.digitsOwner? v).isSome ∨
    (ir.histOwner? v).isSome ∨ (ir.digitsAccOwner? v).isSome ∨ (ir.lowDigitOwner? v).isSome

/-! ## The generators -/

/-- **The tag of a MAC** at the reader `rd` and the key's value `β` (`MacTagAt`):
`Σ_c β^(c+1) · chunk_c(X_H)` (`MacHHoldsAt`) where `x`'s domain hosts the MAC;
`Σ_c β^(c+1) · chunk_c(X_A)`, the chunks of the coordinates of `x` equal to `1` (`MacTwoTagAt`;
compiler/mac.h, `mac_odd`: `U = Σ_c chunk_c(X_A) r_c`), where no domain does. -/
def tagGen (rd : ir.Valuation I) (dx : ℕ) (x : Expr) (real : MacRealization)
    (β : (I real.macField).K) : (I real.macField).K :=
  match real.blindX with
  | none => ∑ c : Fin real.chunks, β ^ ((c : ℕ) + 1) * ir.macChunkH rd real.macField dx x real.width c
  | some _ =>
    ∑ c : Fin real.chunks, β ^ ((c : ℕ) + 1) * ir.macChunkA rd real.macField dx x real.width c

/-- **The integer convolution of chunk `c`** at output coordinate `i` of the MAC unit form `u` in
domain `d` (`chunkTerm`, `0` for an empty chunk width). -/
def unitTerm (rd : ir.Valuation I) (d : ℕ) (u : MacUnits) (i c : ℕ) : ℤ :=
  if hw : 0 < u.width then ir.chunkTerm rd d u.powers u.width u.taps u.operand i c hw else 0

/-- **The accumulator of group `fc = (first, count)`** at output coordinate `i`: the sum of the
integer convolutions of its chunks `[first − 1, first − 1 + count)`, as a natural. -/
def groupAcc (rd : ir.Valuation I) (d : ℕ) (u : MacUnits) (fc : ℕ × ℕ) (i : ℕ) : ℕ :=
  (∑ c ∈ Finset.range fc.2, ir.unitTerm rd d u i (fc.1 - 1 + c)).toNat

/-- **Coordinate `n` of the accumulators** of a grouped `mod_q` with units `u` and grouping `G`:
group `n / w`'s accumulator at output coordinate `n % w`. -/
def accNat (rd : ir.Valuation I) (d : ℕ) (u : MacUnits) (G : GroupedMod) (n : ℕ) : ℕ :=
  ir.groupAcc rd d u (G.groups.getD (n / u.width) default) (n % u.width)

/-- **Coordinate `n` of the quotient digits** of a grouped `mod_q` with modulus `q`: digit
`n % k` (base `T`) of accumulator `n / k` divided by `q`. -/
def digitNat (rd : ir.Valuation I) (d q : ℕ) (u : MacUnits) (G : GroupedMod) (n : ℕ) : ℕ :=
  ir.accNat rd d u G (n / G.digitCount) / q / G.base ^ (n % G.digitCount) % G.base

/-- **The accumulator of an ungrouped digit-form `mod_q`** with left side `e` in domain `d`, at
coordinate `i`: the natural of the left side's integer reading. -/
def digitsAccNat (rd : ir.Valuation I) (d : ℕ) (e : Expr) (i : ℕ) : ℕ :=
  (ir.evalIntWith rd d e i).toNat

/-- **Lower digit `j` of an ungrouped digit-form `mod_q`** with modulus `q`, left side `e` and
radix `B`, at coordinate `i`: digit `j` (base `B`) of the accumulator divided by `q`. -/
def lowDigitNat (rd : ir.Valuation I) (d q : ℕ) (e : Expr) (B j i : ℕ) : ℕ :=
  ir.digitsAccNat rd d e i / q / B ^ j % B

variable (ir) in
/-- **Member `m`'s needle reads a late value of the program.** -/
def memberReadsLate (m : Member) : Bool :=
  (ir.exprNodes (ir.needleExpr m.pred m.needle)).any fun w =>
    (ir.nodeReads ir.fuel w).any fun r =>
      match r with
      | .late u => decide (u < ir.values.length ∧ ir.IsLate u)
      | _ => false

/-- **The needles a late histogram counts** in group `g` of table `t`: with a static histogram
beside it, the needles of the members reading late values (the static histogram counts the
others); otherwise all the group's needles. -/
def histNeedles (rd : ir.Valuation I) (f t g : ℕ) : List (I f).K :=
  if (ir.groupOf t g).staticMult.isSome then
    ((ir.members t g).filter ir.memberReadsLate).flatMap (ir.memberVals rd f)
  else ir.groupNeedles rd f t g

/-- **The late histogram of group `g` of table `t`**, entry `j`: the number of the needles it counts
(`histNeedles`) equal to `j`, read by `rd` in the field of the table's challenge. -/
def histNat (rd : ir.Valuation I) (t g j : ℕ) : ℕ :=
  if h : j < ir.tableSize t then
    ((ir.histNeedles rd (ir.chalField (ir.alphaOf t)) t g).count
      ((⟨j, h⟩ : Fin (ir.tableSize t)) : (I (ir.chalField (ir.alphaOf t))).K))
  else 0

/-! ## The generated late values -/

variable (I) in
/-- **The source environment** at the statement `x`, the committed values `val`, the challenges `c`
and the pads `π`: the honest committed assignment (`honestAsg`, its pad copies computed from the
pads), the challenges, no late value. The tags and the accumulators read it. -/
def srcEnv (x val : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) :
    ir.Env I where
  stmt := x
  asg := ir.bindAsg (ir.honestAsg I val π)
  chal := ir.chalRead I c
  late := 0

/-- **A late value is a value of the program.** -/
theorem lt_of_isLate {v : ℕ} (h : ir.IsLate v) : v < ir.values.length := by
  by_contra hv
  have h1 := h.1
  revert h1
  rw [value_eq_default (Nat.le_of_not_lt hv)]
  decide

variable (I) in
/-- **The source late values of a valuation** `L`: `L` at the source program's late values below
their sizes, `0` elsewhere. -/
def srcLateOf (L : ir.Valuation I) : ir.Valuation I := fun v i =>
  if ir.IsSourceValue v ∧ ir.IsLate v ∧ i < (ir.value v).size then L v i else 0

variable (I) in
/-- **The source environment with the source program's late values** `L` (`srcLateOf`): the
source environment (`srcEnv`) whose late values are `L` at the source late values. The generators
read it. -/
def srcEnvL (x val L : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) :
    ir.Env I :=
  { ir.srcEnv I x val c π with late := ir.srcLateOf I L }

/-- **The source environment with the late values `0` is the source environment.** -/
theorem srcEnvL_zero (x val : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) :
    ir.srcEnvL I x val 0 c π = ir.srcEnv I x val c π := by
  have h0 : ir.srcLateOf I 0 = 0 := by
    funext v i
    unfold srcLateOf
    split <;> rfl
  unfold srcEnvL
  rw [h0]
  rfl

/-- **The generated values read from the source environment** `e`: a MAC tag (`tagGen`, at
coordinate `0`), the accumulators (`accNat`) and the quotient digits (`digitNat`) of a grouped
`mod_q`, the accumulator (`digitsAccNat`) and the lower digits (`lowDigitNat`) of an ungrouped
digit-form `mod_q`; `0` for any other value. -/
def genSrc (e : ir.Env I) (v i : ℕ) : (I (ir.valueField v)).K :=
  match ir.tagOwner? v with
  | some p =>
    match (ir.predicate p).body with
    | .cross dx x _ _ _ real =>
      if i = 0 then castElt (ir.tagGen (ir.reader e) dx x real (castElt (e.chal real.key 0)))
      else 0
    | _ => 0
  | none =>
    match ir.accOwner? v with
    | some t =>
      match (ir.predicate t).body with
      | .mod d _ L _ real =>
        match real.grouped, macUnits? L with
        | some G, some u => (ir.accNat (ir.reader e) d u G i : (I (ir.valueField v)).K)
        | _, _ => 0
      | _ => 0
    | none =>
      match ir.digitsOwner? v with
      | some t =>
        match (ir.predicate t).body with
        | .mod d q L _ real =>
          match real.grouped, macUnits? L with
          | some G, some u => (ir.digitNat (ir.reader e) d q u G i : (I (ir.valueField v)).K)
          | _, _ => 0
        | _ => 0
      | none =>
        match ir.digitsAccOwner? v with
        | some t =>
          match (ir.predicate t).body with
          | .mod d _ L _ _ => (ir.digitsAccNat (ir.reader e) d L i : (I (ir.valueField v)).K)
          | _ => 0
        | none =>
          match ir.lowDigitOwner? v with
          | some tj =>
            match (ir.predicate tj.1).body with
            | .mod d q L _ real =>
              (ir.lowDigitNat (ir.reader e) d q L real.radix tj.2 i : (I (ir.valueField v)).K)
            | _ => 0
          | none => 0

/-- **The environment the late histograms read**: the source environment `e` with its source late
values and the generated values other than the histograms (`genSrc`) as its late values, `0` past a
value's coordinates. -/
def histEnv (e : ir.Env I) : ir.Env I :=
  { e with late := fun v i =>
      if i < (ir.value v).size then (if ir.IsSourceValue v then e.late v i else ir.genSrc e v i)
      else 0 }

/-- **The generated values** at the source environment `e`: the late histograms (`histNat`) read
from `e` with the values `genSrc e` as late values, every other value by `genSrc e`; `0` past a
value's coordinates. -/
def genVal (e : ir.Env I) (v i : ℕ) : (I (ir.valueField v)).K :=
  if i < (ir.value v).size then
    match ir.histOwner? v with
    | some tg => (ir.histNat (ir.reader (ir.histEnv e)) tg.1 tg.2 i : (I (ir.valueField v)).K)
    | none => ir.genSrc e v i
  else 0

/-! ## The facts the generators need -/

variable (ir I) in
/-- **The facts of a program and its interpretation the generated late values need**: every late
value other than the source program's is generated (`IsGenerated`) and no generated late value is
a source value, a tag's pad space is the whole field, every pad space contains the naturals, and every
late value has a pad cell in its domain at each coordinate. -/
structure GenFacts : Prop where
  /-- Every late value other than the source program's is generated. -/
  allGen : ∀ l : ir.Late, ¬ ir.IsSourceValue l.1 → ir.IsGenerated l.1
  /-- No generated late value is a source value. -/
  genNotSource : ∀ l : ir.Late, ir.IsGenerated l.1 → ¬ ir.IsSourceValue l.1
  /-- A tag's pad space is the whole field. -/
  tagFull : ∀ v, (ir.tagOwner? v).isSome → (ir.value v).padSpace = .full
  /-- Every pad space of a late value contains the naturals. -/
  natCast : ∀ l : ir.Late, ∀ n : ℕ,
    (n : (I (ir.valueField l.1)).K) ∈ (I (ir.valueField l.1)).space (ir.value l.1).padSpace
  /-- Every late value's domain is a domain of the program. -/
  domain : ∀ l : ir.Late, (ir.value l.1).domain < ir.domains.length
  /-- Every late value has a pad cell in its domain at each coordinate. -/
  padCells : ∀ l : ir.Late, ∀ i < (ir.value l.1).size,
    CellKey.pad l.1 i ∈ ir.cellKeys (ir.value l.1).domain

/-- **A generated value lies in its pad space**: a tag's pad space is the whole field
(`GenFacts.tagFull`), every other generated value is a natural (`GenFacts.natCast`). -/
theorem genVal_mem (hG : ir.GenFacts I) (e : ir.Env I) (l : ir.Late) (i : ℕ) :
    ir.genVal e l.1 i ∈ (I (ir.valueField l.1)).space (ir.value l.1).padSpace := by
  unfold genVal
  split
  swap
  · exact AddSubgroup.zero_mem _
  split
  · exact hG.natCast l _
  · unfold genSrc
    split
    · rename_i p hp
      rw [hG.tagFull l.1 (by rw [hp]; rfl)]
      exact AddSubgroup.mem_top _
    · repeat' split
      all_goals first | exact hG.natCast l _ | exact AddSubgroup.zero_mem _

/-! ## The honest late values -/

variable (ir I) in
/-- **The source program's late values** of honest inputs `Inp`, as functions of the challenges:
in their pad spaces (`mem`), each reading only its exported challenges (`respects`). -/
structure SrcLate (Inp : Type) where
  /-- The late values at an input and the challenges. -/
  late : Inp → (∀ k, (ir.layout I).Ch k) → ir.Valuation I
  /-- The source late values lie in their pad spaces. -/
  mem : ∀ y c (l : ir.Late), ir.IsSourceValue l.1 → ∀ i,
    late y c l.1 i ∈ (I (ir.valueField l.1)).space (ir.value l.1).padSpace
  /-- Each source late value reads only its exported challenges. -/
  respects : ∀ y v, ir.IsSourceValue v → ir.IsLate v → ∀ c c' : (∀ k, (ir.layout I).Ch k),
    (∀ j, Read.chal j ∈ (ir.value v).reads → ir.chalRead I c j = ir.chalRead I c' j) →
      late y c v = late y c' v

variable (I) in
/-- **The honest late values** of the honest inputs `y` (statement `stmtOf y`, committed values
`val y`, the source program's late values `SL`) at the challenges `c` and the pads `π`: the source
program's late values at its own late values, the generated values (`genVal`) at the source
environment with those late values (`srcEnvL`) at every other. -/
def genLate {Inp : Type} (hG : ir.GenFacts I) (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (y : Inp)
    (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) (l : (ir.layout I).Late) :
    (ir.layout I).Mask l := fun i =>
  if h : ir.IsSourceValue l.1 then ⟨SL.late y c l.1 i, SL.mem y c l h i⟩
  else ⟨ir.genVal (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) l.1 i, genVal_mem hG _ l i⟩

/-- **The honest environment reads the honest late values** at the late values' coordinates: the
message minus the pad (`GenFacts.padCells`: the honest assignment's pads are the pads). -/
theorem honestEnv_late_genLate {Inp : Type} (hG : ir.GenFacts I) (stmtOf val : Inp → ir.Valuation I)
    (SL : ir.SrcLate I Inp) (x : ir.Valuation I) (y : Inp) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) (l : ir.Late) {i : ℕ} (hi : i < (ir.value l.1).size) :
    (ir.honestEnv I x (val y) (ir.genLate I hG stmtOf val SL y) c π).late l.1 i =
      (ir.genLate I hG stmtOf val SL y c π l ⟨i, hi⟩).1 := by
  have hcond : (l.1 : ℕ) < ir.values.length ∧ ir.IsLate l.1 ∧ i < (ir.value l.1).size :=
    ⟨l.1.2, l.2, hi⟩
  simp only [honestEnv, layoutEnv, hcond, and_self, ite_true, msgRead, bindAsg,
    honestAsg_pad (hG.domain l) (hG.padCells l i hi), padsOf, ProofSystem.PhaseLayout.honestRun]
  change (((ir.genLate I hG stmtOf val SL y c π l ⟨i, hi⟩).1 : (I (ir.valueField l.1)).K) + _) - _ = _
  simp

/-! ## The MAC's tail at the honest values -/

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-- **The target's bits read a bit** `bt` (`reader_targetBits`), on the integers and in the field. -/
theorem reader_targetBits_int (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes) (e : ir.Env I)
    {tb dy tag : ℕ} (h : ir.targetBitsB tb dy tag = true) (hd : dy < ir.domains.length)
    (h2 : 1 < ir.charOf (ir.domainField dy))
    (htf : ∀ nm args, (ir.value tb).kind = .pub (.opaque nm args) → ∀ xs i,
      I.opaqueFn nm xs i = if ((xs.headD 0) 0).testBit i then 1 else 0) (m : ℕ) :
    ∃ bt : ℕ, bt < 2 ∧ ir.evalIntWith (ir.reader e) dy (.leaf tb) m = bt ∧
      ir.evalWith (ir.reader e) dy (.leaf tb) m = (bt : (I (ir.domainField dy)).K) ∧
      (bt = 1 ↔ ((I (ir.valueField tag)).toNat (e.late tag 0 + e.asg.pad tag 0)).testBit m) := by
  obtain ⟨bt, hbt2, hrd, hiff⟩ := reader_targetBits hwf hL e h hd h2 htf m
  have htb := h
  unfold targetBitsB at htb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htb
  obtain ⟨⟨⟨-, htbf⟩, -⟩, htb⟩ := htb
  refine ⟨bt, hbt2, ?_, by simp only [evalWith, evalE_leaf, hrd, castElt_natCast htbf], hiff⟩
  simp only [evalIntWith, Expr.evalInt]
  rw [intOf_of_ne_constant _ (fun es hes => by rw [hes] at htb; cases htb) _
      (fun x hx => by rw [hx] at htb; cases htb), hrd,
    hL.toNat_natCast _ (htbf ▸ domainField_lt hwf hd) bt (by rw [htbf]; simp only [charOf] at h2; omega)]

/-- **A MAC check over a field's tail holds at the honest values** (compiler/mac.h; the converse of
`crossHolds_or_macBad`): where the tag is the MAC of the chunks of the check's operand (`hT`:
`Σ_c β^(c+1) · chunk_c(z)`, the chunks of the coordinates of the check's operand equal to `1`), the
check's blind is the polynomial-basis bits of the tag's pad (`hbl`) and the check's operand's
integer reading is its indicator (`hyint`), each bit of the target (the tag's message) is the parity
of the tail's integer left side: the blind plus the integer convolutions
(`MACRows.unpack_maskedMAC`), so the tail `mod_2` holds. `hM` is a property of the model
(`Interp.MacModel`). -/
theorem tail_holds_of_honest (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I) {pid dy : ℕ} {y : Expr}
    {bl : ℕ} {real : MacRealization} (h2 : 2 < ir.charOf (ir.domainField dy))
    (hw0 : 0 < real.width) (hmf : real.macField < ir.fields.length)
    (htag : ir.macTagB real = true) (hbl0 : ir.macBlindCoreB dy bl real = true)
    (hlenY : ir.exprLen y = real.chunks * real.width) {t : ℕ} (ht : t < ir.predicates.length)
    (htB : ir.macTailAtB pid dy y bl real t = true)
    (hT : (castElt (ir.reader e real.tag 0) : (I real.macField).K) =
      ∑ c : Fin real.chunks, (castElt (e.chal real.key 0) : (I real.macField).K) ^ ((c : ℕ) + 1) *
        ir.macChunkA (ir.reader e) real.macField dy y real.width c)
    (hbk : (ir.value bl).kind = .padCopy real.tag "polynomialBits")
    (hbl : ∀ i < real.width, ir.reader e bl i =
      if ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit i then 1 else 0)
    (hdy : dy < ir.domains.length)
    (hyint : ∀ j < ir.exprLen y, ir.evalIntWith (ir.reader e) dy y j =
      if ir.evalWith (ir.reader e) dy y j = 1 then 1 else 0) :
    ir.HoldsWith (ir.reader e) (ir.predicate t).body := by
  have hdF := domainField_lt hwf hdy
  obtain ⟨hpch, hcharF, ⟨h00, h11⟩, -⟩ := modData hwf hI hL hdy h2
  unfold macTagB at htag
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htag
  obtain ⟨⟨⟨htl, htagf⟩, htsz⟩, htk⟩ := htag
  have htagk : (ir.value real.tag).kind = .late := by
    revert htk
    cases (ir.value real.tag).kind <;> simp
  unfold macBlindCoreB at hbl0
  have htB' := htB
  unfold macTailAtB at htB'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB'
  obtain ⟨-, htB'⟩ := htB'
  split at htB'
  · rename_i d b r w nch taps y' tb real' hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at htB'
    obtain ⟨⟨⟨⟨⟨⟨⟨hd, hblq⟩, hw⟩, hnch⟩, hy'⟩, hpow⟩, htb⟩, hcm⟩ := htB'
    have hy'' := Expr.eq_of_beq hy'
    subst d w nch y' hblq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbl0
    obtain ⟨⟨hbv, hbf⟩, hbsz⟩ := hbl0
    split at hcm
    · simp only [decide_eq_true_eq] at hcm
      obtain ⟨hMF, htf⟩ := hM.mod t ht _ _ _ _ _ _ _ _ _ hbt
      have hrf : ir.valueField r = real.macField := by
        unfold powersB at hpow
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow
        exact hpow.1.1.2
      rw [hrf] at hMF
      have := hMF.charTwo
      obtain ⟨B, hunp, heB⟩ := hMF.basis
      have hch2 : ir.charOf real.macField = 2 := by
        have h1 := hI.ringChar _ hmf
        rw [ringChar.eq (I real.macField).K 2, hI.characteristic _ hmf] at h1
        exact h1.symm
      rw [hbt]
      set L : Expr := .add (.leaf b) (.apply (.macConv r real.width real.chunks taps) y) with hLdef
      set rd := ir.reader e with hrd
      set β : (I real.macField).K := castElt (e.chal real.key 0) with hβ
      set Tval : (I real.macField).K := castElt (e.late real.tag 0 + e.asg.pad real.tag 0)
        with hTv
      set PH : (I real.macField).K := castElt (e.asg.pad real.tag 0) with hPH
      set W : MACRows.Wit (I (ir.domainField dy)).K real.width real.chunks :=
        (0, fun j => ir.evalWith rd dy (.leaf b) j, fun c j => ir.evalWith rd dy y (c * real.width + j))
        with hW
      have hrb : ∀ c : Fin real.chunks, NamedOp.macRb ir rd r real.width c =
          Conv.bitsNat B.toMACBasis (β ^ ((c : ℕ) + 1)) := by
        intro c
        funext j
        have hpw := reader_powers hL e hmf (by rw [hch2]; omega) hpow c.2
        rw [← hrd, ← hβ] at hpw
        simp only [NamedOp.macRb, Conv.bitsNat, hunp, ← hpw, toNat_castElt_of_eq hrf]
      -- the blind reads the pad's bits
      have hbval : ∀ j : Fin real.width, ir.evalWith rd dy (.leaf b) j =
          if ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit j then 1 else 0 := by
        intro j
        simp only [evalWith, evalE_leaf]
        rw [hbl j j.2]
        split_ifs
        · exact castElt_one_of_eq hbf
        · exact castElt_zero
      have hacc : ∀ m : Fin real.width, ir.evalIntWith rd dy L m =
          (MACRows.accumulatorNat taps.toFinset B.toMACBasis β W m : ℤ) := by
        intro m
        have hbm : ir.intOf rd b m = if ir.evalWith rd dy (.leaf b) m = 1 then 1 else 0 := by
          have hbk' := hbk
          have hone : (I (ir.valueField b)).toNat 1 = 1 := by
            simpa using hL.toNat_natCast _ (hbf ▸ hdF) 1 (by rw [hbf]; simp only [charOf] at h2; omega)
          have hzero : (I (ir.valueField b)).toNat 0 = 0 := by
            simpa using hL.toNat_natCast _ (hbf ▸ hdF) 0 (by rw [hbf]; simp only [charOf] at h2; omega)
          rw [intOf_of_ne_constant rd (fun es h => by rw [hbk'] at h; cases h), hbval m,
            hbl m m.2]
          split_ifs <;> simp_all
        have hyc : ∀ c : Fin real.chunks, ∀ j : Fin real.width,
            ir.evalIntWith rd dy y (c * real.width + j) =
              if ir.evalWith rd dy y (c * real.width + j) = 1 then 1 else 0 := fun c j =>
          hyint _ (by
            rw [hlenY]
            have := c.2
            have := j.2
            nlinarith)
        have happ := NamedOp.applyInt_macConv ir hpch
          (fun k hk => hL.toNat_natCast _ hdF k hk) rd (r := r) (nch := real.chunks) (taps := taps)
          hw0 hcm (fun j => ir.evalIntWith rd dy y j) m
        have hev : ir.evalIntWith rd dy L m = ir.intOf rd b m +
            NamedOp.applyInt ir (ir.domainField dy) rd (.macConv r real.width real.chunks taps)
              (fun j => ir.evalIntWith rd dy y j) m := rfl
        rw [hev, happ, hbm]
        simp only [MACRows.accumulatorNat, Nat.cast_add, Nat.cast_sum, Nat.mod_eq_of_lt m.2,
          Nat.div_eq_of_lt m.2, zero_mul, zero_add, Conv.applyConv_eq_mulVec, Matrix.mulVec,
          dotProduct, Nat.cast_mul, hW, MACRows.pmac, MACRows.x, LinearMap.coe_comp,
          Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
        refine congrArg₂ (· + ·) ?_ ?_
        · split_ifs <;> rfl
        · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hrb c, hyc c j]
          split_ifs <;> simp
      -- the masked MAC of the check's operand in domain `A` is the target
      have hmac : MACRows.maskedMAC B.toMACBasis β W = Tval := by
        have hpad : MAC.pack B.toMACBasis (fun j => if MACRows.pmac W j = 1 then 1 else 0) = PH := by
          conv_rhs => rw [← B.toMACBasis.pack_unpack PH]
          unfold MAC.pack
          refine Finset.sum_congr rfl fun j _ => ?_
          have hu : B.toMACBasis.unpack PH j =
              ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit j := by
            rw [hunp, hPH, toNat_castElt_of_eq htagf]
          dsimp only
          rw [show MACRows.pmac W j = ir.evalWith rd dy (.leaf b) j from rfl, hbval j, hu]
          by_cases h : ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit j = true
          · rw [if_pos h, if_pos rfl, if_pos h, one_mul]
          · rw [if_neg h, if_neg zero_ne_one, if_neg h, zero_mul]
        have hlate : rd real.tag 0 = e.late real.tag 0 := by rw [hrd, reader_of_late e htagk]
        unfold MACRows.maskedMAC MAC.sharedWitnessMAC MAC.ladder
        rw [hpad, hTv, castElt_add, ← hlate, hT, hPH]
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        dsimp only
        rw [mul_comm]
        congr 1
        simp only [macChunkA, MAC.pack]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [heB, mul_comm, evalPad_of_lt (by rw [hlenY]; have := c.2; have := i.2; nlinarith)]
        rfl
      have hpar := MACRows.unpack_maskedMAC B β W
      rw [hmac] at hpar
      intro m hm
      have hm' : m < real.width := by
        change m < (ir.value b).size at hm
        rwa [hbsz] at hm
      obtain ⟨bt, hbt2, hint, -, hbtiff⟩ := reader_targetBits_int hwf hL e htb hdy (by omega) htf m
      rw [hint, hacc ⟨m, hm'⟩]
      have hp := congrFun hpar ⟨m, hm'⟩
      rw [hunp, hTv, toNat_castElt_of_eq htagf] at hp
      set A := MACRows.accumulatorNat taps.toFinset B.toMACBasis β W ⟨m, hm'⟩
      have hb' : bt = 1 ↔ A % 2 = 1 := by
        rw [hbtiff, hp, decide_eq_true_iff]
      rcases Nat.mod_two_eq_zero_or_one A with h0 | h1
      · have : bt = 0 := by
          have : bt ≠ 1 := fun h => by rw [hb'.1 h] at h0; exact absurd h0 (by norm_num)
          omega
        subst this
        exact ⟨(A / 2 : ℕ), by push_cast; omega⟩
      · have : bt = 1 := hb'.2 h1
        subst this
        exact ⟨(A / 2 : ℕ), by push_cast; omega⟩
    · simp at hcm
  · cases htB'

/-! ## The grouped tail at the honest values -/

/-- **A constant holding `c` reads `c`** at an environment's reader (`constAll`; the leaf facts'
constants, which every reader of an environment has). -/
theorem evalE_leaf_constAll_reader (hL : I.Lawful ir primeNodes) (e : ir.Env I) {u c n f : ℕ}
    (h : ir.constAll u c n f = true) (hf : f < ir.fields.length) (hc : c < ir.charOf f) {i : ℕ}
    (hi : i < n) : ir.evalE (ir.reader e) f (.leaf u) i = (c : (I f).K) := by
  unfold constAll at h
  split at h
  · rename_i es hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hn, hall⟩, hvf⟩ := h
    have hes : es.getD i 0 = c := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact hall _ (List.getElem_mem _)
    rw [evalE_leaf, reader_of_constant e hk i, hes, hL.decode_natCast _ (hvf ▸ hf) c (hvf ▸ hc),
      castElt_natCast hvf]
  · cases h

/-- **A group's accumulator row holds at the honest accumulators** (`groupRowB`; the converse of
`groupSum`): where the accumulator `acc[g w + i]` is the cast of the integer sum of the group's
chunks' convolutions (`chunkTerm`) and the operand's readings are the casts of its integer readings
(`hy`), the row `acc[g w + i] + (p − 1) · macConv(r_g)(Y)_i = 0` holds. -/
theorem groupRow_holds (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (e : ir.Env I) {d acc g : ℕ} {u : MacUnits} {G : GroupedMod} {fc : ℕ × ℕ} {b : PredBody}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) (hw : 0 < u.width)
    (hpow : ir.macPowersB u.powers u.chunks = true) (hfit : fc.1 - 1 + fc.2 ≤ u.chunks)
    (hrow : ir.groupRowB L d u G acc g fc b = true)
    (hacc : ∀ i < u.width, (castElt (ir.reader e acc (g * u.width + i)) :
      (I (ir.domainField d)).K) = ((∑ c ∈ Finset.range fc.2,
        ir.chunkTerm (ir.reader e) d u.powers u.width u.taps u.operand i (fc.1 - 1 + c) hw : ℤ) :
          (I (ir.domainField d)).K))
    (hy : ∀ j < u.chunks * u.width, ir.evalWith (ir.reader e) d u.operand j =
      ((ir.evalIntWith (ir.reader e) d u.operand j : ℤ) : (I (ir.domainField d)).K)) :
    ir.HoldsWith (ir.reader e) b := by
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hd h2
  have hdF := domainField_lt hwf hd
  obtain ⟨key, hkey⟩ := exists_powersB_of_macPowersB hpow
  have hpow' := hpow
  unfold macPowersB at hpow'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow'
  obtain ⟨⟨hrfl, hr1⟩, -⟩ := hpow'
  unfold groupRowB at hrow
  split at hrow
  · rename_i d' ia acc' c rg w' cnt taps' ys z tgt
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrow
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd', hacc'⟩, hc⟩, hw'⟩, hcnt⟩, htaps⟩, hia⟩, hsub⟩, hY⟩, hz⟩, -⟩,
      -⟩, -⟩, -⟩ := hrow
    subst d' acc' w' cnt taps'
    split at hY
    · rename_i iy y' hderef
      simp only [Bool.and_eq_true, beq_iff_eq] at hY
      obtain ⟨hy', hiy⟩ := hY
      have hy'' := Expr.eq_of_beq hy'
      subst hy''
      set rd := ir.reader e with hrd
      intro i hi
      change i < ia.size at hi
      rw [IndexMap.size_of_runList hia] at hi
      simp only [evalWith, evalE_add, evalE_scale_const]
      rw [evalE_leaf_constAll_reader hL e hz hdF (by omega) hi]
      have hre : ir.evalE rd (ir.domainField d) (.reindex ia (.leaf acc)) i =
          castElt (rd acc (g * u.width + i)) := by
        change castElt (rd acc (ia.entry i)) = _
        rw [IndexMap.entry_of_runList hia hi]
      rw [hre, hacc i hi, hdec c (by omega), evalE_apply,
        NamedOp.apply_macConv ir rd hw]
      have hc1 : ((c : ℕ) : (I (ir.domainField d)).K) = -1 := by
        have : ((c + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
          rw [hc]
          exact CharP.cast_eq_zero _ _
        push_cast at this
        linear_combination this
      have hconv : ∑ c' : Fin fc.2, ∑ j : Fin u.width,
          (Conv.matrix u.taps.toFinset (NamedOp.macRb ir rd rg u.width c')
            ⟨i % u.width, Nat.mod_lt _ hw⟩ j : (I (ir.domainField d)).K) *
            ir.evalE rd (ir.domainField d) ys (i / u.width * (fc.2 * u.width) + (c' * u.width + j)) =
          ((∑ c ∈ Finset.range fc.2, ir.chunkTerm rd d u.powers u.width u.taps u.operand i
            (fc.1 - 1 + c) hw : ℤ) : (I (ir.domainField d)).K) := by
        rw [← Fin.sum_univ_eq_sum_range]
        push_cast
        refine Finset.sum_congr rfl fun c' _ => ?_
        simp only [chunkTerm]
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        have hlt : (c' : ℕ) * u.width + j < fc.2 * u.width := by
          have := c'.2
          have := j.2
          nlinarith
        rw [Nat.div_eq_of_lt hi, zero_mul, zero_add,
          macRb_subPowers hL e hrfl hr1 hkey hsub c'.2 (by omega),
          ← evalE_deref hwf.refsOrdered rd _ ys, hderef]
        change _ * ir.evalE rd _ _ (iy.entry _) = _
        rw [IndexMap.entry_of_runList hiy hlt]
        have hidx : (fc.1 - 1) * u.width + ((c' : ℕ) * u.width + j) =
            (fc.1 - 1 + c') * u.width + j := by ring
        have hlt' : (fc.1 - 1 + c') * u.width + j < u.chunks * u.width := by
          have := c'.2
          have := j.2
          have h3 : fc.1 - 1 + (c' : ℕ) + 1 ≤ u.chunks := by omega
          nlinarith
        rw [hidx, show ir.evalE rd (ir.domainField d) u.operand ((fc.1 - 1 + c') * u.width + j) =
          ir.evalWith rd d u.operand _ from rfl, hy _ hlt']
      rw [hconv, hc1]
      ring
    · cases hY
  · cases hrow

/-- **A number below `T^k` is its `k` base-`T` digits**: `Σ_{l<k} T^l · (n / T^l mod T) = n mod T^k`. -/
theorem sum_digits_eq_mod (T : ℕ) : ∀ (k n : ℕ),
    ∑ l ∈ Finset.range k, T ^ l * (n / T ^ l % T) = n % T ^ k
  | 0, n => by simp [Nat.mod_one]
  | k + 1, n => by
    rw [Finset.sum_range_succ, sum_digits_eq_mod T k n, Nat.mod_pow_succ]

/-- **The residues at the honest accumulators and digits** (`residuesB`): where the accumulator
`acc[j]` is the natural `A j` and the digits are the base-`T` digits of `A j / q` (`hgq`), which
fit in `k` digits (`hfit`), the residue `acc[j] − q · Σ_l T^l gq[j k + l]` is `A j mod q`. -/
theorem residue_honest (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (rd : ir.Valuation I) {d q acc : ℕ} {u : MacUnits} {G : GroupedMod}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) (hq : 0 < q)
    (hres : ir.residuesB d q u G acc = true) (A : ℕ → ℕ) {j : ℕ}
    (hj : j < G.groups.length * u.width)
    (hacc : (castElt (rd acc j) : (I (ir.domainField d)).K) = (A j : (I (ir.domainField d)).K))
    (hgq : ∀ gq, G.groupDigits = .leaf gq → ∀ l < G.digitCount,
      (castElt (rd gq (j * G.digitCount + l)) : (I (ir.domainField d)).K) =
        ((A j / q / G.base ^ l % G.base : ℕ) : (I (ir.domainField d)).K))
    (hfit : A j / q < G.base ^ G.digitCount) :
    ir.evalWith rd d G.residues j = ((A j % q : ℕ) : (I (ir.domainField d)).K) := by
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hd h2
  unfold residuesB at hres
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hres
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hres⟩ := hres
  split at hres
  · rename_i acc' c bb k T gq' gq hR hgd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hacc', hgq'⟩, hc⟩, hbb⟩, hk⟩, hT⟩, hTp⟩, -⟩, -⟩, -⟩ := hres
    subst acc' gq' bb k T
    simp only [evalWith]
    rw [← evalE_deref hwf.refsOrdered, hR]
    change castElt (rd acc j) + (I (ir.domainField d)).decode c *
      NamedOp.apply ir (ir.domainField d) rd (.batched (G.groups.length * u.width)
        (.fromDigits G.digitCount G.base)) (ir.evalE rd (ir.domainField d) (.leaf gq)) j = _
    rw [NamedOp.apply_batched_fromDigits ir rd _ hj, hdec c (by omega), hdec G.base hTp, hacc]
    have hcq : ((c : ℕ) : (I (ir.domainField d)).K) = -(q : (I (ir.domainField d)).K) := by
      have : ((c + q : ℕ) : (I (ir.domainField d)).K) = 0 := by
        rw [hc]
        exact CharP.cast_eq_zero _ _
      push_cast at this
      linear_combination this
    have hsum : ∑ l : Fin G.digitCount, (G.base : (I (ir.domainField d)).K) ^ (l : ℕ) *
        ir.evalE rd (ir.domainField d) (.leaf gq) (j * G.digitCount + l) =
        ((A j / q : ℕ) : (I (ir.domainField d)).K) := by
      have hd' : ∀ l : Fin G.digitCount, (G.base : (I (ir.domainField d)).K) ^ (l : ℕ) *
          ir.evalE rd (ir.domainField d) (.leaf gq) (j * G.digitCount + l) =
          ((G.base ^ (l : ℕ) * (A j / q / G.base ^ (l : ℕ) % G.base) : ℕ) :
            (I (ir.domainField d)).K) := by
        intro l
        rw [evalE_leaf, hgq gq hgd l l.2]
        push_cast
        ring
      rw [Finset.sum_congr rfl fun l _ => hd' l, ← Nat.cast_sum, Fin.sum_univ_eq_sum_range
        (fun l => G.base ^ l * (A j / q / G.base ^ l % G.base)), sum_digits_eq_mod,
        Nat.mod_eq_of_lt hfit]
    rw [hsum, hcq]
    have hdm : ((A j : ℕ) : (I (ir.domainField d)).K) =
        ((A j % q : ℕ) : (I (ir.domainField d)).K) + q * ((A j / q : ℕ) : (I (ir.domainField d)).K) := by
      rw [← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [hdm]
    ring
  · cases hres

/-- **The final quotient at the honest values** (`finalQuotB`): where the residues are naturals
`ρ g` (`hρ`), the blind and the right side read as the casts of their integer readings, and the
final sum `b + Σ_g ρ_g` is congruent to the right side modulo `q` and at least it (`hcong`,
`hle`), the final quotient `a · (b + Σ_g r_g) + c · e'` is the cast of `(b + Σ_g ρ_g − e') / q`. -/
theorem finalQuot_honest (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (rd : ir.Valuation I) {d q : ℕ} {E' : Expr} {u : MacUnits}
    {G : GroupedMod} {real : ModRealization} (hd : d < ir.domains.length)
    (h2 : 2 < ir.charOf (ir.domainField d)) (hfin : ir.finalQuotB d q E' u G real = true)
    {i : ℕ} (hiw : i < u.width) (ρ : ℕ → ℕ)
    (hρ : ∀ g < G.groups.length, ir.evalWith rd d G.residues (g * u.width + i) =
      ((ρ g : ℕ) : (I (ir.domainField d)).K))
    (bI eI : ℤ) (hb : (castElt (rd u.blind i) : (I (ir.domainField d)).K) = (bI : _))
    (he : ir.evalWith rd d E' i = (eI : (I (ir.domainField d)).K))
    (hcong : (q : ℤ) ∣ bI + ∑ g ∈ Finset.range G.groups.length, (ρ g : ℤ) - eI) :
    ir.evalWith rd d real.quotExpr i =
      (((bI + ∑ g ∈ Finset.range G.groups.length, (ρ g : ℤ) - eI) / q : ℤ) :
        (I (ir.domainField d)).K) := by
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hd h2
  unfold finalQuotB at hfin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨-, hfin⟩ := hfin
  split at hfin
  · rename_i F cq e₂ hQe
    split at hfin
    · rename_i a hca
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
      obtain ⟨⟨⟨⟨⟨hFs, he₂⟩, ha⟩, hcq⟩, hqa⟩, hqc⟩ := hfin
      have hQf : ir.evalWith rd d real.quotExpr i =
          (a : (I (ir.domainField d)).K) * (castElt (rd u.blind i) +
            ∑ g ∈ Finset.range G.groups.length, (ρ g : (I (ir.domainField d)).K)) +
            (cq : (I (ir.domainField d)).K) * ir.evalWith rd d E' i := by
        simp only [evalWith]
        rw [← evalE_deref hwf.refsOrdered, hQe, evalE_add, evalE_scale_const,
          evalE_finSum rd _ hiw _ F hFs, Expr.eq_of_beq he₂, hdec a ha, hdec cq hcq]
        congr 3
        refine Finset.sum_congr rfl fun g hg => ?_
        exact hρ g (Finset.mem_range.1 hg)
      have hqa' : (q : (I (ir.domainField d)).K) * a = 1 := by
        rw [← Nat.cast_mul, CharP.cast_eq_mod (I (ir.domainField d)).K
          (ir.charOf (ir.domainField d)), hqa, Nat.cast_one]
      have hqc' : (q : (I (ir.domainField d)).K) * cq + 1 = 0 := by
        rw [← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add,
          CharP.cast_eq_mod (I (ir.domainField d)).K (ir.charOf (ir.domainField d)), hqc,
          Nat.cast_zero]
      obtain ⟨Qz, hQz⟩ := hcong
      rw [hQz, Int.mul_ediv_cancel_left _ (by
        intro h0
        have : q = 0 := by exact_mod_cast h0
        subst this
        simp at hqa)]
      rw [hQf, hb, he]
      have hcast : (bI : (I (ir.domainField d)).K) + ∑ g ∈ Finset.range G.groups.length,
          (ρ g : (I (ir.domainField d)).K) - eI = q * Qz := by
        have := congrArg (fun z : ℤ => (z : (I (ir.domainField d)).K)) hQz
        push_cast at this
        exact this
      linear_combination (a : (I (ir.domainField d)).K) * hcast +
        ((Qz : (I (ir.domainField d)).K) - (eI : (I (ir.domainField d)).K) * cq) * hqa' +
        (eI : (I (ir.domainField d)).K) * a * hqc'
    · cases hfin
  · cases hfin

/-! ## The honest environment and the source environment -/

/-- **Readings agree where the late values read agree**: two environments with the same statement,
committed assignment and challenges read a value alike when they agree on the late values it reads
(`read_congr`). -/
theorem reader_eq_of_late {e e' : ir.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg)
    (hc : e.chal = e'.chal) {v : ℕ}
    (hl : ∀ u, Read.late u ∈ ir.nodeReads ir.fuel v → e.late u = e'.late u) :
    ir.reader e v = ir.reader e' v :=
  read_congr _ v ⟨hs, ha, fun c _ => congrFun hc c, hl⟩

/-- **The honest environment reads `0` off the late values' coordinates.** -/
theorem honestEnv_late_zero {x val : ir.Valuation I}
    {late : (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l}
    {c : ∀ k, (ir.layout I).Ch k} {π : (ir.layout I).Pads} {u i : ℕ}
    (h : ¬ (u < ir.values.length ∧ ir.IsLate u ∧ i < (ir.value u).size)) :
    (ir.honestEnv I x val late c π).late u i = 0 := by
  simp only [honestEnv, layoutEnv]
  rw [if_neg h]

section HonestEnv

variable {Inp : Type} (hG : ir.GenFacts I) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The honest environment of the honest inputs `y`. -/
local notation "HE" => ir.honestEnv I (stmtOf y) (val y) (ir.genLate I hG stmtOf val SL y) c π

set_option hygiene false in
/-- The honest environment of the honest inputs `y` at the statement `x`. -/
local notation "HEx" => ir.honestEnv I x (val y) (ir.genLate I hG stmtOf val SL y) c π

/-- **The honest environment's late values are the generated values** at every late value: the
messages minus the pads (`honestEnv_late_genLate`), `0` past the coordinates on both sides. -/
theorem honestEnv_late_eq (x : ir.Valuation I) {u : ℕ} (hu : u < ir.values.length)
    (hl : ir.IsLate u) (hns : ¬ ir.IsSourceValue u) :
    (HEx).late u =
      ir.genVal (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) u := by
  funext i
  by_cases hi : i < (ir.value u).size
  · rw [honestEnv_late_genLate hG stmtOf val SL x y c π ⟨⟨u, hu⟩, hl⟩ hi]
    simp only [genLate, dif_neg hns]
  · rw [honestEnv_late_zero fun h => hi h.2.2, genVal, if_neg hi]

/-- **The honest environment's late values are the source program's** at its own late values: both
environments read them below their sizes and `0` past them (`srcLateOf`). -/
theorem honestEnv_late_eq_src (x : ir.Valuation I) {u : ℕ} (hu : u < ir.values.length)
    (hl : ir.IsLate u) (hs : ir.IsSourceValue u) :
    (HEx).late u =
      ir.srcLateOf I (SL.late y c) u := by
  funext i
  by_cases hi : i < (ir.value u).size
  · rw [honestEnv_late_genLate hG stmtOf val SL x y c π ⟨⟨u, hu⟩, hl⟩ hi]
    simp only [genLate, hs, dite_true, srcLateOf, hl, hi, and_self, ite_true]
  · rw [honestEnv_late_zero fun h => hi h.2.2]
    simp only [srcLateOf, hi, and_false, ite_false]

/-- **A late value read but not a late value of the program reads `0`** in both environments. -/
theorem honestEnv_late_of_not (x : ir.Valuation I) {u : ℕ}
    (hl : ¬ (u < ir.values.length ∧ ir.IsLate u)) :
    (HEx).late u = 0 :=
  funext fun _ => honestEnv_late_zero fun h => hl ⟨h.1, h.2.1⟩

/-- **No late value of the program is read**, in the sense the honest and source environments
agree: every late read of `v` names no late value of the program. -/
def NoLateRead (v : ℕ) : Prop :=
  ∀ u, Read.late u ∈ ir.nodeReads ir.fuel v → ¬ (u < ir.values.length ∧ ir.IsLate u)

variable (ir) in
/-- **Value `w` reads no generated late value**: every late value of the program it reads is a
source value. -/
def NoGenRead (w : ℕ) : Prop :=
  ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w → u < ir.values.length → ir.IsLate u →
    ir.IsSourceValue u

/-- **The honest environment reads like the source environment with the source late values** at a
value reading no generated late value. -/
theorem reader_honestEnv_srcEnvL_of_noGen {v : ℕ} (hv : ir.NoGenRead v) :
    ir.reader HE v =
      ir.reader (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) v := by
  refine reader_eq_of_late (e := HE)
    (e' := ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) rfl rfl rfl fun u hu => ?_
  by_cases hl : u < ir.values.length ∧ ir.IsLate u
  · rw [honestEnv_late_eq_src hG stmtOf val SL y c π _ hl.1 hl.2 (hv u hu hl.1 hl.2)]
    rfl
  · rw [honestEnv_late_of_not hG stmtOf val SL y c π _ hl]
    funext i
    simp only [srcEnvL, srcLateOf]
    rw [if_neg (fun h => hl ⟨lt_of_isLate h.2.1, h.2.1⟩)]
    rfl

/-- **A value reading no late value of the program reads no generated late value.** -/
theorem NoLateRead.noGen {v : ℕ} (h : ir.NoLateRead v) : ir.NoGenRead v :=
  fun u hu hlt hl => absurd ⟨hlt, hl⟩ (h u hu)

/-- **The honest environment reads like the source environment with the source late values** at a
value reading no late value of the program (`reader_honestEnv_srcEnvL_of_noGen`). -/
theorem reader_honestEnv_srcEnvL_of_noLate {v : ℕ} (hv : ir.NoLateRead v) :
    ir.reader HE v =
      ir.reader (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) v :=
  reader_honestEnv_srcEnvL_of_noGen hG stmtOf val SL y c π hv.noGen

/-- **The integer convolutions read only the powers and the operand.** -/
theorem unitTerm_congr {rd rd' : ir.Valuation I} {d : ℕ} {u : MacUnits}
    (hr : rd u.powers = rd' u.powers) (hy : ∀ v ∈ ir.exprNodes u.operand, rd v = rd' v)
    (i c : ℕ) : ir.unitTerm rd d u i c = ir.unitTerm rd' d u i c := by
  unfold unitTerm
  split
  · have hrb : NamedOp.macRb ir rd u.powers u.width = NamedOp.macRb ir rd' u.powers u.width := by
      funext c j
      unfold NamedOp.macRb
      rw [hr]
    simp only [chunkTerm, hrb, evalIntWith_congr hy]
  · rfl

/-- **The accumulators read only the powers and the operand.** -/
theorem accNat_congr {rd rd' : ir.Valuation I} {d : ℕ} {u : MacUnits} {G : GroupedMod}
    (hr : rd u.powers = rd' u.powers) (hy : ∀ v ∈ ir.exprNodes u.operand, rd v = rd' v)
    (n : ℕ) : ir.accNat rd d u G n = ir.accNat rd' d u G n := by
  simp only [accNat, groupAcc, unitTerm_congr hr hy]

/-- **The quotient digits read only the powers and the operand.** -/
theorem digitNat_congr {rd rd' : ir.Valuation I} {d q : ℕ} {u : MacUnits} {G : GroupedMod}
    (hr : rd u.powers = rd' u.powers) (hy : ∀ v ∈ ir.exprNodes u.operand, rd v = rd' v)
    (n : ℕ) : ir.digitNat rd d q u G n = ir.digitNat rd' d q u G n := by
  simp only [digitNat, accNat_congr hr hy]

/-- **The tag reads only its `x` operand.** -/
theorem tagGen_congr {rd rd' : ir.Valuation I} {dx : ℕ} {x : Expr} {real : MacRealization}
    (hx : ∀ v ∈ ir.exprNodes x, rd v = rd' v) (β : (I real.macField).K) :
    ir.tagGen rd dx x real β = ir.tagGen rd' dx x real β := by
  unfold tagGen
  split
  · simp only [macChunkH, evalPad, evalWith, evalE_congr hx]
  · simp only [macChunkA, evalPad, evalWith, evalE_congr hx]
    rfl

variable (ir) in
/-- **The values and challenges the generator of value `v` (`genSrc`) reads**: a tag reads its H
operand's values and its key, a grouped `mod_q`'s accumulators and quotient digits read its
powers and its operand's values, an ungrouped digit-form `mod_q`'s accumulator and lower digits
read its left side's values. -/
def genInputs (v : ℕ) : List ℕ × List ℕ :=
  match ir.tagOwner? v with
  | some p =>
    match (ir.predicate p).body with
    | .cross _ x _ _ _ real => (ir.exprNodes x, [real.key])
    | _ => ([], [])
  | none =>
    match ir.accOwner? v with
    | some t =>
      match (ir.predicate t).body with
      | .mod _ _ L _ real =>
        match real.grouped, macUnits? L with
        | some _, some u => (u.powers :: ir.exprNodes u.operand, [])
        | _, _ => ([], [])
      | _ => ([], [])
    | none =>
      match ir.digitsOwner? v with
      | some t =>
        match (ir.predicate t).body with
        | .mod _ _ L _ real =>
          match real.grouped, macUnits? L with
          | some _, some u => (u.powers :: ir.exprNodes u.operand, [])
          | _, _ => ([], [])
        | _ => ([], [])
      | none =>
        match ir.digitsAccOwner? v with
        | some t =>
          match (ir.predicate t).body with
          | .mod _ _ L _ _ => (ir.exprNodes L, [])
          | _ => ([], [])
        | none =>
          match ir.lowDigitOwner? v with
          | some tj =>
            match (ir.predicate tj.1).body with
            | .mod _ _ L _ _ => (ir.exprNodes L, [])
            | _ => ([], [])
          | none => ([], [])

/-- **A generator reads only its inputs** (`genInputs`). -/
theorem genSrc_congr_inputs {e e' : ir.Env I} {v : ℕ}
    (hr : ∀ w ∈ (ir.genInputs v).1, ir.reader e w = ir.reader e' w)
    (hc : ∀ j ∈ (ir.genInputs v).2, e.chal j = e'.chal j) :
    ir.genSrc e v = ir.genSrc e' v := by
  have hcons : ∀ (u : MacUnits), (∀ w ∈ u.powers :: ir.exprNodes u.operand,
      ir.reader e w = ir.reader e' w) →
      ir.reader e u.powers = ir.reader e' u.powers ∧
        ∀ w ∈ ir.exprNodes u.operand, ir.reader e w = ir.reader e' w := fun u h =>
    ⟨h _ (List.mem_cons_self ..), fun w hw => h w (List.mem_cons_of_mem _ hw)⟩
  funext i
  unfold genInputs at hr hc
  unfold genSrc
  rcases h1 : ir.tagOwner? v with _ | p <;> simp only [h1] at hr hc ⊢
  · rcases h2 : ir.accOwner? v with _ | t <;> simp only [h2] at hr hc ⊢
    · rcases h3 : ir.digitsOwner? v with _ | t <;> simp only [h3] at hr hc ⊢
      · rcases h4 : ir.digitsAccOwner? v with _ | t <;> simp only [h4] at hr hc ⊢
        · rcases h5 : ir.lowDigitOwner? v with _ | tj <;> simp only [h5] at hr hc ⊢
          cases hb : (ir.predicate tj.1).body <;> simp only [hb] at hr hc ⊢
          rename_i L _ real
          simp only [lowDigitNat, digitsAccNat, evalIntWith_congr hr]
        · cases hb : (ir.predicate t).body <;> simp only [hb] at hr hc ⊢
          rename_i L _ real
          simp only [digitsAccNat, evalIntWith_congr hr]
      cases hb : (ir.predicate t).body <;> simp only [hb] at hr hc ⊢
      rename_i L _ real
      cases hg : real.grouped <;> cases hu : macUnits? L <;> simp only [hg, hu] at hr hc ⊢
      rename_i u
      obtain ⟨h4, h5⟩ := hcons u hr
      rw [digitNat_congr h4 h5]
    · cases hb : (ir.predicate t).body <;> simp only [hb] at hr hc ⊢
      rename_i L _ real
      cases hg : real.grouped <;> cases hu : macUnits? L <;> simp only [hg, hu] at hr hc ⊢
      rename_i u
      obtain ⟨h4, h5⟩ := hcons u hr
      rw [accNat_congr h4 h5]
  · cases hb : (ir.predicate p).body <;> simp only [hb] at hr hc ⊢
    rename_i x _ _ _ real
    rw [tagGen_congr (rd' := ir.reader e') hr, hc _ (List.mem_singleton_self _)]

/-- **A late value node has kind `late`.** -/
theorem kind_of_isLate {v : ℕ} (h : ir.IsLate v) : (ir.value v).kind = .late := by
  have h1 := h.1
  revert h1
  cases (ir.value v).kind <;> simp [Kind.isLate]

/-- **The honest environment reads a generated value other than a late histogram as its generator
reads it there** (`genSrc`): the honest late value is the generated value at the source environment
(`honestEnv_late_eq`), whose generator reads its inputs alike in both (`genSrc_congr_inputs`; `hin`:
they read no late value). -/
theorem reader_honestEnv_genSrc {v : ℕ} (hv : v < ir.values.length) (hl : ir.IsLate v)
    (hgen : ir.IsGenerated v) (hhist : ir.histOwner? v = none)
    (hin : ∀ w ∈ (ir.genInputs v).1, ir.NoLateRead w) {n : ℕ} (hn : n < (ir.value v).size) :
    ir.reader HE v n =
      ir.genSrc HE v n := by
  rw [reader_of_late _ (kind_of_isLate hl),
    honestEnv_late_eq hG stmtOf val SL y c π _ hv hl (hG.genNotSource ⟨⟨v, hv⟩, hl⟩ hgen)]
  simp only [genVal, if_pos hn, hhist]
  exact congrFun (genSrc_congr_inputs (fun w hw =>
    (reader_honestEnv_srcEnvL_of_noLate hG stmtOf val SL y c π (hin w hw)).symm) fun _ _ => rfl) n

/-- **The honest tag is the MAC's honest tag** (`MacTagAt`) at the honest environment: the tag's
generated value (`tagGen`, its owner the cross-field `equal` `pid`) at the source environment, which
reads the `x` operand alike (`hx`: it reads no late value). -/
theorem macTag_honest {pid dx : ℕ} {x : Expr} {dy : ℕ} {y' : Expr} {k : CrossKind}
    {real : MacRealization} (hb : (ir.predicate pid).body = .cross dx x dy y' k real)
    (htagB : ir.macTagB real = true) (hown : ir.tagOwner? real.tag = some pid)
    (hhist : ir.histOwner? real.tag = none) (hlate : ir.IsLate real.tag)
    (hx : ∀ v ∈ ir.exprNodes x, ir.NoLateRead v) :
    ir.MacTagAt (ir.reader HE)
      dx x real (castElt ((ir.honestEnv I (stmtOf y) (val y)
        (ir.genLate I hG stmtOf val SL y) c π).chal real.key 0)) := by
  have htag := htagB
  unfold macTagB at htag
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htag
  obtain ⟨⟨⟨htl, htagf⟩, htsz⟩, -⟩ := htag
  set E := HE
  have htg : (castElt (ir.reader E real.tag 0) : (I real.macField).K) =
      ir.tagGen (ir.reader E) dx x real (castElt (E.chal real.key 0)) := by
    rw [reader_honestEnv_genSrc hG stmtOf val SL y c π htl hlate (Or.inl (by rw [hown]; rfl)) hhist
      (by simpa only [genInputs, hown, hb] using hx) htsz]
    simp only [genSrc, hown, hb, if_true]
    rw [castElt_castElt_of_eq htagf.symm]
  unfold MacTagAt
  split
  · rename_i hbx
    unfold MacHHoldsAt
    rw [htg]
    simp only [tagGen, hbx]
  · rename_i bx hbx
    unfold MacTwoTagAt
    rw [htg]
    simp only [tagGen, hbx]

end HonestEnv

/-! ## A MAC with a grouped tail -/

variable (ir primeNodes) in
/-- **A MAC check over a field, checked by one tail** (compiler/mac.h), at domain `sd`, operand `sz`
and blind `sb`: where `x`'s domain hosts the MAC (`MacHostedCore`), the check over `y`'s field with the
blind `blind` (`macBlindCoreB`); where no domain hosts it (`MacTwoCore`, the other operand's
domain of characteristic above `1`; `mac_odd`: one tail per field, each a
`mod_2` in a domain of odd characteristic, `MacOddFieldOk`), the check over `x`'s field with the
blind `blindX` or the check over `y`'s field with the blind `blind`, at the values' intervals
`leafIvl`. A
hosted MAC's check reads `y` padded by zeros to `chunks · width` coordinates (`zeroPadB`). -/
def MacFieldCheck (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (k : CrossKind) (real : MacRealization)
    (sd : ℕ) (sz : Expr) (sb : ℕ) : Prop :=
  (ir.MacHostedCore pid dx x dy y k real ∧ sd = dy ∧
      ir.zeroPadB (ir.domainField dy) (real.chunks * real.width) sz y = true ∧
      real.blind = some sb ∧ ir.macBlindCoreB dy sb real = true) ∨
    (∃ b, real.blindX = some sb ∧ real.blind = some b ∧
      ir.MacTwoCore pid x y k real ∧ 1 < ir.charOf (ir.domainField dy) ∧
        ir.MacOddFieldOk (ir.leafIvl primeNodes) pid dx x sb real ∧ sd = dx ∧ sz = x) ∨
    ∃ bx, real.blindX = some bx ∧ real.blind = some sb ∧
      ir.MacTwoCore pid x y k real ∧ 1 < ir.charOf (ir.domainField dx) ∧
        ir.MacOddFieldOk (ir.leafIvl primeNodes) pid dy y sb real ∧ sd = dy ∧ sz = y

variable (ir primeNodes) in
/-- **A MAC check over a field with its tail** (compiler/mac.h): the cross-field `equal` `pid` with its MAC
realization, the check over a field that its tail performs (`MacFieldCheck`: the check over `y`'s
field for a hosted MAC, or over either field for a MAC no domain hosts), with the check's domain
`dy`, operand `y` and blind `sb`; its tail `t`, a `mod_2` whose left side is in the MAC unit form
with units `u` (the blind and the check's operand), and the facts every honest MAC needs: the owner
of the tag, a late value; the `x` operand, the cross-field `equal`'s `y` operand, the check's
operand and the powers read no late value; the blind is the tag's pad copy. The tail's realization
is either form (`GroupedMac`, `DigitsMac`). Data and properties of the program, decided per program.
-/
structure MacBase where
  /-- The cross-field `equal`. -/
  pid : ℕ
  /-- Its `x` domain (the H domain of a hosted MAC). -/
  dx : ℕ
  /-- Its `x` operand, the operand the tag is computed from. -/
  x : Expr
  /-- Its `y` domain. -/
  cdy : ℕ
  /-- Its `y` operand. -/
  cy : Expr
  /-- Its kind. -/
  k : CrossKind
  /-- Its MAC realization. -/
  real : MacRealization
  hpid : pid < ir.predicates.length
  hb : (ir.predicate pid).body = .cross dx x cdy cy k real
  /-- The check's domain. -/
  dy : ℕ
  /-- The check's operand. -/
  y : Expr
  /-- The check's blind. -/
  sb : ℕ
  hside : ir.MacFieldCheck primeNodes pid dx x cdy cy k real dy y sb
  /-- The check's domain is a domain of the program. -/
  dyLt : dy < ir.domains.length
  /-- The check's operand is well formed in its domain's field. -/
  yOk : ir.ExprOk (ir.domainField dy) y
  /-- The tail. -/
  t : ℕ
  ht : t < ir.predicates.length
  htB : ir.macTailAtB pid dy y sb real t = true
  /-- The tail's realization. -/
  realT : ModRealization
  /-- The tail's left side. -/
  L : Expr
  /-- The tail's right side. -/
  R : Expr
  hbt : (ir.predicate t).body = .mod dy 2 L R realT
  /-- The units. -/
  u : MacUnits
  hu : macUnits? L = some u
  tagOwn : ir.tagOwner? real.tag = some pid
  tagHist : ir.histOwner? real.tag = none
  tagLate : ir.IsLate real.tag
  xNoLate : ∀ v ∈ ir.exprNodes x, ir.NoLateRead v
  cyNoLate : ∀ v ∈ ir.exprNodes cy, ir.NoLateRead v
  yNoLate : ∀ v ∈ ir.exprNodes u.operand, ir.NoLateRead v
  powNoLate : ir.NoLateRead u.powers
  blindCopy : (ir.value sb).kind = .padCopy real.tag "polynomialBits"
  macChar : ir.charOf real.macField = 2

variable (ir primeNodes) in
/-- **The values' intervals the honest MAC checks read**: `leafIvl` at no value range. -/
abbrev honestIvl : ℕ → ℕ → Option Ivl := fun f v => ir.leafIvl primeNodes f v

variable (ir primeNodes) in
/-- **A MAC whose tail is a grouped `mod_2`** (compiler/mac.h with compiler/mod.h `kGrouped`): a
MAC (`MacBase`) whose tail is in the grouped form (`GroupedFormOk`) with accumulators `acc` and
quotient digits `gq`, and the facts the honest values need: the owners of the accumulators and the
digits, which are late values of their domain's field; the digits fit (`fit`: a group's sum, at most
`count · convMax`, halved, is below `T^k`); the lookups on the digits and on the final quotient have
room (`digitsRoom`, `finalRoom`). Data and properties of the program, decided per program. -/
structure GroupedMac extends ir.MacBase primeNodes where
  hgf : ir.GroupedFormOk (ir.honestIvl primeNodes) dy 2 L R realT
  /-- The grouping. -/
  G : GroupedMod
  hG : realT.grouped = some G
  /-- The accumulators. -/
  acc : ℕ
  hA : G.accumulators = some (.leaf acc)
  /-- The quotient digits. -/
  gq : ℕ
  hD : G.groupDigits = .leaf gq
  accOwn : ir.accOwner? acc = some t
  accTag : ir.tagOwner? acc = none
  accHist : ir.histOwner? acc = none
  accLt : acc < ir.values.length
  accLate : ir.IsLate acc
  accField : ir.valueField acc = ir.domainField dy
  gqOwn : ir.digitsOwner? gq = some t
  gqTag : ir.tagOwner? gq = none
  gqAcc : ir.accOwner? gq = none
  gqHist : ir.histOwner? gq = none
  gqLt : gq < ir.values.length
  gqLate : ir.IsLate gq
  gqField : ir.valueField gq = ir.domainField dy
  fit : ∀ fc ∈ G.groups, fc.2 * Conv.convMax u.width u.taps.toFinset / 2 < G.base ^ G.digitCount
  digitsRoom : ∀ p ∈ ir.predicates, ∀ d N r, p.body = .mem d [.leaf gq] (.range N) (.lookup r) →
    d = dy ∧ 0 < G.base ∧ G.base ≤ N
  finalRoom : ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
    D.beq realT.quotExpr = true → d = dy ∧ G.groups.length + 1 < 2 * N

/-- **The H predicate holds at an honest tag** (`macHPredB`; the converse of `macHHolds_of_pred`):
in characteristic `2`, where the tag is `Σ_c β^(c+1) · chunk_c(X_H)` (`MacHHoldsAt`), the predicate
`U + Σ_c r_c · Σ_i X_H[c w + i] · g_i = 0` holds, with `r_c = β^(c+1)` (`reader_powers`) and the
constants `g_i` decoding to the generator's powers (`hpow2`). -/
theorem hPred_holds_of_macHHolds (ho : ir.RefsOrdered) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (e : ir.Env I) {pid dx : ℕ} {x : Expr} {real : MacRealization} {p : ℕ}
    (hp : ir.macHPredB pid dx x real p = true) (hfx : ir.domainField dx = real.macField)
    (hmf : real.macField < ir.fields.length) (htag : ir.macTagB real = true)
    (hpow2 : ∀ j < real.width, (I real.macField).decode (2 ^ j) = (I real.macField).decode 2 ^ j)
    (htag1 : (ir.value real.tag).size = 1)
    (hH : ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0))) :
    ir.HoldsWith (ir.reader e) (ir.predicate p).body := by
  unfold macHPredB at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨⟨⟨hpl, -⟩, hch2⟩, hp⟩ := hp
  split at hp
  · rename_i d u n r w x' G z tgt hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨⟨hd, rfl⟩, rfl⟩, rfl⟩, hx⟩, hpow⟩, hgv⟩, hz⟩ := hp
    rw [hd] at hb
    rw [hb]
    have hpx := padsTo_of_zeroPadB ho hI hL (fun _ _ hk i => reader_of_constant e hk i) (hfx ▸ hmf)
      (by rw [hfx, hch2]; omega) hx
    have hH' := (macHHoldsAt_of_padsTo hpx).2 hH
    unfold macTagB at htag
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htag
    obtain ⟨⟨⟨-, htagf⟩, htsz⟩, -⟩ := htag
    have : CharP (I real.macField).K 2 := by
      have := charP_field hI hmf
      simp only [charOf] at hch2
      rwa [hch2] at this
    intro i hi
    have hi0 : i = 0 := by
      have hi' : i < (ir.value real.tag).size := by simpa [exprLen, Expr.len] using hi
      omega
    subst hi0
    apply (castElt_inj_of_eq hfx).1
    simp only [evalWith, castElt_evalE hfx]
    have hz0 : ir.evalE (ir.reader e) real.macField (.leaf z) 0 = 0 := by
      have := evalE_leaf_constAll_reader hL e hz hmf (by rw [hch2]; omega) Nat.zero_lt_one
      simpa using this
    have hap : ∀ (op : NamedOp) (E : Expr) (i : ℕ), ir.evalE (ir.reader e) real.macField (.apply op E) i =
        NamedOp.apply ir real.macField (ir.reader e) op (ir.evalE (ir.reader e) real.macField E) i :=
      fun _ _ _ => rfl
    have hmul : ∀ (E E' : Expr) (i : ℕ), ir.evalE (ir.reader e) real.macField (.mul E E') i =
        ir.evalE (ir.reader e) real.macField E i * ir.evalE (ir.reader e) real.macField E' i :=
      fun _ _ _ => rfl
    have hre : ∀ (m : IndexMap) (E : Expr) (i : ℕ),
        ir.evalE (ir.reader e) real.macField (.reindex m E) i =
          ir.evalE (ir.reader e) real.macField E (m.entry i) := fun _ _ _ => rfl
    rw [hz0]
    simp only [evalE_add, hap, hmul, hre, evalE_leaf, NamedOp.apply_sum, zero_mul, zero_add]
    have hsum : (∑ c : Fin real.chunks, (castElt (ir.reader e r c) : (I real.macField).K) *
        ∑ t : Fin real.width, ir.evalE (ir.reader e) real.macField x' (c * real.width + t) *
          ir.evalE (ir.reader e) real.macField G (c * real.width + t)) =
        ∑ c : Fin real.chunks, (castElt (e.chal real.key 0) : (I real.macField).K) ^ ((c : ℕ) + 1) *
          ir.macChunkH (ir.reader e) real.macField dx x' real.width c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [reader_powers hL e hmf (by omega) hpow c.2]
      congr 1
      simp only [macChunkH]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [evalPad_of_lt (by rw [hpx.1]; have := c.2; have := t.2; nlinarith)]
      rw [evalE_genView e hgv c.2 t.2, hpow2 t t.2, evalWith, castElt_evalE hfx, mul_comm]
    rw [hsum, ← hH']
    exact CharTwo.add_self_eq_zero _
  · cases hp

/-- **A chunk's integer convolution on bits lies in `[0, convMax]`**: its entries are naturals with
row sums at most `convMax` (`Conv.matrix_rowSum_le_convMax`) and the operand's integer readings are
bits (`hy`). -/
theorem chunkTerm_mem (rd : ir.Valuation I) {d r w : ℕ} {taps : List ℕ} {y : Expr} (hw : 0 < w)
    (i c : ℕ) (hy : ∀ j : Fin w, ir.evalIntWith rd d y (c * w + j) = 0 ∨
      ir.evalIntWith rd d y (c * w + j) = 1) :
    0 ≤ ir.chunkTerm rd d r w taps y i c hw ∧
      ir.chunkTerm rd d r w taps y i c hw ≤ Conv.convMax w taps.toFinset := by
  have hrow := Conv.matrix_rowSum_le_convMax taps.toFinset
    (NamedOp.macRb_le_one ir rd r w c) ⟨i % w, Nat.mod_lt _ hw⟩
  unfold chunkTerm
  constructor
  · refine Finset.sum_nonneg fun j _ => ?_
    rcases hy j with h | h <;> rw [h] <;> positivity
  · calc ∑ j : Fin w, (Conv.matrix taps.toFinset (NamedOp.macRb ir rd r w c)
          ⟨i % w, Nat.mod_lt _ hw⟩ j : ℤ) * ir.evalIntWith rd d y (c * w + j)
        ≤ ∑ j : Fin w, (Conv.matrix taps.toFinset (NamedOp.macRb ir rd r w c)
          ⟨i % w, Nat.mod_lt _ hw⟩ j : ℤ) :=
          Finset.sum_le_sum fun j _ => by
            rcases hy j with h | h <;> rw [h] <;> simp
      _ ≤ _ := by exact_mod_cast hrow

/-- **A group's accumulator on bits** is the natural of its integer sum, at most
`count · convMax`. -/
theorem groupAcc_eq (rd : ir.Valuation I) {d : ℕ} {u : MacUnits} (hw : 0 < u.width) (fc : ℕ × ℕ)
    (i : ℕ) (hy : ∀ c < fc.2, ∀ j : Fin u.width,
      ir.evalIntWith rd d u.operand ((fc.1 - 1 + c) * u.width + j) = 0 ∨
        ir.evalIntWith rd d u.operand ((fc.1 - 1 + c) * u.width + j) = 1) :
    ((ir.groupAcc rd d u fc i : ℕ) : ℤ) = ∑ c ∈ Finset.range fc.2,
        ir.chunkTerm rd d u.powers u.width u.taps u.operand i (fc.1 - 1 + c) hw ∧
      ir.groupAcc rd d u fc i ≤ fc.2 * Conv.convMax u.width u.taps.toFinset := by
  have hmem := fun c (hc : c ∈ Finset.range fc.2) =>
    chunkTerm_mem rd (r := u.powers) (taps := u.taps) hw i (fc.1 - 1 + c)
      (hy c (Finset.mem_range.1 hc))
  have hsum : ∑ c ∈ Finset.range fc.2, ir.unitTerm rd d u i (fc.1 - 1 + c) =
      ∑ c ∈ Finset.range fc.2, ir.chunkTerm rd d u.powers u.width u.taps u.operand i
        (fc.1 - 1 + c) hw := by
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [unitTerm, dif_pos hw]
  have h0 : 0 ≤ ∑ c ∈ Finset.range fc.2, ir.chunkTerm rd d u.powers u.width u.taps u.operand i
      (fc.1 - 1 + c) hw := Finset.sum_nonneg fun c hc => (hmem c hc).1
  have hle : ∑ c ∈ Finset.range fc.2, ir.chunkTerm rd d u.powers u.width u.taps u.operand i
      (fc.1 - 1 + c) hw ≤ ∑ _c ∈ Finset.range fc.2, (Conv.convMax u.width u.taps.toFinset : ℤ) :=
    Finset.sum_le_sum fun c hc => (hmem c hc).2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  unfold groupAcc
  rw [hsum]
  refine ⟨Int.toNat_of_nonneg h0, ?_⟩
  rw [Int.toNat_le]
  push_cast
  exact hle

/-- **Chunk `c` of an operand of bits in the MAC field is its indicator chunk** (`macChunkH`,
`macChunkA`): `castElt` maps `0` and `1` of the MAC field to themselves. -/
theorem macChunkH_eq_macChunkA {rd : ir.Valuation I} {f dx : ℕ} {x : Expr} {w c : ℕ}
    (hfx : ir.domainField dx = f)
    (hb : ∀ i : Fin w, ir.evalPad rd dx x (c * w + i) = 0 ∨ ir.evalPad rd dx x (c * w + i) = 1) :
    ir.macChunkH rd f dx x w c = ir.macChunkA rd f dx x w c := by
  unfold macChunkH macChunkA
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hb i with h | h <;> rw [h]
  · rw [castElt_zero, if_neg zero_ne_one]
  · rw [castElt_one_of_eq hfx, if_pos rfl]

/-- **Indicator chunks agree where the coordinates equal to `1` agree.** -/
theorem macChunkA_congr {rd : ir.Valuation I} {f d d' : ℕ} {z z' : Expr} {w c : ℕ}
    (h : ∀ i : Fin w, (ir.evalPad rd d z (c * w + i) = 1 ↔ ir.evalPad rd d' z' (c * w + i) = 1)) :
    ir.macChunkA rd f d z w c = ir.macChunkA rd f d' z' w c := by
  unfold macChunkA
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [h i]

namespace MacBase

variable (M : ir.MacBase primeNodes)

/-- **The source facts a MAC check over a field's honest values need**, at a reader `rd`: the cross-field `equal`
holds, the `x` operand and the check's operand read bits, and the check's operand's integer reading
is its indicator. -/
structure Source (rd : ir.Valuation I) : Prop where
  /-- The cross-field `equal` holds. -/
  cross : ir.HoldsWith rd (.cross M.dx M.x M.cdy M.cy M.k M.real)
  /-- The `x` operand reads bits. -/
  xbits : ∀ i < ir.exprLen M.x, ir.evalWith rd M.dx M.x i = 0 ∨ ir.evalWith rd M.dx M.x i = 1
  /-- The check's operand reads bits. -/
  ybits : ∀ j < ir.exprLen M.y, ir.evalWith rd M.dy M.y j = 0 ∨ ir.evalWith rd M.dy M.y j = 1
  /-- The check's operand's integer reading is its indicator. -/
  yint : ∀ j < ir.exprLen M.y, ir.evalIntWith rd M.dy M.y j =
    if ir.evalWith rd M.dy M.y j = 1 then 1 else 0

end MacBase

/-! ## What the generated values read -/

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

/-- **Readings agree where the environments agree on what is read**: two environments with the
same statement read a value alike when they agree on the challenges and the late values it reads
(`nodeReads`; a message also reads its late value's pad) and on the committed values it reads
(`valReads`). -/
theorem read_congr_vals {e e' : ir.Env I} (hs : e.stmt = e'.stmt) :
    ∀ n v, (∀ c, Read.chal c ∈ ir.nodeReads n v → e.chal c = e'.chal c) →
      (∀ u, Read.late u ∈ ir.nodeReads n v → e.late u = e'.late u ∧
        ((∃ w, (ir.value w).kind = .message u) → e.asg.pad u = e'.asg.pad u)) →
      (∀ u ∈ ir.valReads n v, e.asg.val u = e'.asg.val u) →
      ir.read e n v = ir.read e' n v
  | 0, _, _, _, _ => rfl
  | n + 1, v, hc, hl, ha => by
    funext i
    rcases hk : (ir.value v).kind with
      _ | ⟨_ | ⟨name, args⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, m⟩ | u | xb <;>
      simp only [nodeReads, hk] at hc hl <;> simp only [valReads, hk] at ha
    case priv => simp only [read, hk, ha v (List.mem_singleton_self _)]
    case padCopy => simp only [read, hk, ha v (List.mem_singleton_self _)]
    case bound => simp only [read, hk, ha v (List.mem_singleton_self _)]
    case late => simp only [read, hk, (hl v (List.mem_singleton_self _)).1]
    case challenge => simp only [read, hk, hc c (List.mem_singleton_self _)]
    case message =>
      simp only [read, hk, (hl u (List.mem_singleton_self _)).1,
        (hl u (List.mem_singleton_self _)).2 ⟨v, hk⟩]
    case pub.input => simp only [read, hk, hs]
    case pub.opaque =>
      simp only [read, hk, hs]
      split_ifs
      · rfl
      · have hargs : args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e n u j)) =
            args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e' n u j)) :=
          List.map_congr_left fun u hu => by
            rw [read_congr_vals hs n u (fun c h => hc c (List.mem_flatMap.2 ⟨u, hu, h⟩))
              (fun w h => hl w (List.mem_flatMap.2 ⟨u, hu, h⟩))
              (fun w h => ha w (List.mem_flatMap.2 ⟨u, hu, h⟩))]
        rw [hargs]
    case pub.expr =>
      simp only [read, hk]
      exact congrFun (evalE_congr fun u hu =>
        read_congr_vals hs n u (fun c h => hc c (List.mem_flatMap.2 ⟨u, hu, h⟩))
          (fun w h => hl w (List.mem_flatMap.2 ⟨u, hu, h⟩))
          (fun w h => ha w (List.mem_flatMap.2 ⟨u, hu, h⟩))) i
    case bits => simp only [read, hk, bitView, read_congr_vals hs n w hc hl ha]
    all_goals simp only [read, hk]

/-- **A value read whole is bound to its digits or read from the committed assignment**
(`valReads`, `asgReads`). -/
theorem isBound_or_mem_asgReads : ∀ {n v u : ℕ}, u ∈ ir.valReads n v →
    (ir.value u).kind.isBound = true ∨ u ∈ ir.asgReads n v
  | 0, _, _, h => by simp [valReads] at h
  | n + 1, v, u, h => by
    rcases hk : (ir.value v).kind with
      _ | ⟨_ | ⟨name, args⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u', m⟩ | u' | xb <;>
      simp only [valReads, hk] at h <;> simp only [asgReads, hk]
    case priv => exact .inr h
    case padCopy => exact .inr h
    case bound => exact .inl (by rw [List.mem_singleton.1 h, hk]; rfl)
    case pub.opaque =>
      obtain ⟨w, hw, hu⟩ := List.mem_flatMap.1 h
      exact (isBound_or_mem_asgReads hu).imp_right fun h' => List.mem_flatMap.2 ⟨w, hw, h'⟩
    case pub.expr =>
      obtain ⟨w, hw, hu⟩ := List.mem_flatMap.1 h
      exact (isBound_or_mem_asgReads hu).imp_right fun h' => List.mem_flatMap.2 ⟨w, hw, h'⟩
    case bits => exact isBound_or_mem_asgReads h
    all_goals simp at h

/-- **Readings agree where the environments agree on what is read**: two environments with the same
statement read a value alike when they agree on the challenges and the late values it reads
(`nodeReads`), on the committed assignment's values it reads (`asgReads`), and on the pads of the
late values it reads (a message reads its value plus its pad). -/
theorem read_congr_asg {e e' : ir.Env I} (hs : e.stmt = e'.stmt)
    (hbnd : ∀ u, (ir.value u).kind.isBound = true → e.asg.val u = e'.asg.val u) :
    ∀ n v, (∀ c, Read.chal c ∈ ir.nodeReads n v → e.chal c = e'.chal c) →
      (∀ u, Read.late u ∈ ir.nodeReads n v → e.late u = e'.late u ∧
        ((∃ w, (ir.value w).kind = .message u) → e.asg.pad u = e'.asg.pad u)) →
      (∀ u ∈ ir.asgReads n v, e.asg.val u = e'.asg.val u) →
      ir.read e n v = ir.read e' n v := fun n v hc hl ha =>
  read_congr_vals hs n v hc hl fun u hu => (isBound_or_mem_asgReads hu).elim (hbnd u) (ha u)

/-- **The honest assignment's committed values depend on the pads only through the pad copies.** -/
theorem honestAsg_val_congr (val : ir.Valuation I) {π π' : (ir.layout I).Pads} {u : ℕ}
    (h : ∀ w m, (ir.value u).kind = .padCopy w m → ir.padsOf I π w = ir.padsOf I π' w) :
    (ir.honestAsg I val π).val u = (ir.honestAsg I val π').val u := by
  have hc : ir.copyVal I val π u = ir.copyVal I val π' u := by
    funext i
    unfold copyVal
    split
    · rename_i w m hk
      rw [h w m hk]
    · rfl
  funext i
  simp only [honestAsg, ofAllCells, honestCells, ofCells, toCells]
  split
  · split
    · rw [hc]
    · rfl
  · rfl

/-- **The honest assignment's pads are the pads.** -/
theorem honestAsg_pad_congr (val : ir.Valuation I) {π π' : (ir.layout I).Pads} {u : ℕ}
    (h : ir.padsOf I π u = ir.padsOf I π' u) :
    (ir.honestAsg I val π).pad u = (ir.honestAsg I val π').pad u := by
  funext i
  simp only [honestAsg, ofAllCells, honestCells, ofCells, toCells]
  split
  · split
    · rw [h]
    · rfl
  · rfl

/-- **The honest assignment's committed values not copying a pad do not depend on the pads.** -/
theorem honestAsg_val_congr_of_not (val : ir.Valuation I) (π π' : (ir.layout I).Pads) {u : ℕ}
    (h : ∀ w m, (ir.value u).kind ≠ .padCopy w m) :
    (ir.honestAsg I val π).val u = (ir.honestAsg I val π').val u :=
  honestAsg_val_congr val fun w m hk => absurd hk (h w m)

/-- **The source environment with late values `L` reads a value alike at two challenge and pad
vectors** agreeing on the challenges it reads, on the late values it reads (`L`, `L'`) and the pads
of those its messages read, and on the pads its pad copies copy; the values bound to their digits
read no pad copy (`hbound`). -/
theorem reader_srcLate_congr (x val : ir.Valuation I) {c c' : ∀ k, (ir.layout I).Ch k}
    {π π' : (ir.layout I).Pads} (L L' : ir.Valuation I)
    (hbound : ∀ u e, (ir.value u).kind = .bound e → ∀ w ∈ ir.exprNodes e,
      ∀ w' m, (ir.value w).kind ≠ .padCopy w' m) {v : ℕ}
    (hc : ∀ j, Read.chal j ∈ ir.nodeReads ir.fuel v → ir.chalRead I c j = ir.chalRead I c' j)
    (hl : ∀ u, Read.late u ∈ ir.nodeReads ir.fuel v → L u = L' u ∧
      ((∃ w, (ir.value w).kind = .message u) → ir.padsOf I π u = ir.padsOf I π' u))
    (ha : ∀ u ∈ ir.asgReads ir.fuel v, ∀ w m, (ir.value u).kind = .padCopy w m →
      ir.padsOf I π w = ir.padsOf I π' w) :
    ir.reader { ir.srcEnv I x val c π with late := L } v =
      ir.reader { ir.srcEnv I x val c' π' with late := L' } v := by
  have hbnd : ∀ u, (ir.value u).kind.isBound = true →
      (ir.bindAsg (ir.honestAsg I val π)).val u = (ir.bindAsg (ir.honestAsg I val π')).val u := by
    intro u hu
    funext i
    simp only [bindAsg]
    split
    · rename_i e he
      refine congrFun (evalE_congr fun w hw => funext fun j => ?_) i
      simp only [committedRead]
      split
      · rfl
      · rw [honestAsg_val_congr_of_not val π π' (hbound u e he w hw)]
    · rename_i hne
      exfalso
      revert hu hne
      cases (ir.value u).kind <;> simp_all [Kind.isBound]
  refine read_congr_asg (e := { ir.srcEnv I x val c π with late := L })
    (e' := { ir.srcEnv I x val c' π' with late := L' }) rfl hbnd ir.fuel v
    (fun j hj => hc j hj) (fun u hu => ⟨(hl u hu).1, fun hm => ?_⟩) fun u hu => ?_
  · simp only [srcEnv, bindAsg]
    exact honestAsg_pad_congr val ((hl u hu).2 hm)
  · by_cases hb : (ir.value u).kind.isBound = true
    · exact hbnd u hb
    · simp only [srcEnv]
      rw [bindAsg_val_of_isBound (h := by simpa using hb),
        bindAsg_val_of_isBound (h := by simpa using hb)]
      exact honestAsg_val_congr val (ha u hu)

/-! ## The generated values read only their exported reads -/

variable (ir) in
/-- **What value `w` reads at the source environment is listed in `rs`**: its challenges, the pads
of the late values its messages read, the pads its pad copies copy, and the challenges of the
source late values it reads. -/
def SrcCovered (rs : List Read) (w : ℕ) : Prop :=
  (∀ j, Read.chal j ∈ ir.nodeReads ir.fuel w → Read.chal j ∈ rs) ∧
  (∀ u, Read.late u ∈ ir.nodeReads ir.fuel w → (∃ m, (ir.value m).kind = .message u) →
    Read.pad u ∈ rs) ∧
  (∀ u ∈ ir.asgReads ir.fuel w, ∀ w' m, (ir.value u).kind = .padCopy w' m → Read.pad w' ∈ rs) ∧
  (∀ u, Read.late u ∈ ir.nodeReads ir.fuel w → ir.IsSourceValue u →
    ∀ j, Read.chal j ∈ (ir.value u).reads → Read.chal j ∈ rs)

variable (ir) in
/-- **The values bound to their digits read no pad copy.** -/
def BoundNoCopy : Prop :=
  ∀ u e, (ir.value u).kind = .bound e → ∀ w ∈ ir.exprNodes e, ∀ w' m, (ir.value w).kind ≠ .padCopy w' m

/-- **Pads agreeing on the late values whose pads `rs` lists agree as valuations there.** -/
theorem padsOf_congr_of_mem {rs : List Read} {π π' : (ir.layout I).Pads}
    (h : ∀ u : ir.Late, Read.pad u.1 ∈ rs → π u = π' u) {w : ℕ} (hw : Read.pad w ∈ rs) :
    ir.padsOf I π w = ir.padsOf I π' w := by
  funext i
  unfold padsOf
  split
  · rename_i hc
    rw [h ⟨⟨w, hc.1⟩, hc.2.1⟩ hw]
  · rfl

/-- **The source environment reads a covered value alike** at two challenge and pad vectors
agreeing on what `rs` lists, when the late values agree where it reads them. -/
theorem reader_srcLate_covered (hb : ir.BoundNoCopy) (x val : ir.Valuation I) {rs : List Read}
    {c c' : ∀ k, (ir.layout I).Ch k} {π π' : (ir.layout I).Pads}
    (hc : ∀ j, Read.chal j ∈ rs → ir.chalRead I c j = ir.chalRead I c' j)
    (hp : ∀ u : ir.Late, Read.pad u.1 ∈ rs → π u = π' u) (L L' : ir.Valuation I) {w : ℕ}
    (hw : ir.SrcCovered rs w) (hL : ∀ u, Read.late u ∈ ir.nodeReads ir.fuel w → L u = L' u) :
    ir.reader { ir.srcEnv I x val c π with late := L } w =
      ir.reader { ir.srcEnv I x val c' π' with late := L' } w :=
  reader_srcLate_congr x val L L' hb (fun j hj => hc j (hw.1 j hj))
    (fun u hu => ⟨hL u hu, fun hm => padsOf_congr_of_mem hp (hw.2.1 u hu hm)⟩)
    fun u hu w' m hk => padsOf_congr_of_mem hp (hw.2.2.1 u hu w' m hk)

variable (ir) in
/-- **Two choices of the source program's late values agree** at each source late value whose
challenges `rs` lists. -/
def SrcLateAgree (rs : List Read) (L L' : ir.Valuation I) : Prop :=
  ∀ u, ir.IsSourceValue u → ir.IsLate u →
    (∀ j, Read.chal j ∈ (ir.value u).reads → Read.chal j ∈ rs) → L u = L' u

/-- **The source late values agree at a late value a covered value reads**, for two choices of
the source program's late values agreeing where `rs` lists their challenges. -/
theorem srcLateOf_congr_covered {rs : List Read} {L L' : ir.Valuation I}
    (hL : ir.SrcLateAgree rs L L') {w : ℕ} (hw : ir.SrcCovered rs w) {u : ℕ}
    (hu : Read.late u ∈ ir.nodeReads ir.fuel w) : ir.srcLateOf I L u = ir.srcLateOf I L' u := by
  funext i
  unfold srcLateOf
  by_cases hs : ir.IsSourceValue u
  · by_cases hl : ir.IsLate u
    · rw [hL u hs hl (hw.2.2.2 u hu hs)]
    · simp [hl]
  · simp [hs]

/-- **A late histogram reads only its needles.** -/
theorem histNat_congr {rd rd' : ir.Valuation I} {t g : ℕ}
    (h : ∀ m ∈ ir.members t g, ∀ v ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), rd v = rd' v)
    (j : ℕ) : ir.histNat rd t g j = ir.histNat rd' t g j := by
  have hN : ir.histNeedles rd (ir.chalField (ir.alphaOf t)) t g =
      ir.histNeedles rd' (ir.chalField (ir.alphaOf t)) t g := by
    unfold histNeedles
    split
    · exact List.flatMap_congr fun m hm => by
        simp only [memberVals, evalE_congr (f := ir.chalField (ir.alphaOf t))
          (h m (List.mem_of_mem_filter hm))]
    · exact groupNeedles_congr h
  unfold histNat
  rw [hN]

/-! ## The honest environment from the source environment -/

variable (ir) in
/-- **Predicate body `b` reads no generated late value** (`NoGenRead` at each value it reads). -/
def NoGenPred (b : PredBody) : Prop := ∀ w ∈ ir.predNodes b, ir.NoGenRead w

/-! ## Checkers for the program facts, through the memo tables -/

variable (ir) in
/-- **The late values that have a message**, as a set. -/
def msgSet : NatTrie Unit :=
  natSet (ir.values.filterMap fun x =>
    match x.kind with
    | .message u => some u
    | _ => none)

variable (ir) in
/-- **Whether some value of the program is the message of late value `u`** (`msgSet`). -/
def hasMessageB (u : ℕ) : Bool := (ir.msgSet.get? u).isSome

/-- **A message of `u` is a value of the program.** -/
theorem hasMessageB_of {u m : ℕ} (h : (ir.value m).kind = .message u) : ir.hasMessageB u = true := by
  unfold hasMessageB msgSet
  rw [natSet_isSome, List.mem_filterMap]
  have hm : m < ir.values.length := by
    by_contra hm
    have hd : ir.value m = default := by
      simp only [value]
      exact List.getD_eq_default _ _ (by omega)
    rw [hd] at h
    cases h
  refine ⟨ir.value m, ?_, by rw [h]⟩
  rw [value, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
  exact List.getElem_mem hm

variable (ir) in
/-- **`NoLateRead`, through the reads table.** -/
def noLateReadB (v : ℕ) : Bool :=
  (ir.readsT.getD v []).all fun r =>
    match r with
    | .late u => !decide (u < ir.values.length ∧ ir.IsLate u)
    | _ => true

theorem noLateRead_of_B (hwf : ir.WellFormed) {v : ℕ} (h : ir.noLateReadB v = true) :
    ir.NoLateRead v := by
  intro u hu
  have hm := (mem_readsT hwf v _).1 hu
  have := List.all_eq_true.1 h _ hm
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact this

variable (ir) in
/-- **`SrcCovered`, through the reads tables.** -/
def srcCoveredB (rs : List Read) (w : ℕ) : Bool :=
  decide (w < ir.values.length) &&
    (ir.readsT.getD w []).all (fun r =>
      match r with
      | .chal j => rs.contains (.chal j)
      | .late u => (!ir.hasMessageB u || rs.contains (.pad u)) &&
          (!decide (ir.IsSourceValue u) || (ir.value u).reads.all fun r =>
            match r with
            | .chal j => rs.contains (.chal j)
            | _ => true)
      | .pad _ => true) &&
    (ir.asgReadsT.getD w []).all fun u =>
      match (ir.value u).kind with
      | .padCopy w' _ => rs.contains (.pad w')
      | _ => true

theorem srcCovered_of_B (hwf : ir.WellFormed) {rs : List Read} {w : ℕ}
    (h : ir.srcCoveredB rs w = true) : ir.SrcCovered rs w := by
  unfold srcCoveredB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hw, hr⟩, ha⟩ := h
  refine ⟨fun j hj => ?_, fun u hu ⟨m, hm⟩ => ?_, fun u hu w' m hk => ?_, fun u hu hs j hj => ?_⟩
  · simpa using hr _ ((mem_readsT hwf w _).1 hj)
  · have := hr _ ((mem_readsT hwf w _).1 hu)
    simp only [Bool.and_eq_true, hasMessageB_of hm, Bool.not_true, Bool.false_or,
      List.contains_iff_mem] at this
    exact this.1
  · have := ha u ((mem_asgReadsT hwf hw u).1 hu)
    simp only [hk, List.contains_iff_mem] at this
    exact this
  · have := hr _ ((mem_readsT hwf w _).1 hu)
    simp only [Bool.and_eq_true, hs, decide_true, Bool.not_true, Bool.false_or,
      List.all_eq_true] at this
    simpa using this.2 _ hj

variable (ir) in
/-- **`BoundNoCopy`, as a check.** -/
def boundNoCopyB : Bool :=
  (List.range ir.values.length).all fun u =>
    match (ir.value u).kind with
    | .bound e => (ir.exprNodes e).all fun w =>
        match (ir.value w).kind with
        | .padCopy _ _ => false
        | _ => true
    | _ => true

theorem boundNoCopy_of_B (h : ir.boundNoCopyB = true) : ir.BoundNoCopy := by
  intro u e he w hw w' m hk
  have hu : u < ir.values.length := by
    by_contra hu
    have hd : ir.value u = default := by
      simp only [value]
      exact List.getD_eq_default _ _ (by omega)
    rw [hd] at he
    cases he
  have := List.all_eq_true.1 h u (List.mem_range.2 hu)
  simp only [he, List.all_eq_true] at this
  have := this w hw
  simp [hk] at this

variable (ir) in
/-- **`GroupedMac.digitsRoom`, as a check**: every lookup of the single record `gq` into a range
`[0, N)` is of domain `dy` with `0 < base ≤ N`. -/
def digitsRoomB (gq dy base : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [.leaf g] (.range N) (.lookup _) => !(g == gq) || (d == dy && decide (0 < base) && decide (base ≤ N))
    | _ => true

theorem digitsRoom_of_B {gq dy base : ℕ} (h : ir.digitsRoomB gq dy base = true) :
    ∀ p ∈ ir.predicates, ∀ d N r, p.body = .mem d [.leaf gq] (.range N) (.lookup r) →
      d = dy ∧ 0 < base ∧ base ≤ N := by
  intro p hp d N r hb
  have := List.all_eq_true.1 h p hp
  simp only [hb, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

variable (ir) in
/-- **`GroupedMac.finalRoom`, as a check**: every lookup of a single record `D` with
`D.beq Q` into a range `[0, N)` is of domain `dy` with `groups + 1 < 2N`. -/
def finalRoomB (Q : Expr) (dy groups : ℕ) : Bool :=
  ir.predicates.all fun p =>
    match p.body with
    | .mem d [D] (.range N) (.lookup _) => !(D.beq Q) || (d == dy && decide (groups + 1 < 2 * N))
    | _ => true

theorem finalRoom_of_B {Q : Expr} {dy groups : ℕ} (h : ir.finalRoomB Q dy groups = true) :
    ∀ p ∈ ir.predicates, ∀ d D N r, p.body = .mem d [D] (.range N) (.lookup r) →
      D.beq Q = true → d = dy ∧ groups + 1 < 2 * N := by
  intro p hp d D N r hb hD
  have := List.all_eq_true.1 h p hp
  simp only [hb, hD, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at this
  exact this

variable (ir) in
/-- **Whether value `v` is the pad copy `m` of late value `w`**, as a check. -/
def isPadCopyB (v w : ℕ) (m : String) : Bool :=
  match (ir.value v).kind with
  | .padCopy w' m' => w' == w && m' == m
  | _ => false

theorem kind_of_isPadCopyB {v w : ℕ} {m : String} (h : ir.isPadCopyB v w m = true) :
    (ir.value v).kind = .padCopy w m := by
  unfold isPadCopyB at h
  split at h
  · rename_i w' m' hk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [hk, h.1, h.2]
  · cases h

/-- **The source environment reads a committed value as the honest values** at a coordinate
with a cell in its domain. -/
theorem reader_srcEnv_priv (x val : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) {v i : ℕ} (hk : (ir.value v).kind = .priv)
    (hd : (ir.value v).domain < ir.domains.length)
    (hc : CellKey.val v i ∈ ir.cellKeys (ir.value v).domain) :
    ir.reader (ir.srcEnv I x val c π) v i = val v i := by
  rw [reader_of_priv _ hk]
  simp only [srcEnv]
  rw [bindAsg_val_of_isBound (h := by rw [hk]; rfl), honestAsg_val hd hc]
  simp only [copyVal, hk]

variable (ir) in
/-- **Value `v` is a committed value of a domain of the program with a cell at each coordinate**,
as a check. -/
def privCellB (v : ℕ) : Bool :=
  (match (ir.value v).kind with
    | .priv => true
    | _ => false) &&
    decide (v < ir.values.length) && decide ((ir.value v).domain < ir.domains.length) &&
    ir.isCellValue (ir.value v).domain v

theorem kind_of_privCellB {v : ℕ} (h : ir.privCellB v = true) : (ir.value v).kind = .priv := by
  unfold privCellB at h
  simp only [Bool.and_eq_true] at h
  have h1 := h.1.1.1
  revert h1
  cases (ir.value v).kind <;> simp

/-- **The source environment reads a checked committed value as the honest values**
(`reader_srcEnv_priv` at `privCellB`). -/
theorem reader_srcEnv_of_privCellB (x val : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) {v i : ℕ} (h : ir.privCellB v = true) (hi : i < (ir.value v).size) :
    ir.reader (ir.srcEnv I x val c π) v i = val v i := by
  have hk := kind_of_privCellB h
  unfold privCellB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact reader_srcEnv_priv x val c π hk h.1.2 ((ir.mem_cellKeys_val).2 ⟨h.1.1.2, h.2, hi⟩)

/-- **The source environment with late values reads a checked committed value as the honest
values** (`reader_srcEnv_of_privCellB`). -/
theorem reader_srcEnvL_of_privCellB (x val L : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) {v i : ℕ} (h : ir.privCellB v = true) (hi : i < (ir.value v).size) :
    ir.reader (ir.srcEnvL I x val L c π) v i = val v i := by
  have hk := kind_of_privCellB h
  have h' := reader_srcEnv_of_privCellB x val c π h hi
  rw [reader_of_priv _ hk] at h' ⊢
  exact h'

variable (ir) in
/-- **Value `v` is the bit view `sel` of value `w`**, as a check. -/
def isBitsB (v w : ℕ) (sel : IndexMap) : Bool :=
  match (ir.value v).kind with
  | .bits w' sel' => w' == w && sel' == sel
  | _ => false

theorem kind_of_isBitsB {v w : ℕ} {sel : IndexMap} (h : ir.isBitsB v w sel = true) :
    (ir.value v).kind = .bits w sel := by
  unfold isBitsB at h
  split at h
  · rename_i w' sel' hk
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [hk, h.1, h.2]
  · cases h

/-- **The source environment reads a bit view of a checked committed value** as the bits of the
honest words. -/
theorem reader_srcEnv_bits (x val : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) {v w i : ℕ} {sel : IndexMap} (hv : ir.isBitsB v w sel = true)
    (hw : ir.privCellB w = true)
    (hs : sel.entry (i / ((ir.value v).size / sel.size)) < (ir.value w).size) :
    ir.reader (ir.srcEnv I x val c π) v i = (I (ir.valueField v)).ofBool ((I (ir.valueField w)).coord
      ((ir.value w).type.nodeName.getD "") (val w (sel.entry (i / ((ir.value v).size /
        sel.size)))) (i % ((ir.value v).size / sel.size))) := by
  rw [reader_of_bits_of_priv _ (kind_of_isBitsB hv) (kind_of_privCellB hw),
    ← reader_of_priv _ (kind_of_privCellB hw), reader_srcEnv_of_privCellB x val c π hw hs]

variable (ir) in
/-- **The environment `e` reads the checked committed values of field `f` as `val`**
(`privCellB`), at their coordinates. The source environment does
(`reader_srcEnv_of_privCellB`); so does an environment read through a renaming of one
(`RealizedProgram.pullEnv`), which is how the facts of a program's part transfer to a program holding it. -/
def ReadsCells (f : ℕ) (e : ir.Env I) (val : ir.Valuation I) : Prop :=
  ∀ ⦃v i : ℕ⦄, ir.privCellB v = true → ir.valueField v = f → i < (ir.value v).size →
    ir.reader e v i = val v i

/-- **A bit view of a checked committed value** reads the bits of the values `val` the
environment reads. -/
theorem ReadsCells.reader_bits {f : ℕ} {e : ir.Env I} {val : ir.Valuation I}
    (hr : ir.ReadsCells f e val) {v w i : ℕ} {sel : IndexMap} (hv : ir.isBitsB v w sel = true)
    (hw : ir.privCellB w = true) (hf : ir.valueField w = f)
    (hs : sel.entry (i / ((ir.value v).size / sel.size)) < (ir.value w).size) :
    ir.reader e v i = (I (ir.valueField v)).ofBool ((I (ir.valueField w)).coord
      ((ir.value w).type.nodeName.getD "") (val w (sel.entry (i / ((ir.value v).size /
        sel.size)))) (i % ((ir.value v).size / sel.size))) := by
  rw [reader_of_bits_of_priv _ (kind_of_isBitsB hv) (kind_of_privCellB hw),
    ← reader_of_priv _ (kind_of_privCellB hw), hr hw hf hs]

/-- **The source environment reads a pad copy as its map of the pad**, at a coordinate with a
cell. -/
theorem reader_srcEnv_padCopy (x val : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) {v u i : ℕ} {m : String} (hk : (ir.value v).kind = .padCopy u m)
    (hd : (ir.value v).domain < ir.domains.length)
    (hc : CellKey.val v i ∈ ir.cellKeys (ir.value v).domain) :
    ir.reader (ir.srcEnv I x val c π) v i =
      (I (ir.valueField v)).ofBool (I.padCopyBit m (ir.padsOf I π u 0) i) := by
  rw [reader_of_padCopy _ hk]
  simp only [srcEnv]
  rw [bindAsg_val_of_isBound (h := by rw [hk]; rfl), honestAsg_val hd hc]
  simp only [copyVal, hk]

/-- **The source environment with late values reads a pad copy as the copied pad's bits**
(`reader_srcEnv_padCopy`). -/
theorem reader_srcEnvL_padCopy (x val L : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) {v u i : ℕ} {m : String} (hk : (ir.value v).kind = .padCopy u m)
    (hd : (ir.value v).domain < ir.domains.length)
    (hc : CellKey.val v i ∈ ir.cellKeys (ir.value v).domain) :
    ir.reader (ir.srcEnvL I x val L c π) v i =
      (I (ir.valueField v)).ofBool (I.padCopyBit m (ir.padsOf I π u 0) i) := by
  have h' := reader_srcEnv_padCopy x val c π hk hd hc
  rw [reader_of_padCopy _ hk] at h' ⊢
  exact h'

end

end GordieHowe.RealizedProgram
