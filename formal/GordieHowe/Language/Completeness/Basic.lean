-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Exec

@[expose] public section

/-!
# GordieHowe: completeness certificates, the generators

The honest prover of a realized program extends an execution of the source program by the values
the realizations add (`lem:core-red` (2)). A **completeness certificate** names, for every value,
the generator that computes it (`GordieHowe.RealizedProgram.Gen`), so the honest values dispatch on
the certificate and nothing is searched (`CERTIFICATE_REPRESENTATION.md`, C):

* **the generators** (`GordieHowe.RealizedProgram.Gen`): the execution's own value (`source`), a
  lookup digit, a committed digit of a quotient, a transformed value, a static histogram (the
  committed generators); a MAC tag, a grouped tail's accumulators and quotient digits, an ungrouped
  digit tail's accumulator and lower digits, a late histogram (the late generators); `none` for a
  value the semantics fixes (statement, constant, challenge, message, bound value, pad copy);
* **the honest committed values** (`GordieHowe.RealizedProgram.genCommitted`): the execution's
  phase-`0` values at the source values; the committed generators read the environment of the
  execution (`withGens`), a static histogram reads it with the lookup digits (`genCommitted`);
* **the honest late values** (`GordieHowe.RealizedProgram.genLateOf`): the execution's late values at
  the source late values; the late generators read the source environment (`genSrcOf`), a late
  histogram reads it with the other generated values as late values (`histEnvOf`).

The strata are those of `GordieHowe.RealizedProgram.genCommitted` and `GordieHowe.RealizedProgram.genVal`;
the generator formulas are theirs (`lookupDigitNat`, `commDigitNat`, `specNat`, `staticHistNat`,
`tagGen`, `accNat`, `digitNat`, `digitsAccNat`, `lowDigitNat`, `histNat`). The certificate is
untrusted: what the honest values satisfy follows from its checks
(`GordieHowe/Language/Completeness/Check.lean`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP

/-- **The generator of a value**, naming the program items it reads by id. -/
inductive Gen where
  /-- A value the semantics fixes, or that no generator computes: `0` where honest. -/
  | none
  /-- A value of the source program: the execution's. -/
  | source
  /-- Digit `j` of the record of the two-sided or digit lookup `p` (of `N − 1` minus it for the
  second set). -/
  | lookupDigit (p : ℕ) (second : Bool) (j : ℕ)
  /-- Digit `k` of the lookup `lk` of radix-`R` digit `j` of the honest quotient of `mod_q` `m`. -/
  | commDigit (m j lk k : ℕ)
  /-- The transformed value of convolution `c` of `RealizedProgram.convs`. -/
  | spec (c : ℕ)
  /-- The static histogram of group `g` of table `t`. -/
  | staticHist (t g : ℕ)
  /-- The tag of the MAC of cross-field `equal` `p`. -/
  | tag (p : ℕ)
  /-- The accumulators of the grouped `mod_q` `p`. -/
  | acc (p : ℕ)
  /-- The quotient digits of the grouped `mod_q` `p`. -/
  | quotDigit (p : ℕ)
  /-- The accumulator of the ungrouped digit-form `mod_q` `p`. -/
  | digitsAcc (p : ℕ)
  /-- Lower digit `j` of the ungrouped digit-form `mod_q` `p`. -/
  | lowDigit (p j : ℕ)
  /-- The late histogram of group `g` of table `t`. -/
  | lateHist (t g : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **The generators of a program's values**, aligned with the values. -/
abbrev Gens : Type := List Gen

/-- **The generator of value `v`** (`none` past the list). -/
def Gens.at (G : Gens) (v : ℕ) : Gen := G.getD v .none

section

variable {ir : RealizedProgram} {I : Interp}

variable (ir I) in
/-- **The phase-`0` values with the committed generators' values** at the statement `x` and the
source program's phase-`0` values `s`: `s` at the source values; a lookup digit, a committed digit
and a transformed value read in the environment of the execution at the default challenges;
`0` elsewhere. -/
def withGens (G : Gens) (x s : ir.Valuation I) : ir.Valuation I := fun v i =>
  if ir.IsSourceValue v then s v i
  else
    match G.at v with
    | .lookupDigit p sd j => (ir.lookupDigitNat (ir.reader (ir.execEnv I x s 0 (ir.chal0 I)))
        ⟨p, sd, j⟩ i : (I (ir.valueField v)).K)
    | .commDigit m j lk k => (ir.commDigitNat (ir.reader (ir.execEnv I x s 0 (ir.chal0 I)))
        ⟨m, j, lk, k⟩ i : (I (ir.valueField v)).K)
    | .spec c =>
      match ir.convs[c]? with
      | some cv => (ir.specNat (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) cv i :
          (I (ir.valueField v)).K)
      | none => 0
    | _ => 0

variable (ir I) in
/-- **The honest committed values** at the statement `x` and the source program's phase-`0` values
`s`: the committed generators' values (`withGens`), and each static histogram the counts of its
group's needles read there (`staticHistNat`), `0` past its size. -/
def genCommitted (G : Gens) (x s : ir.Valuation I) : ir.Valuation I := fun v i =>
  if ir.IsSourceValue v then s v i
  else
    match G.at v with
    | .staticHist t g =>
      if i < (ir.value v).size then
        (ir.staticHistNat (ir.reader (ir.execEnv I x (ir.withGens I G x s) 0 (ir.chal0 I))) t g i :
          (I (ir.valueField v)).K)
      else 0
    | _ => ir.withGens I G x s v i

/-- **The honest committed values at a source value** are the source program's. -/
theorem genCommitted_of_source (G : Gens) (x s : ir.Valuation I) {v : ℕ}
    (hv : ir.IsSourceValue v) : ir.genCommitted I G x s v = s v := by
  funext i
  simp only [genCommitted, hv, ite_true]

variable (ir) in
/-- **The late generators' values read from the source environment** `e`: a MAC tag (`tagGen`, at
coordinate `0`), the accumulators (`accNat`) and the quotient digits (`digitNat`) of a grouped
`mod_q`, the accumulator (`digitsAccNat`) and the lower digits (`lowDigitNat`) of an ungrouped
digit-form `mod_q`; `0` for any other generator (`genSrc` with the owners read off `G`). -/
def genSrcOf (G : Gens) (e : ir.Env I) (v i : ℕ) : (I (ir.valueField v)).K :=
  match G.at v with
  | .tag p =>
    match (ir.predicate p).body with
    | .cross dx x _ _ _ real =>
      if i = 0 then castElt (ir.tagGen (ir.reader e) dx x real (castElt (e.chal real.key 0)))
      else 0
    | _ => 0
  | .acc p =>
    match (ir.predicate p).body with
    | .mod d _ L _ real =>
      match real.grouped, macUnits? L with
      | some Gm, some u => (ir.accNat (ir.reader e) d u Gm i : (I (ir.valueField v)).K)
      | _, _ => 0
    | _ => 0
  | .quotDigit p =>
    match (ir.predicate p).body with
    | .mod d q L _ real =>
      match real.grouped, macUnits? L with
      | some Gm, some u => (ir.digitNat (ir.reader e) d q u Gm i : (I (ir.valueField v)).K)
      | _, _ => 0
    | _ => 0
  | .digitsAcc p =>
    match (ir.predicate p).body with
    | .mod d _ L _ _ => (ir.digitsAccNat (ir.reader e) d L i : (I (ir.valueField v)).K)
    | _ => 0
  | .lowDigit p j =>
    match (ir.predicate p).body with
    | .mod d q L _ real =>
      (ir.lowDigitNat (ir.reader e) d q L real.radix j i : (I (ir.valueField v)).K)
    | _ => 0
  | _ => 0

variable (ir) in
/-- **The environment the late histograms read**: the source environment `e` with its source late
values and the late generators' values other than the histograms (`genSrcOf`) as its late values,
`0` past a value's coordinates. -/
def histEnvOf (G : Gens) (e : ir.Env I) : ir.Env I :=
  { e with late := fun v i =>
      if i < (ir.value v).size then (if ir.IsSourceValue v then e.late v i else ir.genSrcOf G e v i)
      else 0 }

variable (ir) in
/-- **The late generators' values** at the source environment `e`: the late histograms (`histNat`)
read from `e` with the values `genSrcOf G e` as late values, every other value by `genSrcOf`; `0`
past a value's coordinates. -/
def genValOf (G : Gens) (e : ir.Env I) (v i : ℕ) : (I (ir.valueField v)).K :=
  if i < (ir.value v).size then
    match G.at v with
    | .lateHist t g => (ir.histNat (ir.reader (ir.histEnvOf G e)) t g i : (I (ir.valueField v)).K)
    | _ => ir.genSrcOf G e v i
  else 0

/-- **A late generator's value other than a tag is a natural.** -/
theorem genValOf_natCast (G : Gens) (e : ir.Env I) {v : ℕ} (ht : ∀ p, G.at v ≠ .tag p) (i : ℕ) :
    ∃ n : ℕ, ir.genValOf G e v i = n := by
  unfold genValOf
  split
  · split
    · exact ⟨_, rfl⟩
    · unfold genSrcOf
      split
      · rename_i p hp
        exact absurd hp (ht p)
      all_goals (repeat' split) <;> first | exact ⟨_, rfl⟩ | exact ⟨0, Nat.cast_zero.symm⟩
  · exact ⟨0, Nat.cast_zero.symm⟩

end

end GordieHowe.RealizedProgram
