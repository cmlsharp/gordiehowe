-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Frontend.Statement
public import GordieHowe.Applications.Falcon512.NormHonest
public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.Completeness.Execution

@[expose] public section

/-!
# GordieHowe: the honest execution of a Falcon ring

The execution of the source program of a Falcon ring program (`GordieHowe.RealizedProgram.SourceExecution`), generic in the
program and its interpretation; the native rings and the carriers instantiate it.

* **The honest inputs** (`RingIn`): a ring statement `(R, m, r)` with a witness of the ring relation
  `GordieHowe.Falcon512.Ring.ringRel64`; its signature (`RingIn.normIn`: the signer's key, the coefficients of
  `HashToPoint(r ‖ m)` and the decompressed `s2`) is valid (`RingIn.valid`,
  `GordieHowe.Falcon512.Ring.Native.honestAlgebra_of_mem`).
* **The roles** (`FalconRingRoles`, per scheme): each source value of the execution is the
  spectrum, the index bits, or the cast of an honest natural of the signature (`nat r`, the
  scheme's naturals `natOf r`). The honest values `honestVal` read the roles off `roleTable`; the
  realization's values (lookup digits, static histograms) are generated (`GordieHowe.RealizedProgram.genCommitted`).
* **Generic pieces**, for every scheme: the spectrum the natural-order transform of the signer's key
  at the program's root (`specK`), the index bits the bits of the position, the membership
  (`member_honest`) and the index bits' check (`idxBool_honest`), the honest values in the prime
  subfield (`honestVal_mem`), the member checks and the execution (`GordieHowe.Falcon512.Ring.sourceExecutionOf`) from the
  scheme's source predicates.
* **The native rings** (section `Native`): the norm's naturals (`NatRole`, `GordieHowe.Falcon512.Norm.NormIn`), the
  signature equation (`sig_honest`, `c − s1 = h · s2` through the transform), the norm's and the
  encoding's source predicates (`GordieHowe.Falcon512.Norm.preds_honest`), and the execution (`sourceExecution`), from
  which `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` builds the honest strategy.
-/

namespace GordieHowe.Falcon512.Ring

open GordieHowe.Ring Native RealizedProgram
open Norm (FalconNorm FalconNormHonest NormIn NormVals)

set_option linter.unusedSectionVars false

/-! ## The honest inputs -/

variable {msgLen : ℕ} {G : Signer msgLen}

variable (G) in
/-- **An honest input of a Falcon ring**: a ring statement and a witness of the ring relation. -/
structure RingIn where
  /-- The statement. -/
  x : RStmt G
  /-- The witness: the signer's position and signature. -/
  w : RingWit (scheme G)
  /-- The pair is in the ring relation. -/
  mem : (x, w) ∈ ringRel64 G

namespace RingIn

variable (y : RingIn G)

/-- **The signature the honest values read**: the signer's key, the statement's challenge and the
decompressed `s2`. -/
def normIn : NormIn :=
  ⟨(Native.ringKey y.x y.w.idx).h, stmtChallenge y.x, witnessS2 y.w⟩

/-- **The honest signature is valid** (`Native.honestAlgebra_of_mem`). -/
theorem valid : y.normIn.Valid :=
  ⟨(honestAlgebra_of_mem y.mem).1.algebra, (honestAlgebra_of_mem y.mem).1.encoding⟩

/-- **The honest statement passes the check**: `64` keys and a successful hash. -/
theorem ringOk_x : ringOk y.x = true :=
  ringOk_iff.2 ⟨y.mem.1, (honestAlgebra_of_mem y.mem).2⟩

/-- **The signer's position is in the ring.** -/
theorem idx_lt : y.w.idx < 64 := by
  have := y.mem.2.idx_lt
  rw [y.mem.1] at this
  exact this

end RingIn

/-! ## The roles of the values -/

/-- **The roles of the honest naturals of the Falcon rings' source values**: the native rings'
`s2`, `signature.s1` and the norm's digits and carries; the carriers' `s2` and `signature.s1` (the
same naturals), the magnitudes of `s2`, their low parts, and the digits of the values bound to
their digits (the quotient, the magnitudes of `s1`, the norm). -/
inductive NatRole
  | s2 | s1 | a | sq | cc | nd | nc | D | Dc
  | mag2 | low2
  | quotD (k : ℕ)
  | mag1D (k : ℕ)
  | normD (k : ℕ)
  deriving DecidableEq

/-! ### The carriers' honest naturals -/

namespace Carrier

variable (w : NormIn)

/-- **The magnitude of `s2`'s coefficient `j`**. -/
-- spec-side
noncomputable def mag2 (j : ℕ) : ℕ := if j < 512 then w.mag (512 + j) else 0

/-- **The magnitude of `s1`'s coefficient `j`**. -/
-- spec-side
noncomputable def mag1 (j : ℕ) : ℕ := if j < 512 then w.mag j else 0

/-- **The carriers' bias** `512 (q − 1)² + 12289 · 2`, a multiple of `q` above every negative
residual `c − h s2 − s1`. -/
abbrev bias : ℕ := 77309435394

/-- **The honest quotient of coefficient `j`** of the biased signature equation
(`Emulated.Rows.honestQuotient` at the carriers' bias: `(bias + c − h s2 − s1) / q`). -/
-- spec-side
noncomputable def quot (j : ℕ) : ℕ :=
  if h : j < 512 then Emulated.Rows.honestQuotient 12289 bias
    (EmulatedAlgebraCircuit.keyCoeffs w.h) w.c (Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) w.h w.c w.s2)
    (Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2) ⟨j, h⟩ else 0

/-- **The encoding budget's value**: `50176 − Σ mag2 + Σ (mag2 mod 128)`. -/
-- spec-side
noncomputable def budget : ℕ := 50176 - ∑ i : Fin 512, (mag2 w i - mag2 w i % 128)

/-- **The squared norm**: `Σ mag1² + Σ mag2²`. -/
-- spec-side
noncomputable def squares : ℕ := ∑ i : Fin 512, mag1 w i ^ 2 + ∑ i : Fin 512, mag2 w i ^ 2

end Carrier

/-- **The honest naturals of a role** at a signature. -/
-- spec-side
noncomputable def NatRole.natOf : NatRole → NormIn → ℕ → ℕ
  | .s2, w => w.nS2
  | .s1, w => w.nS1
  | .a, w => w.nA
  | .sq, w => w.nSq
  | .cc, w => w.nCc
  | .nd, w => w.nNd
  | .nc, w => w.nNc
  | .D, w => w.nD
  | .Dc, w => w.nDc
  | .mag2, w => Carrier.mag2 w
  | .low2, w => fun j => Carrier.mag2 w j % 128
  | .quotD k, w => fun j => Carrier.quot w j / 2048 ^ k % 2048
  | .mag1D k, w => fun j => Carrier.mag1 w j / 128 ^ k % 128
  | .normD k, w => fun _ => Carrier.squares w / 2048 ^ k % 2048

/-- **The role of a source value in the honest execution**: the spectrum, the index bits, or an
honest natural of role `r`. -/
inductive VRole
  | spec
  | bit
  | nat (r : NatRole)
  deriving DecidableEq

/-- **The honest naturals of a Falcon ring program** (the native rings, the carriers): the source
values holding the casts of honest naturals of the signature with their roles (`natRoles`). -/
class FalconRingRoles (program : RealizedProgram) where
  /-- The values with honest naturals, with their roles. -/
  natRoles : List (ℕ × NatRole)

section Roles

variable (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingRoles program]

/-- **The values' roles**: the spectrum, the index bits and the scheme's honest naturals. -/
def roleTable : List (ℕ × VRole) :=
  [(FalconRingMember.spec program, .spec), (FalconRingSelect.idx program, .bit)] ++
    (FalconRingRoles.natRoles (program := program)).map (fun p => (p.1, .nat p.2))

/-- **The role of a value** (the first entry of `roleTable`). -/
def roleOf (v : ℕ) : Option (VRole) :=
  ((roleTable program).find? fun p => p.1 == v).map Prod.snd

variable {program} {I : Interp}

variable (program) in
/-- **The honest spectrum**: the natural-order transform of the signer's key at the program's
root. -/
-- spec-side
noncomputable def specK (y : RingIn G) (j : ℕ) : (I 0).K :=
  Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program))
    (fun c => ((keyEntry y.x (y.w.idx * 512 + c) : ℕ) : (I 0).K)) j

variable (program I) in
/-- **The honest source values** of an honest input, by role (`roleOf`): the spectrum, the bits of
the position and the scheme's honest naturals; `0` for every other value (the realization's values
are generated, `RealizedProgram.genCommitted`).

Running time: computing these values takes one transform of length `512` and the scheme's honest
naturals (for the native rings one negacyclic product and `O(1024)` digit operations; for the
carriers one negacyclic product and the quotients). This running time is argued here, not proved in
Lean. -/
-- spec-side
noncomputable def honestVal (y : RingIn G) (v j : ℕ) : (I (program.valueField v)).K :=
  match roleOf program v with
  | some .spec => castElt (a := 0) (if j < 512 then specK program y j else 0)
  | some .bit => castElt (a := 0) ((y.w.idx / 2 ^ j % 2 : ℕ) : (I 0).K)
  | some (.nat r) => castElt (a := 0) ((r.natOf y.normIn j : ℕ) : (I 0).K)
  | none => 0

end Roles

/-! ## The program facts of the roles -/

variable (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingRoles program] in
/-- **The program facts of the roles** (decided per program): every role of `roleTable` is its
value's (`roleOf`), whose values are committed cells. -/
class FalconRingRoleFacts : Prop where
  /-- The roles are the values'. -/
  roles : ∀ p ∈ roleTable program, roleOf program p.1 = some p.2
  /-- The roles' values are private committed cells. -/
  privCell : ∀ p ∈ roleTable program, program.privCellB p.1 = true

section Generic

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingRoles program] [FalconRingRoleFacts program]
  {I : Interp}

/-- **The honest spectrum.** -/
theorem honestVal_spec (y : RingIn G) (j : ℕ) :
    honestVal program I y (FalconRingMember.spec program) j =
      castElt (a := 0) (if j < 512 then specK program y j else 0) := by
  unfold honestVal
  rw [FalconRingRoleFacts.roles (program := program) (_, .spec) (by simp [roleTable])]

/-- **The honest index bits.** -/
theorem honestVal_bit (y : RingIn G) (j : ℕ) :
    honestVal program I y (FalconRingSelect.idx program) j =
      castElt (a := 0) ((y.w.idx / 2 ^ j % 2 : ℕ) : (I 0).K) := by
  unfold honestVal
  rw [FalconRingRoleFacts.roles (program := program) (_, .bit) (by simp [roleTable])]

/-- A value of `natRoles` has its role in `roleTable`. -/
theorem mem_roleTable_nat {v : ℕ} {r : NatRole}
    (h : (v, r) ∈ FalconRingRoles.natRoles (program := program)) : (v, VRole.nat r) ∈ roleTable program := by
  simp only [roleTable, List.mem_append, List.mem_map]
  exact Or.inr ⟨(v, r), h, rfl⟩

/-- **The honest naturals of a role.** -/
theorem honestVal_nat (y : RingIn G) {v : ℕ} {r : NatRole}
    (h : (v, r) ∈ FalconRingRoles.natRoles (program := program)) (j : ℕ) :
    honestVal program I y v j =
      castElt (a := 0) ((r.natOf y.normIn j : ℕ) : (I 0).K) := by
  unfold honestVal
  rw [FalconRingRoleFacts.roles (program := program) _ (mem_roleTable_nat h)]

/-- **The bits of a natural**: `Σ_{i ≤ t} (n / 2^i mod 2) 2^i = n mod 2^(t+1)`. -/
theorem lowBits_bits (n : ℕ) : ∀ t, lowBits (fun i => n / 2 ^ i % 2) t = n % 2 ^ (t + 1)
  | 0 => by simp [lowBits]
  | t + 1 => by
    rw [lowBits_succ, lowBits_bits n t, Nat.mod_pow_succ (k := t + 1)]
    ring

section Holds

variable [RingField (I 0) (FalconRingMember.mOne program)] [AReading (I 0)]
  (y : RingIn G) {c : ∀ k, (program.layout I).Ch k} {π : (program.layout I).Pads}

set_option hygiene false in
local notation "env" =>
  program.srcEnv I (stmtOf (program := program) (I := I) y.x) (honestVal program I y) c π

/-- **A field `equal` of domain `0` holds** where it holds coordinatewise in field `0` (the
converse of `holdsAt_equal0`). -/
theorem holdsWith_equal0_of {rd : program.Valuation I} {lhs rhs : Expr} {t : Target}
    (h : ∀ i < program.exprLen lhs, program.evalE rd 0 lhs i = program.evalE rd 0 rhs i) :
    program.HoldsWith rd (.equal 0 lhs rhs t) := fun i hi => by
  have := h i hi
  unfold RealizedProgram.evalWith
  rw [FalconRingMember.domainField0 (program := program)]
  exact this

/-- **A role's value reads its honest value** at the source environment. -/
theorem reader_env {v : ℕ} {r : VRole} (hr : (v, r) ∈ roleTable program)
    {j : ℕ} (hj : j < (program.value v).size) :
    program.reader env v j = honestVal program I y v j :=
  RealizedProgram.reader_srcEnv_of_privCellB _ _ c π (FalconRingRoleFacts.privCell (program := program) _ hr)
    hj

/-- **A value of `natRoles` of field `0` reads its honest natural** in field `0`. -/
theorem leaf_nat_env {v : ℕ} {r : NatRole}
    (hr : (v, r) ∈ FalconRingRoles.natRoles (program := program)) (hf : program.valueField v = 0) {j : ℕ}
    (hj : j < (program.value v).size) :
    program.evalE (program.reader env) 0 (.leaf v) j =
      ((r.natOf y.normIn j : ℕ) : (I 0).K) := by
  rw [RealizedProgram.evalE_leaf, reader_env y (mem_roleTable_nat hr) hj, honestVal_nat y hr]
  exact castElt_castElt_zero hf _

/-- **The honest index bits** read as bits. -/
theorem leafIdx_env {i : ℕ} (hi : i < 6) :
    program.evalE (program.reader env) 0 (.leaf (FalconRingSelect.idx program)) i =
      ((y.w.idx / 2 ^ i % 2 : ℕ) : (I 0).K) := by
  rw [RealizedProgram.evalE_leaf, reader_env y (r := .bit) (by simp [roleTable])
    (by rw [(FalconRingMember.sizes (program := program)).1]; exact hi), honestVal_bit]
  exact castElt_castElt_zero ((FalconRingMember.fields (program := program)) _ (by simp)) _

theorem bitsOf_env {i : ℕ} (hi : i < 6) : bitsOf env i = y.w.idx / 2 ^ i % 2 := by
  unfold bitsOf
  rw [if_pos hi, leafIdx_env y hi, AReading.toNat_natCast (lt_of_lt_of_le
    (Nat.mod_lt _ (by norm_num)) (by norm_num))]

/-- **The honest position**: the index bits name the signer's position. -/
theorem idxOf_env : idxOf env = y.w.idx := by
  unfold idxOf
  have h : bitsOf env = fun i => if i < 6 then y.w.idx / 2 ^ i % 2 else 0 := by
    funext i
    by_cases hi : i < 6
    · rw [bitsOf_env y hi, if_pos hi]
    · simp [bitsOf, hi]
  rw [h]
  have hl : lowBits (fun i => if i < 6 then y.w.idx / 2 ^ i % 2 else 0) 5 =
      lowBits (fun i => y.w.idx / 2 ^ i % 2) 5 := by
    unfold lowBits
    exact Finset.sum_congr rfl fun i hi => by
      dsimp only
      rw [if_pos (by simp at hi; omega)]
  rw [hl, lowBits_bits, Nat.mod_eq_of_lt (by have := y.idx_lt; norm_num; omega)]

/-- **The honest spectrum** reads the transform of the signer's key. -/
theorem specOf_env {t : ℕ} (ht : t < 512) : specOf env t = specK program y t := by
  unfold specOf
  rw [RealizedProgram.evalE_leaf, reader_env y (r := .spec) (by simp [roleTable])
    (by rw [(FalconRingMember.sizes (program := program)).2.1]; exact ht), honestVal_spec,
    castElt_castElt_zero ((FalconRingMember.fields (program := program)) _ (by simp)), if_pos ht]

/-- **`member.signer` holds on the honest values**: the spectrum's fingerprint is the signer's
digest (`evalE_memberLhs`). -/
theorem member_honest : program.HoldsAt env (program.predicate 0).body := by
  obtain ⟨t, hb⟩ := FalconRingMember.member (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [exprLen_memberLhs] at hi
  obtain rfl : i = 0 := by omega
  have hbits : ∀ i < 6, bitsOf env i ≤ 1 ∧ program.evalE (program.reader env) 0
      (.leaf (FalconRingSelect.idx program)) i = (bitsOf env i : (I 0).K) := fun i hi =>
    ⟨by rw [bitsOf_env y hi]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num)),
      by rw [bitsOf_env y hi, leafIdx_env y hi]⟩
  have hst : (env).stmt = stmtOf (program := program) (I := I) y.x := rfl
  rw [evalE_memberLhs _ hbits, evalE_zero, idxOf_env, sub_eq_zero]
  simp only [hst, ringEntry_stmtOf]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [specOf_env y m.isLt, _root_.mul_comm]
  rfl

/-- **The index bits' check holds**: the honest bits are bits. -/
theorem idxBool_honest :
    program.HoldsAt env (program.predicate (FalconRingMember.idxPred program)).body := by
  obtain ⟨t, hb⟩ := FalconRingMember.idxBool (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_leaf, (FalconRingMember.sizes (program := program)).1]
    at hi
  rw [RealizedProgram.evalE_mul, leafIdx_env y hi]
  rcases Nat.mod_two_eq_zero_or_one (y.w.idx / 2 ^ i) with h | h <;> rw [h] <;> simp

end Holds

/-! ## The honest values in the prime subfield -/

/-- **A field interpretation whose node `GF(p^1)` is a subfield** (the prime subfield of the native
fields and of the Goldilocks extensions). -/
class PrimeNode (FA : FieldInterp) : Prop where
  /-- The node `GF(p^1)` is a subfield. -/
  subfield : ∃ S : Subfield FA.K, ∀ x, x ∈ FA.node "GF(p^1)" ↔ x ∈ S

instance (priority := 100) (FA : FieldInterp) [AField FA] : PrimeNode FA :=
  ⟨⟨_, AField.node_prime (FA := FA)⟩⟩

/-- **The naturals lie in the node `GF(p^1)`** of a field identifier `0`. -/
theorem natCast_mem_prime0 [PrimeNode (I 0)] {a : ℕ} (ha : a = 0) (n : ℕ) :
    ((n : ℕ) : (I a).K) ∈ (I a).node "GF(p^1)" := by
  subst ha
  obtain ⟨S, hS⟩ := PrimeNode.subfield (FA := I 0)
  exact (hS _).2 (natCast_mem S n)

/-- **The honest spectrum lies in the node `GF(p^1)`**: a sum of products of naturals and powers of
the root (`hψ`: the root lies in the node). -/
theorem specK_mem [PrimeNode (I 0)]
    (hψ : (I 0).decode (FalconRingMember.psi program) ∈ (I 0).node "GF(p^1)") (y : RingIn G)
    (j : ℕ) : (if j < 512 then specK program y j else 0) ∈ (I 0).node "GF(p^1)" := by
  obtain ⟨S, hS⟩ := PrimeNode.subfield (FA := I 0)
  rw [hS]
  split_ifs with hj
  · unfold specK
    rw [Ops.nttNatural_apply 512 _ _ hj]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (natCast_mem _ _)
      (Subfield.pow_mem _ ((hS _).1 hψ) _)
  · exact zero_mem _

/-- A cast from field identifier `a` lies in the node where its argument does, `0` elsewhere. -/
theorem castElt_mem_of {a b : ℕ} {z : (I a).K} (hz : a = b → z ∈ (I a).node "GF(p^1)") :
    (castElt z : (I b).K) ∈ (I b).node "GF(p^1)" := by
  by_cases h : a = b
  · exact castElt_mem_node h (hz h)
  · rw [castElt_of_ne h]
    exact zero_mem _

/-- **Every honest value of a value of field `0` lies in the node `GF(p^1)`.** -/
theorem honestVal_mem [PrimeNode (I 0)]
    (hψ : (I 0).decode (FalconRingMember.psi program) ∈ (I 0).node "GF(p^1)") (y : RingIn G)
    {v : ℕ} (hf : program.valueField v = 0) (j : ℕ) :
    honestVal program I y v j ∈ (I (program.valueField v)).node "GF(p^1)" := by
  unfold honestVal
  rcases roleOf program v with _ | r
  · exact zero_mem ((I (program.valueField v)).node "GF(p^1)")
  cases r <;> dsimp only <;> refine castElt_mem_of fun h => ?_
  · exact specK_mem hψ y j
  all_goals first
    | exact natCast_mem_prime0 (h.trans hf) _

/-! ## The honest strategy from the source -/

variable (program) in
/-- **The program facts of a Falcon ring's source strategy** (decided per program): statement
bounds only on the keys and the challenge, at least `q`; no cross-field `equal`; the committed values in the node `GF(p^1)` of field `0` and no pad
copy; the node-typed values committed in the node of field `0`; the statement's two member checks,
the keys and the challenge below `q`. -/
class FalconRingSource : Prop where
  /-- The program is well formed. -/
  wf : program.WellFormed
  /-- The statement bounds: the keys and the challenge, at least `q`. -/
  bounds : ∀ vN ∈ program.declaredRanges,
    (vN.1 = FalconRingMember.ring program ∨ vN.1 = FalconRingMember.chal program) ∧ 12289 ≤ vN.2
  /-- No cross-field `equal`. -/
  noCross : ∀ q < program.predicates.length, (match (program.predicate q).body with
    | .cross _ _ _ _ _ _ => false
    | _ => true) = true
  /-- The committed values: in the node `GF(p^1)` of field `0`. -/
  cells : ∀ v < program.values.length, program.isCellValue (program.value v).domain v = true →
    (program.value v).node.map (·.name) = some "GF(p^1)" ∧ program.valueField v = 0 ∧
      program.domainField (program.value v).domain = 0
  /-- No pad copy. -/
  noPadCopy : ∀ v < program.values.length, (match (program.value v).kind with
    | .padCopy _ _ => false
    | _ => true) = true
  /-- The node-typed values are committed values of the node `GF(p^1)` in field `0`. -/
  typed : ∀ v < program.values.length, (program.value v).typeSource = .node →
    program.privCellB v = true ∧ (program.value v).type = .sub "GF(p^1)" ∧ program.valueField v = 0
  /-- The statement's member checks: the keys (`statement.ring`) and the challenge (`statement.c`)
  below `q`. -/
  checks : ∀ m ∈ program.statement.checks,
    (program.memberValue? m.member = some (FalconRingMember.ring program) ∨
      program.memberValue? m.member = some (FalconRingMember.chal program)) ∧
      m.entryBound? = some 12289

variable [FalconRingSource program]

section Source

variable [AReading (I 0)]

/-- **The honest statement passes the member checks**: the keys' coefficients and the challenge's
are below `q` (`keyEntry_lt`, `stmtChallenge_lt`). -/
theorem checks_stmtOf (x : RStmt G) :
    program.StatementOk I (stmtOf (program := program) (I := I) x) := by
  intro m hm
  obtain ⟨hv, hq⟩ := FalconRingSource.checks (program := program) m hm
  unfold RealizedProgram.MemberHolds
  rcases hv with hv | hv <;> rw [hv, hq] <;> intro i hi
  · rw [stmtOf_ring, RealizedProgram.toNat_castElt
      ((FalconRingMember.fields (program := program)) _ (by simp)).symm,
      AReading.toNat_natCast (keyEntry_lt x i)]
    exact keyEntry_lt x i
  · rw [(FalconRingMember.sizes (program := program)).2.2.2.1] at hi
    rw [stmtOf_chal x hi, RealizedProgram.toNat_castElt
      ((FalconRingMember.fields (program := program)) _ (by simp)).symm,
      AReading.toNat_natCast (stmtChallenge_lt x _)]
    exact stmtChallenge_lt x _

variable (program G I) in
/-- **The honest relation**: the program statement is the honest input's (`stmtOf`). -/
def relH : Set (program.Valuation I × RingIn G) := {p | p.1 = stmtOf p.2.x}

variable [PrimeNode (I 0)]

/-- **The node-typed values lie in their types** at the source environment of the honest values
(`RealizedProgram.SourceSatAt.types`). -/
theorem honest_types (hψ : (I 0).decode (FalconRingMember.psi program) ∈ (I 0).node "GF(p^1)")
    (y : RingIn G) (x : program.Valuation I) (c : ∀ k, (program.layout I).Ch k)
    (π : (program.layout I).Pads) (v : ℕ) (hv : v < program.values.length)
    (hts : (program.value v).typeSource = .node) (j : ℕ) (hj : j < (program.value v).size) :
    (I (program.valueField v)).InType (program.value v).type
      (program.reader (program.srcEnv I x (honestVal program I y) c π) v j) := by
  obtain ⟨hp, hty, hf⟩ := FalconRingSource.typed (program := program) v hv hts
  rw [RealizedProgram.reader_srcEnv_of_privCellB x _ c π hp hj, hty]
  exact honestVal_mem hψ y hf j

/-- **The node `GF(p^1)` of field `0` contains `1`** (`natCast_mem_prime0`). -/
theorem oneNodes : OneNodes I [(0, "GF(p^1)")] := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  simpa using natCast_mem_prime0 (I := I) rfl 1

variable (program I PN) in
/-- **The execution of a Falcon ring's source program** (`RealizedProgram.SourceExecution`): the honest values
`honestVal` (`RealizedProgram.execOf`) at the ring statement's program statement, no late value, no
completeness event; the source program accepts where the scheme's source predicates hold (`holds`)
and its node-typed values lie in their types (`honest_types`, at the root in `GF(p^1)`, `hψ`), every
other `kpriv` source value being Boolean checked (`hk`). -/
noncomputable def sourceExecutionOf (hψ : (I 0).decode (FalconRingMember.psi program) ∈ (I 0).node "GF(p^1)")
    (holds : ∀ (y : RingIn G) c π, ∀ q < program.predicates.length,
      program.inSource (program.predicate q) = true →
        program.HoldsAt (program.srcEnv I (stmtOf (program := program) (I := I) y.x)
          (honestVal program I y) c π) (program.predicate q).body)
    (hI : I.Registered program) (hL : I.Lawful program PN)
    {Gn : RealizedProgram.Gens} (R : program.CommittedFacts I Gn)
    (hbc : program.BoundNoCopy)
    (hk : program.KprivTyped) (hone : program.BoundOneMem I)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false)
    (hng : program.NoGammaTables) :
    program.SourceExecution I (relH G program I) where
  packFree _ _ _ _ _ := RealizedProgram.packFreeAt_of_noGamma hng _
  stmtOf y := stmtOf y.x
  stmt _ _ h := h
  val y := program.execOf I (honestVal program I y)
  late _ _ := 0
  respects _ _ _ _ _ _ _ := rfl
  bad _ _ _ _ := False
  δ _ := 0
  badBound _ _ _ _ _ := by simp [IOP.probUniform]
  checks x y h := by
    rw [show x = stmtOf y.x from h]
    exact checks_stmtOf _
  bounded x y h := by
    rw [show x = stmtOf y.x from h]
    intro vN hvN i hi
    obtain ⟨hv | hv, hle⟩ := FalconRingSource.bounds (program := program) vN hvN
    · rw [hv]
      refine ⟨_, lt_of_lt_of_le (keyEntry_lt y.x i) hle, ?_⟩
      rw [stmtOf_ring]
      exact RealizedProgram.castElt_natCast
        ((FalconRingMember.fields (program := program)) _ (by simp)).symm _
    · rw [hv] at hi ⊢
      rw [(FalconRingMember.sizes (program := program)).2.2.2.1] at hi
      refine ⟨_, lt_of_lt_of_le (stmtChallenge_lt y.x ⟨i, hi⟩) hle, ?_⟩
      rw [stmtOf_chal y.x hi]
      exact RealizedProgram.castElt_natCast
        ((FalconRingMember.fields (program := program)) _ (by simp)).symm _
  accepting x y hy c _ := by
    rw [show x = stmtOf y.x from hy]
    refine sourceAcceptingAtC_of_srcEnv (l := 0) (π := 0) FalconRingSource.wf hI hL R hbc hk hone
      ?_ ?_ <;> rw [RealizedProgram.srcEnvL_zero]
    · exact ⟨fun p hp _ => by
        obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
        exact holds y c 0 q hq ‹_›,
       fun v hv _ hts i hi => honest_types hψ y _ c 0 v hv hts i hi⟩
    · intro p hp _ dx x' dy y' k real hb
      obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
      have := FalconRingSource.noCross (program := program) q hq
      rw [hb] at this
      cases this
  fieldEqs _ _ _ _ _ := RealizedProgram.fieldEqsAt_of_none hff _

end Source

end Generic

/-! ## The native rings -/

section Native

variable (program : RealizedProgram) [FalconNorm program] [FalconNormHonest program]

/-- **The native values with honest naturals**: the norm's values. -/
def nativeRoles : List (ℕ × NatRole) :=
  [(FalconNorm.s2 program, .s2), (FalconNorm.s1 program, .s1),
    (FalconNorm.a program, .a), (FalconNorm.sq program, .sq), (FalconNorm.cc program, .cc),
    (FalconNorm.nd program, .nd), (FalconNorm.nc program, .nc), (FalconNorm.D program, .D),
    (FalconNorm.Dc program, .Dc)]

variable {program}

variable (program) in
/-- **The native rings' roles** (`FalconRingRoles`). -/
instance nativeRolesInst : FalconRingRoles program where
  natRoles := nativeRoles program

variable [FalconRingPowers program] [FalconRingSelect program] [FalconRingMember program]

variable (program) in
/-- **The program facts of a native Falcon ring's honest strategy** (decided per program): domain
`0` of field `0` holds the norm; the norm reads `s2` (value `9`) and `signature.s1` (value `10`);
every source predicate is the membership, the signature equation, the index bits' check or one of
the norm's and the encoding's. -/
class FalconRingHonest : Prop where
  /-- The norm's domain is `0`. -/
  dA_eq : FalconNorm.dA program = 0
  /-- The norm's field is `0`. -/
  fA_eq : FalconNorm.fA program = 0
  /-- The norm reads `s2` (value `9`) and `signature.s1` (value `10`). -/
  s2_eq : FalconNorm.s2 program = 9
  /-- `signature.s1` is value `10`. -/
  s1_eq : FalconNorm.s1 program = 10
  /-- Every source predicate is the membership, the signature equation, the index bits' check or
  one of the norm's and the encoding's. -/
  cover : ∀ q < program.predicates.length, program.inSource (program.predicate q) = true →
    q ∈ [0, 1, 14] ∨
    q ∈ [FalconNorm.p0 program, FalconNorm.p0 program + 1, FalconNorm.p0 program + 2,
      FalconNorm.p0 program + 3, FalconNorm.p0 program + 4, FalconNorm.p0 program + 5,
      FalconNorm.p0 program + 6, FalconNorm.p0 program + 7, FalconNorm.p0 program + 8,
      FalconNorm.p0 program + 9, FalconNorm.pDc program, FalconNorm.pEncB program,
      FalconNorm.pRange program, FalconNorm.pRange program + 1, FalconNorm.pRange program + 2,
      FalconNorm.pRange program + 3, FalconNorm.pRange program + 4, FalconNorm.pRange program + 5,
      FalconNorm.pHigh program, FalconNorm.pSlack program]

variable [FalconRingHonest program] [FalconRingRoleFacts program] {I : Interp}

/-- A native role's value. -/
theorem mem_nativeRoles {v : ℕ} {r : NatRole} (h : (v, r) ∈ nativeRoles program) :
    (v, r) ∈ FalconRingRoles.natRoles (program := program) := h

/-- A native role's honest value, cast from the norm's field. -/
theorem honestVal_native (y : RingIn G) {v : ℕ} {r : NatRole} (h : (v, r) ∈ nativeRoles program)
    (j : ℕ) : honestVal program I y v j =
      castElt (a := FalconNorm.fA program) ((r.natOf y.normIn j : ℕ) : (I (FalconNorm.fA program)).K) := by
  rw [honestVal_nat y (mem_nativeRoles h)]
  have hfA := FalconRingHonest.fA_eq (program := program)
  revert hfA
  generalize FalconNorm.fA program = a
  rintro rfl
  rfl

/-- **The honest values of the norm** (`Norm.NormVals`). -/
theorem normVals (y : RingIn G) : NormVals (honestVal program I y) y.normIn where
  s2 j := honestVal_native y (r := .s2) (by simp [nativeRoles]) j
  s1 j := honestVal_native y (r := .s1) (by simp [nativeRoles]) j
  a j := honestVal_native y (r := .a) (by simp [nativeRoles]) j
  sq j := honestVal_native y (r := .sq) (by simp [nativeRoles]) j
  cc j := honestVal_native y (r := .cc) (by simp [nativeRoles]) j
  nd j := honestVal_native y (r := .nd) (by simp [nativeRoles]) j
  nc j := honestVal_native y (r := .nc) (by simp [nativeRoles]) j
  D j := honestVal_native y (r := .D) (by simp [nativeRoles]) j
  Dc j := honestVal_native y (r := .Dc) (by simp [nativeRoles]) j

attribute [local instance] ringField_base

section Holds

variable [FalconRingBase program] [AField (I 0)] [AField (I (FalconNorm.fA program))]
  (y : RingIn G) {c : ∀ k, (program.layout I).Ch k} {π : (program.layout I).Pads}

set_option hygiene false in
local notation "env" =>
  program.srcEnv I (stmtOf (program := program) (I := I) y.x) (honestVal program I y) c π

/-- A native role's value of field `0` reads its honest natural in field `0`. -/
theorem leaf_native_env {v : ℕ} {r : NatRole} (hr : (v, r) ∈ nativeRoles program)
    (hf : program.valueField v = 0) {j : ℕ} (hj : j < (program.value v).size) :
    program.evalE (program.reader env) 0 (.leaf v) j = ((r.natOf y.normIn j : ℕ) : (I 0).K) :=
  leaf_nat_env y (mem_nativeRoles hr) hf hj

/-- **The signature equation holds on the honest values**: the honest `s1` is `c − h · s2`, so the
transform of `c − s1` is the signer's key's transform times the transform of `s2`
(`GordieHowe.Falcon512.NativeAlgebraCircuit.Honest.honestSignature_eq`, `DFT.negSpectrum_negacyclicConvCoeff`). -/
theorem sig_honest : program.HoldsAt env (program.predicate 1).body := by
  obtain ⟨t, hb⟩ := FalconRingBase.sig (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  refine holdsWith_equal0_of fun k hk => ?_
  rw [exprLen_sigLhs] at hk
  have hspec' := specOf_env (c := c) (π := π) y hk
  rw [evalE_sigLhs _ hk, evalE_leaf2 _ hk, hspec', sub_eq_zero]
  have hs2 : ∀ j < 512, s2Of env j = ((y.normIn.nS2 j : ℕ) : (I 0).K) := fun j hj => by
    unfold s2Of
    rw [(FalconRingBase.ids (program := program)).2.2.2.2.2.2.2]
    have h9 := FalconRingHonest.s2_eq (program := program)
    have hr : (9, NatRole.s2) ∈ nativeRoles program := by rw [← h9]; simp [nativeRoles]
    exact leaf_native_env y hr ((FalconRingBase.fields (program := program)) 9 (by simp))
      (by rw [(FalconRingBase.sizes (program := program)).1]; exact hj)
  have hs1 : ∀ j < 512, s1Of env j = ((y.normIn.nS1 j : ℕ) : (I 0).K) := fun j hj => by
    unfold s1Of
    have h10 := FalconRingHonest.s1_eq (program := program)
    have hr : (10, NatRole.s1) ∈ nativeRoles program := by rw [← h10]; simp [nativeRoles]
    exact leaf_native_env y hr ((FalconRingBase.fields (program := program)) 10 (by simp))
      (by rw [(FalconRingBase.sizes (program := program)).2.1]; exact hj)
  have hψ := Native.psiF_pow (I 0).K
  rw [nttNatural_eq_negSpectrum _ ⟨k, hk⟩, nttNatural_eq_negSpectrum _ ⟨k, hk⟩]
  have hst : (env).stmt = stmtOf (program := program) (I := I) y.x := rfl
  rw [hst]
  have hconv : (fun j : Fin falcon512.n => chalEntry (stmtOf (program := program) (I := I) y.x) j -
      s1Of env j) = LatticeCrypto.negacyclicConvCoeff
        (Native.Rows.keyVec (F := (I 0).K) y.normIn.h)
        (fun j : Fin falcon512.n => ((y.normIn.nS2 j : ℕ) : (I 0).K)) := by
    funext j
    rw [chalEntry_stmtOf, hs1 j j.isLt, NormIn.nS1_fin,
      Falcon512.NativeAlgebraCircuit.Honest.honestSignature_eq (F := (I 0).K) y.normIn.h y.normIn.c y.normIn.s2 j]
    simp only [NormIn.nS2_fin]
    unfold RingIn.normIn
    ring
  have hs2' : (fun j : Fin falcon512.n => s2Of env j) =
      fun j : Fin falcon512.n => ((y.normIn.nS2 j : ℕ) : (I 0).K) := funext fun j => hs2 j j.isLt
  have hspec : specK program y k = DFT.negSpectrum (psiF (I 0).K)
      (Native.Rows.keyVec (F := (I 0).K) y.normIn.h) ⟨k, hk⟩ := by
    unfold specK
    rw [(FalconRingBase.ids (program := program)).2.2.2.1, nttNatural_eq_negSpectrum _ ⟨k, hk⟩]
    congr 1
    funext j
    rw [keyEntry_add]
    rfl
  have e1 := congrArg (fun f => f ⟨k, hk⟩)
    (DFT.negSpectrum_negacyclicConvCoeff hψ (Native.Rows.keyVec (F := (I 0).K) y.normIn.h)
      (fun j : Fin falcon512.n => ((y.normIn.nS2 j : ℕ) : (I 0).K)))
  simp only [Pi.mul_apply] at e1
  rw [hconv, hs2', hspec]
  exact e1

/-- **Every source predicate holds at the source environment of the honest values**: the
membership, the signature equation, the index bits' check (`member_honest`, `sig_honest`,
`idxBool_honest`), the norm's and the encoding's (`Norm.preds_honest`). -/
theorem source_holds {q : ℕ} (hq : q < program.predicates.length)
    (hs : program.inSource (program.predicate q) = true) :
    program.HoldsAt env (program.predicate q).body := by
  rcases FalconRingHonest.cover (program := program) q hq hs with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact member_honest y
    · exact sig_honest y
    · have h14 : FalconRingMember.idxPred program = 14 :=
        (FalconRingBase.ids (program := program)).2.2.2.2.2.1
      have := idxBool_honest (c := c) (π := π) y
      rwa [h14] at this
  · exact Norm.preds_honest y.valid (normVals y) q h

end Holds

/-! ### The native needles -/

variable [FalconRingSource program] [FalconRingBase program]
  [AField (I 0)] [AField (I (FalconNorm.fA program))]

/-- **The native root lies in `F_q`.** -/
theorem psi_mem_native : (I 0).decode (FalconRingMember.psi program) ∈ (I 0).node "GF(p^1)" := by
  rw [AField.decode_eq]
  exact natCast_mem_prime0 rfl _

variable (program I PN) in
/-- **The execution of a native Falcon ring's source program** (`sourceExecutionOf` at the native
predicates `source_holds`). -/
noncomputable def sourceExecution (hI : I.Registered program) (hL : I.Lawful program PN)
    {Gn : RealizedProgram.Gens} (R : program.CommittedFacts I Gn)
    (hbc : program.BoundNoCopy)
    (hk : program.KprivTyped) (hone : program.BoundOneMem I)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false)
    (hng : program.NoGammaTables) :
    program.SourceExecution I (relH G program I) :=
  sourceExecutionOf program I PN psi_mem_native (fun y _ _ _ hq hs => source_holds y hq hs) hI hL R hbc hk
    hone hff hng

end Native

end GordieHowe.Falcon512.Ring
