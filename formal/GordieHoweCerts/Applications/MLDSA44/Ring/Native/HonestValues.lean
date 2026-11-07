-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.HonestA
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.HonestCore
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.Frontend.Readings
public import GordieHowe.Language.Completeness.Roles

@[expose] public section

/-!
# GordieHowe: the honest values of the native ML-DSA-44 ring programs

The honest committed values of a native ML-DSA-44 ring program (`MLDSA44.Ring.Native.ROMParams`,
`MLDSA44.Ring.Native.QROMParams`; C++ `lib/gordiehowe/examples/rings/mldsa_ring_testing.h`,
`ring_witness`) on an honest input (`GordieHowe.MLDSA44.Ring.RingIn`), and the parts of its source program
the native ML-DSA program's predicates give through the renaming
(`GordieHowe.MLDSA44.Ring.Native.MldsaRingEmbed`).

* **The program facts** (`MldsaRingHonest`, decided per program): the inverse of the renaming on
  the values it holds (`inv`), the member's values outside its image, and the classes of the
  values the honest values are read through.
* **The honest values** (`honestVal`): `member.a_hat` and `member.t1` the signer's key's row
  (`keyEntry`), `member.mu` the bits of the signer's `μ` (`muBitNat` of `RingIn.mu`), the index
  bits the signer's position's; at every value the renaming holds, the native program's honest
  value at the ring input (`natVal`: domain `A`'s `aValR`, domain `H`'s core `hValCore`).
* **The native program's view** (`readsCells_pull`, `readsA_pull`): at the source environment of
  the honest values, the environment read as the native program's (`pull`) reads the native
  honest values on the held values and `0` on the other committed values, so domain `A`'s gadgets
  and domain `H`'s core hold there (`aPreds_ring`, `hPreds_core`), and by the renaming's
  correspondences (`holdsAt_pullEnv`, `holdsAt_pullEnv_body`) so do the ring's predicates
  (`aSource_holds`, `core_holds`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits RealizedProgram

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

set_option hygiene false in
local notation "vA" => MldsaRingRelation.aHat program

set_option hygiene false in
local notation "vT" => MldsaRingRelation.t1 program

set_option hygiene false in
local notation "vI" => (TableSelect.shape program).idx

set_option hygiene false in
local notation "vMu" => MldsaRingFront.muA program

/-! ## The program facts -/

/-- **The program facts of a native ML-DSA-44 ring program's honest values** (decided per
program): the inverse of the renaming on the values it holds, the member's values outside the
renaming's image and distinct, the held committed values committed in the ring program, domain
`H`'s core and domain `A`'s values held, the native bound values' expressions of held values, and
the ring's bound values read committed values and constants. -/
class MldsaRingHonest (program : RealizedProgram) [MldsaRingEmbed program] [MldsaRingRelation program]
    [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] where
  /-- The inverse of the renaming on the held values. -/
  inv : ℕ → ℕ
  /-- `inv` inverts the renaming on `ringV`. -/
  inv_val : ∀ u ∈ ringV, inv ((σ).val u) = u
  /-- The member's values are no renamed values. -/
  member_ne : ∀ u ∈ ringV, ∀ v ∈ [vA, vT, vMu, vI], (σ).val u ≠ v
  /-- The member's values are distinct. -/
  member_nodup : [vA, vT, vMu, vI].Nodup
  /-- The member's values are committed values of field `0`. -/
  memberCells : ∀ v ∈ [vA, vT, vMu, vI], program.privCellB v = true ∧ program.valueField v = 0
  /-- The held committed values are committed values of the ring program. -/
  privCell : ∀ u ∈ ringV, (nat).privCellB u = true → program.privCellB ((σ).val u) = true
  /-- Domain `H`'s core hash values are held. -/
  coreV : (69 ∈ ringV ∧ 119 ∈ ringV) ∧ ∀ p : Fin 10, (p : ℕ) ≠ 0 → ∀ t : Fin 24,
    wordsVal p t ∈ ringV
  /-- SampleInBall's cells are held. -/
  selV : ∀ u ∈ [556, 557, 560, 561, 562, 563, 564, 565], u ∈ ringV
  /-- Domain `A`'s values are held. -/
  aV : ∀ u ∈ Native.AValues ++ [57, 64, 65], u ∈ ringV
  /-- The native bound values of domain `A` read held values through no shared expression. -/
  boundExprs : ([57, 64, 65] : List ℕ).all (fun u => match ((nat).value u).kind with
    | .bound E => E.opsFree && E.directNodes.all (· ∈ ringV) && E.refs.isEmpty
    | _ => true) = true
  /-- Every value bound to its digits reads committed values and constants. -/
  bound : ∀ v < program.values.length, program.BoundOk v
  /-- The crossing's `y` has `7168` coordinates. -/
  len50 : program.exprLen (.ref 50) = 7168
  /-- Every cross-field `equal` crosses `ref 513` of domain `H` and `ref 50` of domain `A`. -/
  crossOperands : program.crossOperandsB 1 (.ref 513) 0 (.ref 50) = true

/-- **The inverse of a renaming of values on `ringV`**: the first held value renamed to `v`
(`v` itself where none is). -/
def ringInv (σ' : Renaming) (v : ℕ) : ℕ := (ringV.find? fun u => σ'.val u == v).getD v

/-! ## The honest values -/

section Values

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] [MldsaRingHonest program]
  {F0 FH : FieldInterp} [HField FH]
  [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

variable (program F0 FH) in
/-- **The native program's honest values at a ring input**: domain `A`'s (`aValR`) on
`AValues`, domain `H`'s core (`hValCore`) elsewhere. -/
-- spec-side
noncomputable def natVal (y : RingIn msgLen) (u j : ℕ) : (interp ((nat).valueField u)).K :=
  if u ∈ Native.AValues then castElt (a := 0) (aValR y F0.K u j) else hValCore nat F0 FH y u j

variable (program F0 FH) in
/-- **The honest committed values of a native ML-DSA-44 ring program** on an honest input:
`member.a_hat` the signer's `Â` (`keyEntry`, coordinates below `4096`), `member.t1` its
`NTT(2^d · t1)` (`keyEntry` from `4096`), `member.mu` the bits of the signer's `μ`, the index bits
the bits of the signer's position; at the renamed value of every held native value its native
honest value (`natVal`); `0` elsewhere (the realization's values are generated,
`RealizedProgram.genCommitted`).

Running time: one `ExpandA` and four NTTs of the signer's key, `μ = H(tr ‖ M′)`, and the time of
`natVal` (`aValR` and `hValCore`). This running time is argued here, not proved in Lean. -/
-- spec-side
noncomputable def honestVal (y : RingIn msgLen) (v j : ℕ) : (interp (program.valueField v)).K :=
  if v = vA then castElt (a := 0) (if j < 4096 then ((keyEntry y.key j : ℕ) : (interp 0).K) else 0)
  else if v = vT then castElt (a := 0) ((keyEntry y.key (4096 + j) : ℕ) : (interp 0).K)
  else if v = vMu then castElt (a := 0) ((muBitNat y.mu j : ℕ) : (interp 0).K)
  else if v = vI then castElt (a := 0) ((y.w.idx / 2 ^ j % 2 : ℕ) : (interp 0).K)
  else if MldsaRingHonest.inv program v ∈ ringV ∧ (σ).val (MldsaRingHonest.inv program v) = v then
    castElt (natVal program F0 FH y (MldsaRingHonest.inv program v) j)
  else 0

/-- A cast of a value at two equal identifiers. -/
theorem castElt_dep {I : Interp} {g : ℕ → ℕ} (f : ∀ n, (I (g n)).K) {a b c : ℕ} (h : a = b) :
    (castElt (f a) : (I c).K) = castElt (f b) := by
  subst h
  rfl

/-- **A held value's renamed value reads its native honest value.** -/
theorem honestVal_held (y : RingIn msgLen) {u : ℕ} (hu : u ∈ ringV) (j : ℕ) :
    honestVal program F0 FH y ((σ).val u) j = castElt (natVal program F0 FH y u j) := by
  have hne := MldsaRingHonest.member_ne (program := program) u hu
  have hinv := MldsaRingHonest.inv_val (program := program) u hu
  unfold honestVal
  rw [if_neg (hne _ (by simp)), if_neg (hne _ (by simp)), if_neg (hne _ (by simp)),
    if_neg (hne _ (by simp)), if_pos ⟨by rw [hinv]; exact hu, by rw [hinv]⟩]
  exact castElt_dep (I := interp) (fun n => natVal program F0 FH y n j) hinv

end Values

/-! ## The native program's view of the source environment -/

/-- **A renamed bound value is bound to the renamed expression.** -/
theorem kindCorr_bound {σ' : Renaming} {E : Expr} {k' : Kind}
    (h : σ'.kindCorr (.bound E) k' = true) : k' = .bound (σ'.expr E) := by
  cases k' <;> simp [Renaming.kindCorr, Renaming.kind?] at h ⊢
  exact (Expr.eq_of_beq h).symm

/-- **A core hash value is a round's words of permutations `1 … 9`, or `w1`'s or `μ`'s words.** -/
theorem coreHashB_cases {v : ℕ} (h : coreHashB v = true) :
    v = 69 ∨ v = 119 ∨ ∃ p : Fin 10, (p : ℕ) ≠ 0 ∧ ∃ t : Fin 24, wordsVal p t = v := by
  unfold coreHashB at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    revert h
    rcases hw : MLDSA44.wordsOwner? v with _ | ⟨p, t⟩
    · simp
    · intro hp
      refine ⟨p, by simpa using hp, t, ?_⟩
      have := List.find?_some hw
      simpa using this

/-- The core's round words are no values of domain `A`. -/
theorem wordsVal_not_aValues : ∀ p : Fin 10, ∀ t : Fin 24, wordsVal p t ∉ Native.AValues := by
  decide +kernel

/-- A cast of an expression's value between two equal fields is its value there. -/
theorem castElt_evalE_of_eq {I : Interp} {ir : RealizedProgram} {rd : ir.Valuation I} {Ex : Expr}
    {j f g : ℕ} (h : f = g) : (castElt (ir.evalE rd f Ex j) : (I g).K) = ir.evalE rd g Ex j := by
  subst h
  exact castElt_self _

section Source

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] [MldsaRingHonest program]
  {F0 FH : FieldInterp} [QField F0] [HField FH] [Native.MldsaAAlgebra nat] [hN : Native.MldsaNativeHonest nat F0 FH]
  [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MldsaHNativeData FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

/-- **A held committed value reads its native honest value** in the environment read as the
native program's. -/
theorem reader_held {u : ℕ} (hu : u ∈ ringV) (hp : (nat).privCellB u = true) {j : ℕ}
    (hj : j < ((nat).value u).size) :
    (nat).reader (pull E) u j = natVal program F0 FH y u j := by
  obtain ⟨-, -, hf, hsz, -⟩ := (MldsaRingEmbed.embedding (program := program)).vals u hu
  rw [reader_pull E hu j, reader_srcEnv_of_privCellB x _ c π
    (MldsaRingHonest.privCell u hu hp) (by rw [hsz]; exact hj), honestVal_held y hu j]
  exact castElt_castElt_of_eq hf.symm _

/-- **A committed value not held reads `0`** in the environment read as the native program's. -/
theorem reader_unheld {u : ℕ} (hu : u ∉ ringV) (hk : ((nat).value u).kind = .priv) (j : ℕ) :
    (nat).reader (pull E) u j = 0 := by
  rw [reader_of_priv _ hk]
  simp [pull, pullEnv, hu]

variable (program F0 FH) in
/-- **The native program's honest valuation** at a ring input: `natVal` on the held values, `0`
elsewhere. -/
-- spec-side
noncomputable def valN (u j : ℕ) : (interp ((nat).valueField u)).K :=
  if u ∈ ringV then natVal program F0 FH y u j else 0

/-- **The environment read as the native program's reads the native honest valuation** on its
committed values of domain `H`. -/
theorem readsCells_pull : (nat).ReadsCells 1 (pull E) (valN program F0 FH y) := by
  intro u j hp _ hj
  unfold valN
  by_cases hu : u ∈ ringV
  · rw [if_pos hu]
    exact reader_held y x c π hu hp hj
  · rw [if_neg hu]
    exact reader_unheld y x c π hu (kind_of_privCellB hp) j

/-- **The environment read as the native program's reads domain `A`'s honest values.** -/
theorem readsA_pull : ReadsA (pull E) y where
  cells u hA j hj := by
    obtain ⟨hp, hf⟩ := Native.MldsaNativeHonest.a_cells (program := nat) u hA
    have hu := MldsaRingHonest.aV (program := program) u (List.mem_append_left _ hA)
    unfold Native.rdA
    rw [evalE_leaf, reader_held y x c π hu hp hj]
    unfold natVal
    rw [if_pos hA]
    exact castElt_castElt_of_eq hf.symm _
  bound u Ex hk hu j := by
    have huV := MldsaRingHonest.aV (program := program) u (List.mem_append_right _ hu)
    have hb := List.all_eq_true.1 (MldsaRingHonest.boundExprs (program := program)) u hu
    rw [hk] at hb
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hb
    obtain ⟨⟨hop, hnodes⟩, hrefs⟩ := hb
    obtain ⟨-, hl', hf, -, -, -, hkc, -⟩ := (MldsaRingEmbed.embedding (program := program)).vals u huV
    rw [hk] at hkc
    have hk' := kindCorr_bound hkc
    have key : (nat).reader (pull E) u j =
        (nat).evalE ((nat).reader (pull E)) ((nat).valueField u) Ex j := by
      rw [reader_pull E huV j, reader_bindAsg_of_boundOk MldsaRingHonest.bound rfl hl' hk',
        evalE_rename (MldsaRingEmbed.embedding (program := program)) E hop hnodes
          (by simp [hrefs])]
      exact castElt_evalE_of_eq hf
    have hf0 : (nat).valueField u = 0 := by
      obtain ⟨h57, h64, h65, -⟩ := Native.MldsaNativeHonest.a_bound (program := nat)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    unfold Native.rdA
    rw [evalE_leaf, key]
    exact castElt_evalE_of_eq hf0

/-- **The native honest valuation at the core's hash values is `hashValCore`.** -/
theorem valN_hash : ∀ v, coreHashB v = true →
    valN program F0 FH y v = hashValCore (program := nat) (F0 := F0) (FH := FH) y v := by
  intro v hv
  obtain ⟨hw, -⟩ := MLDSA44.wordsOwner_checks
  have hmem : v ∈ ringV ∧ v ∉ Native.AValues ∧ MLDSA44.IsHashValue v := by
    rcases coreHashB_cases hv with rfl | rfl | ⟨p, hp, t, rfl⟩
    · exact ⟨(MldsaRingHonest.coreV (program := program)).1.1, by decide, by
        unfold MLDSA44.IsHashValue; simp⟩
    · exact ⟨(MldsaRingHonest.coreV (program := program)).1.2, by decide, by
        unfold MLDSA44.IsHashValue; simp⟩
    · refine ⟨(MldsaRingHonest.coreV (program := program)).2 p hp t, wordsVal_not_aValues p t, ?_⟩
      unfold MLDSA44.IsHashValue
      simp [hw p t]
  funext j
  unfold valN natVal hValCore
  rw [if_pos hmem.1, if_neg hmem.2.1, if_pos hmem.2.2]

/-- **The native honest valuation at a held value of domain `H`'s core outside the hash** is
`hValCore`. -/
theorem valN_core {v : ℕ} (hv : v ∈ [556, 557, 560, 561, 562, 563, 564, 565]) :
    valN program F0 FH y v = hValCore nat F0 FH y v := by
  have hA : v ∉ Native.AValues := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  funext j
  unfold valN natVal
  rw [if_pos (MldsaRingHonest.selV (program := program) v hv), if_neg hA]

theorem valN_556 : ∀ n < 312, castElt (b := 1) (valN program F0 FH y 556 n) = jFR (K := FH.K) y n := by
  intro n _
  obtain ⟨n7, -, -⟩ := MLDSA44.h_classes
  have h7 := (MldsaHSelHonest.sel_cells (program := nat)).2.2.2.2.2.2.2.2.2.2.1
  rw [valN_core y (by simp)]
  unfold hValCore
  rw [if_neg n7, if_pos rfl]
  exact castElt_castElt_of_eq h7.symm _

theorem valN_557 : ∀ w < 99, castElt (b := 1) (valN program F0 FH y 557 w) =
    packWord (FH := FH) (lowFR (K := FH.K) y) w := by
  intro w _
  obtain ⟨-, n8, -⟩ := MLDSA44.h_classes
  have h8 := (MldsaHSelHonest.sel_cells (program := nat)).2.2.2.1
  rw [valN_core y (by simp)]
  unfold hValCore
  rw [if_neg n8, if_neg (by decide), if_pos rfl]
  exact castElt_castElt_of_eq h8.symm _

theorem valN_mem : ∀ v, v ∈ [560, 561, 562, 563, 564, 565] → ∀ n < ((nat).value v).size,
    castElt (b := 1) (valN program F0 FH y v n) = memFR nat F0 FH y v n := by
  intro v hv n _
  obtain ⟨-, -, nm⟩ := MLDSA44.h_classes
  have hf := (MldsaHSelHonest.mem_cells (program := nat)).1 v hv
  have h7 : v ≠ 556 := by rintro rfl; simp at hv
  have h8 : v ≠ 557 := by rintro rfl; simp at hv
  rw [valN_core y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)]
  unfold hValCore
  rw [if_neg (nm v hv), if_neg h7, if_neg h8, if_pos hv]
  exact castElt_castElt_of_eq hf.2.symm _

/-- **Domain `H`'s core holds at the honest values**: ring predicate `k − 24` for every native
core predicate `k` (`48 … 270`), by the renaming (`MldsaRingEmbed.hPredCorr`,
`holdsAt_pullEnv`) at the native core's honest values (`hPreds_core`). -/
theorem core_holds {k : ℕ} (h48 : 48 ≤ k) (h270 : k ≤ 270) :
    program.HoldsAt E (program.predicate (k - 24)).body :=
  (holdsAt_pullEnv (MldsaRingEmbed.embedding (program := program)) E
    (MldsaRingEmbed.hPredCorr k h48 h270).1).2
    (hPreds_core y (readsCells_pull y x c π) (valN_hash y) (valN_556 y) (valN_557 y)
      (valN_mem y) h48 h270)

/-- **Domain `A`'s gadgets hold at the honest values**: ring predicate `predMap k` for every
native predicate `k` of `aSource`, by the renaming (`MldsaRingEmbed.aPredCorr`,
`holdsAt_pullEnv_body`) at domain `A`'s honest values (`aPreds_ring`). -/
theorem aSource_holds {k : ℕ} (hk : k ∈ aSource) :
    program.HoldsAt E (program.predicate (predMap k)).body :=
  (holdsAt_pullEnv_body (MldsaRingEmbed.embedding (program := program)) E
    (MldsaRingEmbed.aPredCorr k ((by decide : ∀ k ∈ aSource, k ∈ aPreds) k hk)).1).2
    (aPreds_ring (readsA_pull y x c π) hk)

end Source

end GordieHowe.MLDSA44.Ring.Native
