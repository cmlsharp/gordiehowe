-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeForger
public import GordieHowe.Model.QROM.SimPMF

@[expose] public section

/-!
# The canonical extracted witness of a key-free forgery

A readout of the key-free forger (`kfForger`, `GordieHowe/Applications/Ring/KeyFreeForger.lean`)
sees the extraction run's registers and the measured database, but not the users' key coins or the
base component. When the forger's win (`forgerWinsKF`) is split by a condition the readout cannot
test, the split is made on one witness fixed in advance: the first witness the list extractor
(`SPBCS.dbExtractBitsList`, in the lexicographic order of the database's keys) returns that
satisfies a test `ok`.

- `kfCanon`, `kfCanon_eq_some_iff`, `kfCanon_spec`, `exists_kfCanon_eq_some`: the canonical
  witness and its characterization.
- `forgerCanonKF`, `forgerWinsKF_canon`, `simProb_forgerWinsKF_le_canon`: the canonical witness
  satisfies a goal in the extraction run; a win at a goal splits into two goals at the canonical
  witness.
- `kfCanonOut`, `simProb_forgerCanonKF_eq`: the canonical witness, the output and the first `Q`
  logged requests of an extraction run; the probability of a goal at the canonical witness is that
  of an event of their distribution.
- `forgerCanonKF_kfIns_iff`: in the forger's bridge (`kfIns`) the condition reads the output and
  logs of the extraction run's registers (`extForgery`, `extLogs`);
  `forgerCanonKF_kfIns_dropTabCW_iff`: it is invariant under dropping and reinserting the table.
-/

namespace GordieHowe

open Quantum Signature QROM RingSignature RingSignature.OracleSplit
open scoped ENNReal

namespace RingSignature.KeyFree

open GordieHowe.SPBCS IOP SPTerm RingSignature.Insider

section Canon

variable {k kN kS L e N n : ℕ} {Xb Yb : Type} [DecidableEq Xb] [DecidableEq Yb]
  {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  {B : BaseSigner Xb Yb N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} [DecidableEq X₀] (M : SPBCS Mg P X₀ k kN kS L e) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {Vr : X₀ → FullTr P τ → Bool}
  {Stmt Wit R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R]
  {rel : Stmt → Wit → Prop} [DecidableRel rel]
  {enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit} {dummyS : Stmt}
  [Inhabited M.NIProof]

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n

open Classical in
/-- **The canonical extracted witness** for the explicit statement `x₀` and the database `D`: the
first witness, read through `wit`, of the list extractor (`dbExtractBitsList`, the database's keys
in lexicographic order) that satisfies `ok`; none if there is none. It is computed by
`List.find?` over that list, with `ok` decided classically. -/
noncomputable def kfCanon {WitK W : Type} (Ext : CausalExtractor P τ X₀ WitK)
    (wit : X₀ → WitK → W) (ok : W → Prop) (x₀ : X₀) (D : DB Xq (Out k e)) : Option W :=
  ((M.dbExtractBitsList Ext x₀ D).map (wit x₀)).find? fun w => decide (ok w)

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  [Inhabited M.NIProof] in
/-- **The canonical witness is the first one satisfying `ok`**: it satisfies `ok`, and it follows
exactly the witnesses of the list extractor that fail `ok`. -/
theorem kfCanon_eq_some_iff {WitK W : Type} (Ext : CausalExtractor P τ X₀ WitK)
    (wit : X₀ → WitK → W) (ok : W → Prop) (x₀ : X₀) (D : DB Xq (Out k e)) (w : W) :
    kfCanon M Ext wit ok x₀ D = some w ↔ ok w ∧
      ∃ as bs, (M.dbExtractBitsList Ext x₀ D).map (wit x₀) = as ++ w :: bs ∧
        ∀ a ∈ as, ¬ ok a := by
  classical
  rw [kfCanon, List.find?_eq_some_iff_append]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  [Inhabited M.NIProof] in
/-- **The canonical witness is an extracted witness satisfying `ok`.** -/
theorem kfCanon_spec {WitK W : Type} (Ext : CausalExtractor P τ X₀ WitK)
    (wit : X₀ → WitK → W) (ok : W → Prop) (x₀ : X₀) (D : DB Xq (Out k e)) {w : W}
    (h : kfCanon M Ext wit ok x₀ D = some w) :
    (∃ w' ∈ M.dbExtractBits Ext x₀ D, wit x₀ w' = w) ∧ ok w := by
  classical
  obtain ⟨hok, as, bs, hl, -⟩ := (kfCanon_eq_some_iff M Ext wit ok x₀ D w).1 h
  refine ⟨?_, hok⟩
  have hm : w ∈ (M.dbExtractBitsList Ext x₀ D).map (wit x₀) := by simp [hl]
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hm
  refine ⟨w', ?_, rfl⟩
  rw [← coe_dbExtractBitsList]
  exact Multiset.mem_coe.2 hw'

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  [Inhabited M.NIProof] in
/-- **There is a canonical witness** when some extracted witness satisfies `ok`. -/
theorem exists_kfCanon_eq_some {WitK W : Type} (Ext : CausalExtractor P τ X₀ WitK)
    (wit : X₀ → WitK → W) (ok : W → Prop) (x₀ : X₀) (D : DB Xq (Out k e))
    (h : ∃ w ∈ M.dbExtractBits Ext x₀ D, ok (wit x₀ w)) :
    ∃ w, kfCanon M Ext wit ok x₀ D = some w := by
  classical
  obtain ⟨w, hw, hok⟩ := h
  rw [← coe_dbExtractBitsList] at hw
  rw [← Option.isSome_iff_exists, kfCanon, List.find?_isSome]
  exact ⟨wit x₀ w, List.mem_map_of_mem (Multiset.mem_coe.1 hw), decide_eq_true hok⟩

variable {M}

/-- **The canonical witness satisfies a goal** in one extraction run of the simulation-extraction
step, on the registers `c` and the database `D`: the canonical witness (`kfCanon`) for the
adversary's explicit statement `x₀`, at the test `ok` at the output and the first `Q` logged
requests, exists and satisfies `G` there. -/
def forgerCanonKF {SC' WitK W : Type} [Fintype SC'] [DecidableEq SC']
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (ok G : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A) Psim Q)
    (D : DB Xq (Out k e)) : Prop :=
  ∃ w, kfCanon M Ext wit
      (ok (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A).toTPKindAlg Psim Q c).1.1.work)
        ((Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
          (dummyS := dummyS) prf keys Q A).toTPKindAlg Psim Q c).1.1.logs).take Q))
      (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A).toTPKindAlg Psim Q c).1.1.work).2 D = some w ∧
    G (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A).toTPKindAlg Psim Q c).1.1.work)
      ((Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
        (dummyS := dummyS) prf keys Q A).toTPKindAlg Psim Q c).1.1.logs).take Q) w

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **A win at a goal splits at the canonical witness**: when every witness of the goal `Goal`
passes the test `ok` (`hok`), and the goal at one witness gives `G₁` or `G₂` at every witness
passing `ok` (`hsplit`), a win at `Goal` is a win of the canonical witness at `G₁` or at `G₂`. -/
theorem forgerWinsKF_canon {SC' WitK W : Type} [Fintype SC'] [DecidableEq SC']
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (Goal ok G₁ G₂ : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (hok : ∀ p rs w, Goal p rs w → ok p rs w)
    (hsplit : ∀ p rs w w', Goal p rs w → ok p rs w' → G₁ p rs w' ∨ G₂ p rs w')
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A) Psim Q)
    (D : DB Xq (Out k e))
    (h : forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
      Goal c D) :
    forgerCanonKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit ok G₁
        c D ∨
      forgerCanonKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit ok G₂
        c D := by
  obtain ⟨w, hw, hg⟩ := h
  obtain ⟨w', hw'⟩ := exists_kfCanon_eq_some M Ext wit _ _ D ⟨w, hw, hok _ _ _ hg⟩
  rcases hsplit _ _ _ _ hg (kfCanon_spec M Ext wit _ _ D hw').2 with h₁ | h₂
  · exact Or.inl ⟨w', hw', h₁⟩
  · exact Or.inr ⟨w', hw', h₂⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The forger's win at a goal is at most the canonical witness's wins at two goals**
(`forgerWinsKF_canon`), in one extraction run of the simulation-extraction step. -/
theorem simProb_forgerWinsKF_le_canon {SC' WitK W : Type} [Fintype SC'] [DecidableEq SC']
    (Qs : ∀ x, M.IOPQueries Vr x) (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins)
    (Q kq : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (Goal ok G₁ G₂ : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (hok : ∀ p rs w, Goal p rs w → ok p rs w)
    (hsplit : ∀ p rs w w', Goal p rs w → ok p rs w' → G₁ p rs w' ∨ G₂ p rs w') :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A) Psim Q kq)
        (forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
          Goal) ≤
      simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
          keys Q A) Psim Q kq)
          (forgerCanonKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
            ok G₁) +
        simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
          prf keys Q A) Psim Q kq)
          (forgerCanonKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
            ok G₂) :=
  (simProb_mono _ _ fun c D h => forgerWinsKF_canon prf keys Q A Psim Ext wit Goal ok G₁ G₂ hok
    hsplit c D h).trans (simProb_or_le _ _ _ _)

/-- **The canonical witness, the output and the logged requests of an extraction run**, on the
registers `c` and the database `D`: the canonical witness (`kfCanon`) at the test `ok`, the
adversary's output, and its first `Q` logged requests. -/
noncomputable def kfCanonOut {SC' WitK W : Type} [Fintype SC'] [DecidableEq SC']
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (ok : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A) Psim Q)
    (D : DB Xq (Out k e)) : Option W × (Frg × X₀) × List (MUR ⊕ R) :=
  (kfCanon M Ext wit
      (ok (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A).toTPKindAlg Psim Q c).1.1.work)
        ((Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
          (dummyS := dummyS) prf keys Q A).toTPKindAlg Psim Q c).1.1.logs).take Q))
      (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A).toTPKindAlg Psim Q c).1.1.work).2 D,
    A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
      keys Q A).toTPKindAlg Psim Q c).1.1.work,
    (Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
      (dummyS := dummyS) prf keys Q A).toTPKindAlg Psim Q c).1.1.logs).take Q)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **A goal at the canonical witness is an event of the readout's distribution**: its probability
in the extraction run is that of the canonical witness existing and satisfying `G` at the output
and the logged requests, under the distribution of `kfCanonOut` (`simPMF`). -/
theorem simProb_forgerCanonKF_eq {SC' WitK W : Type} [Fintype SC'] [DecidableEq SC']
    (Qs : ∀ x, M.IOPQueries Vr x) (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins)
    (Q kq : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (ok G : Frg × X₀ → List (MUR ⊕ R) → W → Prop) :
    simProb (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A) Psim Q kq)
        (forgerCanonKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
          ok G) =
      ((simPMF (outEquiv k e) (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
          prf keys Q A) Psim Q kq)).map fun p =>
          kfCanonOut (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit ok
            p.1.out p.2).toOuterMeasure
        {o | ∃ w, o.1 = some w ∧ G o.2.1 o.2.2 w} := by
  rw [simProb, simLaw_eq_toOuterMeasure_simPMF, PMF.toOuterMeasure_map_apply]
  rfl

end Canon

section Bridge

variable {k kN kS L e N n : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y]
  [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins]
  {B : BaseSigner (Bits (queryBits k kN kS L)) Y N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} [DecidableEq X₀] {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Stmt Wit R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R]
  (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (enc : (Fin n → B.PK) → MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit)
  (dummyS : Stmt) [Inhabited M.NIProof] {SC' : Type} [Fintype SC'] [DecidableEq SC']

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n


omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The canonical witness's goal in the forger's bridge** (`kfIns`) reads the output and the
logs of the extraction run's registers (`extForgery`, `extLogs`). -/
theorem forgerCanonKF_kfIns_iff {WitK W : Type}
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁)
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (ok G : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (x : ExtReg ((A _ p).restrictAt sp ω) (simExtChallenger Psim Q) MUR (MUResponse B.core))
    (D : DB Xq (Out k e)) :
    forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys Q
        ((A _ p).restrictAt sp ω) Psim Ext wit ok G
        (kfIns sp rel enc dummyS Aux A prf Psim Q keys p ω x) D ↔
      ∃ w, kfCanon M Ext wit (ok (extForgery x) ((Quantum.requests (extLogs x)).take Q))
          (extForgery x).2 D = some w ∧
        G (extForgery x) ((Quantum.requests (extLogs x)).take Q) w :=
  Iff.rfl

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The canonical witness's goal is invariant under dropping and reinserting the table**
(`hW` of `kfExt_le_muEufNmaProb`). -/
theorem forgerCanonKF_kfIns_dropTabCW_iff {WitK W : Type}
    (Aux : (Fin n → B.PK) → Type)
    {shA : ∀ pks, Aux pks → AlgShape Xq Y (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : ∀ pks (aux : Aux pks), AdaptiveIAlg (shA pks aux) (Frg × X₀))
    (prf : Frg → Option M.NIProof)
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC') (Q : ℕ)
    (keys : Fin n → B.KeyCoins) (p : Aux fun i => B.pk (keys i)) (ω : Xq → Y₁)
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (ok G : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (D : DB Xq (Out k e)) :
    ∀ c, (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf
        keys Q
        ((A _ p).restrictAt sp ω) Psim Ext wit ok G : SPBCS.Reg (seAlgKF (rel := rel)
          (enc := enc (fun i => B.pk (keys i)))
          (dummyS := dummyS) prf keys Q ((A _ p).restrictAt sp ω)) Psim Q → DB Xq (Out k e) → Prop)
        (kfIns sp rel enc dummyS Aux A prf Psim Q keys p ω
          (dropTabCW ((A _ p).restrictAt sp ω) (simExtChallenger Psim Q)
            (seTwoKF (Proof := M.Response b) B rel (enc (B.pk ∘ keys)) dummyS (B.pk ∘ keys) Q)
            (fun _ => keyReplyNone B keys) c)) D ↔
      (forgerCanonKF (rel := rel) (enc := enc (fun i => B.pk (keys i))) (dummyS := dummyS) prf keys
          Q
        ((A _ p).restrictAt sp ω) Psim Ext wit ok G : SPBCS.Reg (seAlgKF (rel := rel)
          (enc := enc (fun i => B.pk (keys i)))
          (dummyS := dummyS) prf keys Q ((A _ p).restrictAt sp ω)) Psim Q → DB Xq (Out k e) → Prop)
        c D :=
  fun _ => Iff.rfl

end Bridge

end RingSignature.KeyFree

end GordieHowe
