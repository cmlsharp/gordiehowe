-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridgeProof

@[expose] public section

/-!
# The Kraus maps of the bridge's composition across the table swap

The statements `BridgeHop` and `BridgeKeeps`
(`GordieHowe/Model/Quantum/Interactive/ReqBridgeProof.lean`) for a trace-preserving adversary:
`bridgeHop`, for a relay whose outer requests are never the dummy `d₂` and a bound `T` at least the
query depth, and `bridgeKeeps`.

The proof follows the compiled circuit gate by gate.

- `WorkRel.Rel σ' σ S K`: `K.op r (σ' a) (σ b) = K.op r a b` for the columns `b` whose work register
  is in `S`, with `σ'` and `σ` permutations of the work register; `WorkRel.Keeps S K`: the nonzero
  rows of the columns in `S` are in `S`. `WorkRel.Rel.comp`: a composition along `(σ'', σ)` from
  maps along `(σ'', σ')` and `(σ', σ)`, the second keeping `S`.
- `ReprogrammedCircuit.RelAt τ w S c k σ σe`: every Kraus map of `c` keeps `S` and is along the
  current column permutation on both sides or absorbs it (along `τ` and it); a reprogrammed query
  needs the column permutation `τ` and starts the next segment with `τ` then the write `w (k + 1)`.
  `ReprogrammedCircuit.relAt_seg`, `ReprogrammedCircuit.relAt_toAlg_step`: the segments, and the
  Kraus maps of the compiled algorithm, are along `τ` and `τ` then `w i`.
- `KindAlg.relAt_fullCircBoth`: the composition's circuit with a permutation of the workspace that
  keeps the kind, and writes on the adversary's registers trivial except at the ends of the slots,
  is `RelAt` when the adversary's Kraus maps absorb the writes before them.
- `AdaptiveIAlg.tpOp_inl_entry`, `AdaptiveIAlg.tpOp_inr_inl_entry`,
  `AdaptiveIAlg.tpOp_inr_inr_of_haltOp`: the entries of the trace-preserving form's operators.
- `AdaptiveIAlg.tpOp_withStep_cntOne`, `AdaptiveIAlg.tpOp_cntOne`: the trace-preserving forms of
  `A.withStep st'` and `A` along `cntOne` when `st'` is along the permutations of `A`'s steps, and
  its case `st' = A.step`.
- `AdaptiveIAlg.drel_toTPKindAlg`, `AdaptiveIAlg.dkeeps_toTPKindAlg`: the trace-preserving form's
  steps from the adversary's steps, when the halting operators vanish.
- `afterAtTab_answerDelta`: step `j + 1` of the adversary absorbed with the empty table, after the
  request point of slot `j` with the reply `x`, reads across the table swap as the step at the table
  `tab`, when `x` is the table's reply at the count of the earlier outer requests;
  `stepTab_op_absTabSwap`, `stepTab_table`: a step across the table swap, and the table register
  kept.
- `countND_reqLog`: at the end of slot `j`, the requests of the request points before it other than
  `d₂` number the outer requests logged before slot `j` (`outerCount`).
- `ProdPerm.ctrlFst`: a controlled permutation of `P × Q` acting on `P` alone, as a permutation of
  `P`; `writeP`, `writeW`: the writes of the request points on the adversary's registers, with
  `writeV_eq` and `tabSwap_eq` the composition's write and table swap.
- `BridgeStepsOK st`: the per-step facts of steps `st` replacing the base's (trace preservation,
  the table register kept, the writes absorbed across the table swap); `dkeeps_toTP`,
  `bridgeStepsOK_toTP`: the base's steps satisfy them.
- `advKraus_tabRelAt`, `relAt_bridgeAt`, `depth_bridgeComposeAt`, `bridgeHopAt`, `bridgeKeepsAt`:
  the statements at steps `st`; `advKraus_tabRel`, `relAt_bridge`, `depth_bridgeCompose`, `bridgeHop`,
  `bridgeKeeps` their instances at the base's steps.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

namespace KrausMap

/-- **The entries of a Kraus map between two basis permutations.** -/
theorem ofPerm_comp_comp_op_apply {R ι : Type} [Fintype R]
    [Fintype ι] [DecidableEq ι] (π₂ π₁ : Equiv.Perm ι) (K : KrausMap R ι ι)
    (r : (Unit × R) × Unit) (y x : ι) :
    ((KrausMap.ofPerm π₂).comp (K.comp (KrausMap.ofPerm π₁))).op r y x =
      K.op r.1.2 (π₂.symm y) (π₁ x) := by
  change ∑ u, (KrausMap.ofPerm π₂).op r.2 y u *
    (∑ v, K.op r.1.2 u v * (KrausMap.ofPerm π₁).op r.1.1 v x) = _
  simp only [KrausMap.ofPerm_op_apply]
  rw [Finset.sum_eq_single (π₂.symm y) (fun u _ hu => by
      rw [if_neg (fun h => hu (by rw [h, Equiv.symm_apply_apply])), zero_mul]) (by simp),
    if_pos (Equiv.apply_symm_apply _ _).symm, one_mul, Finset.sum_eq_single (π₁ x)
      (fun v _ hv => by rw [if_neg hv, mul_zero]) (by simp), if_pos rfl, mul_one]

end KrausMap

/-! ### Kraus maps along permutations of the work register -/

namespace WorkRel

variable {V X Y R R₁ R₂ : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype R] [Fintype R₁] [Fintype R₂]

/-- A permutation of the work register on the query registers. -/
abbrev wq (σ : Equiv.Perm V) : Equiv.Perm (QueryReg V 1 X Y) :=
  σ.prodCongr (Equiv.refl _)

/-- **A Kraus map along permutations of the work register**: on the columns whose work register
is in `S`, the operator at the rows moved by `σ'` and the columns moved by `σ` is the operator. -/
def Rel (σ' σ : Equiv.Perm V) (S : Set V) (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) :
    Prop :=
  ∀ r a b, b.1 ∈ S → K.op r (wq σ' a) (wq σ b) = K.op r a b

/-- **A Kraus map keeps the work registers in `S`**: on the columns in `S`, its nonzero rows are
in `S`. -/
def Keeps (S : Set V) (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) : Prop :=
  ∀ r a b, b.1 ∈ S → K.op r a b ≠ 0 → a.1 ∈ S

/-- **Composition along permutations**: `K₂ ∘ K₁` along `(σ'', σ)` when `K₁` is along `(σ', σ)`
and keeps `S`, and `K₂` is along `(σ'', σ')`. -/
theorem Rel.comp {σ'' σ' σ : Equiv.Perm V} {S : Set V}
    {K₂ : KrausMap R₂ (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    {K₁ : KrausMap R₁ (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h₂ : Rel σ'' σ' S K₂) (h₁ : Rel σ' σ S K₁) (hk : Keeps S K₁) :
    Rel σ'' σ S (K₂.comp K₁) := fun r a b hb => by
  change (K₂.op r.2 * K₁.op r.1) _ _ = (K₂.op r.2 * K₁.op r.1) _ _
  rw [Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp (wq σ')]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h₁ r.1 m b hb]
  by_cases h : K₁.op r.1 m b = 0
  · rw [h, mul_zero, mul_zero]
  · rw [h₂ r.2 a m (hk r.1 m b hb h)]

/-- **A composition keeps `S`** when both maps do. -/
theorem Keeps.comp {S : Set V} {K₂ : KrausMap R₂ (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    {K₁ : KrausMap R₁ (QueryReg V 1 X Y) (QueryReg V 1 X Y)} (h₂ : Keeps S K₂) (h₁ : Keeps S K₁) :
    Keeps S (K₂.comp K₁) := fun r a b hb hne => by
  change (K₂.op r.2 * K₁.op r.1) a b ≠ 0 at hne
  rw [Matrix.mul_apply] at hne
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h₂ r.2 a m (h₁ r.1 m b hb (right_ne_zero_of_mul hm)) (left_ne_zero_of_mul hm)

/-- The identity is along every permutation on both sides. -/
theorem rel_identity (σ : Equiv.Perm V) (S : Set V) :
    Rel σ σ S (KrausMap.identity (QueryReg V 1 X Y)) := fun _ a b _ => by
  change (1 : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) _ _ = (1 : Matrix _ _ ℂ) a b
  simp only [Matrix.one_apply, (wq σ).injective.eq_iff]

/-- The identity keeps every set. -/
theorem keeps_identity (S : Set V) : Keeps S (KrausMap.identity (QueryReg V 1 X Y)) :=
  fun _ a b hb hne => by
  change (1 : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) a b ≠ 0 at hne
  by_cases h : a = b
  · exact h ▸ hb
  · exact absurd (Matrix.one_apply_ne h) hne

/-- The entries of a basis permutation as a Kraus map, on the query registers. -/
theorem ofPerm_op_apply' (π : Equiv.Perm (QueryReg V 1 X Y)) (r : Unit) (i' i : QueryReg V 1 X Y) :
    (KrausMap.ofPerm π).op r i' i = if i' = π i then 1 else 0 := by
  simp only [KrausMap.ofPerm, KrausMap.permConj, KrausMap.identity, Matrix.submatrix_apply,
    Equiv.refl_apply, Matrix.one_apply]
  exact if_congr (Equiv.symm_apply_eq π) rfl rfl

/-- A basis permutation that carries `σ` to `σ'` on `S` is along `(σ', σ)`. -/
theorem rel_ofPerm {π : Equiv.Perm (QueryReg V 1 X Y)} {σ' σ : Equiv.Perm V} {S : Set V}
    (h : ∀ b : QueryReg V 1 X Y, b.1 ∈ S → π (wq σ b) = wq σ' (π b)) :
    Rel σ' σ S (KrausMap.ofPerm π) := fun r a b hb => by
  rw [ofPerm_op_apply', ofPerm_op_apply', h b hb]
  exact if_congr (wq σ').injective.eq_iff rfl rfl

/-- A basis permutation that maps `S` into `S` keeps it. -/
theorem keeps_ofPerm {π : Equiv.Perm (QueryReg V 1 X Y)} {S : Set V}
    (h : ∀ b : QueryReg V 1 X Y, b.1 ∈ S → (π b).1 ∈ S) : Keeps S (KrausMap.ofPerm π) :=
  fun r a b hb hne => by
  rw [ofPerm_op_apply'] at hne
  split_ifs at hne with hab
  · exact hab ▸ h b hb
  · exact absurd rfl hne

/-- A permutation of the work register on the work register with the ancilla. -/
abbrev wa (σ : Equiv.Perm V) : Equiv.Perm (V × (X × Y × Bool)) :=
  σ.prodCongr (Equiv.refl _)

/-- The work registers with the ancilla whose work register is in `S`. -/
def ancSet (S : Set V) : Set (V × (X × Y × Bool)) :=
  {v | v.1 ∈ S}

/-- The entries of a Kraus map with the identity on the ancilla. -/
theorem liftAnc_op_apply (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) (r : R)
    (p' p : ReprogrammedQueryReg V X Y) :
    K.liftAnc.op r p' p = K.op r (p'.1.1, p'.2) (p.1.1, p.2) *
      (1 : Matrix (X × Y × Bool) (X × Y × Bool) ℂ) p'.1.2 p.1.2 := by
  simp only [KrausMap.liftAnc, KrausMap.reindex, KrausMap.tensorId, Matrix.submatrix_apply,
    Equiv.symm_symm, Matrix.kroneckerMap_apply]
  rfl

/-- `Rel` with the identity on the ancilla. -/
theorem Rel.liftAnc {σ' σ : Equiv.Perm V} {S : Set V}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)} (h : Rel σ' σ S K) :
    Rel (wa σ') (wa σ) (ancSet S) K.liftAnc := fun r a b hb => by
  rw [liftAnc_op_apply, liftAnc_op_apply]
  exact congrArg (· * _) (h r (a.1.1, a.2) (b.1.1, b.2) hb)

/-- `Keeps` with the identity on the ancilla. -/
theorem Keeps.liftAnc {S : Set V} {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h : Keeps S K) : Keeps (ancSet S) K.liftAnc := fun r a b hb hne => by
  rw [liftAnc_op_apply] at hne
  exact h r (a.1.1, a.2) (b.1.1, b.2) hb (left_ne_zero_of_mul hne)

section Reprog

variable [AddGroup Y] (a : V → List (Assignment X Y))

omit [Fintype V] [DecidableEq V] [Fintype X] [Fintype Y] [DecidableEq Y] [AddGroup Y] in
/-- `reprogSwap` commutes with a permutation of the work register that its assignments do not
read. -/
theorem reprogSwap_wa {σ : Equiv.Perm V} (ha : ∀ v, a (σ v) = a v)
    (p : ReprogrammedQueryReg V X Y) :
    reprogSwap a (wq (wa σ) p) = wq (wa σ) (reprogSwap a p) := by
  obtain ⟨⟨v, x, y, f⟩, e⟩ := p
  simp only [reprogSwap_apply, reprogCond, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply,
    id_eq, ha]
  split_ifs <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- `reprogAdd` commutes with a permutation of the work register that its assignments do not
read. -/
theorem reprogAdd_wa {σ : Equiv.Perm V} (ha : ∀ v, a (σ v) = a v)
    (p : ReprogrammedQueryReg V X Y) :
    reprogAdd a (wq (wa σ) p) = wq (wa σ) (reprogAdd a p) := by
  obtain ⟨⟨v, x, y, f⟩, e⟩ := p
  simp only [reprogAdd, queryPermOf_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply,
    id_eq, ha]

omit [AddGroup Y] in
/-- `reprogSwap` is along a permutation of the work register that its assignments do not read. -/
theorem rel_reprogSwap {σ : Equiv.Perm V} (ha : ∀ v, a (σ v) = a v) (S : Set V) :
    Rel (wa σ) (wa σ) (ancSet S) (KrausMap.ofPerm (reprogSwap a)) :=
  rel_ofPerm fun b _ => reprogSwap_wa a ha b

/-- `reprogAdd` is along a permutation of the work register that its assignments do not read. -/
theorem rel_reprogAdd {σ : Equiv.Perm V} (ha : ∀ v, a (σ v) = a v) (S : Set V) :
    Rel (wa σ) (wa σ) (ancSet S) (KrausMap.ofPerm (reprogAdd a)) :=
  rel_ofPerm fun b _ => reprogAdd_wa a ha b

omit [AddGroup Y] in
/-- `reprogSwap` keeps every set of work registers. -/
theorem keeps_reprogSwap (S : Set V) :
    Keeps (ancSet S) (KrausMap.ofPerm (reprogSwap a)) :=
  keeps_ofPerm fun p hp => by
    rw [reprogSwap_apply]
    split_ifs
    · exact hp
    · exact hp

/-- `reprogAdd` keeps every set of work registers. -/
theorem keeps_reprogAdd (S : Set V) :
    Keeps (ancSet S) (KrausMap.ofPerm (reprogAdd a)) :=
  keeps_ofPerm fun _ hp => hp

end Reprog

section Sigma

variable {W : Type} [Fintype W] [DecidableEq W]

/-- `Rel` of map `k` of a family, embedded with the index set of the family. -/
theorem Rel.sigmaEmbed {n : ℕ} {G : Fin n → IndexedKrausMap (QueryReg W 1 X Y)} {k : Fin n}
    {σ' σ : Equiv.Perm W} {S : Set W} (h : Rel σ' σ S (G k).K) :
    Rel σ' σ S (KrausMap.sigmaEmbed G k) := fun p a b hb => by
  simp only [KrausMap.sigmaEmbed]
  split_ifs with hh
  · exact h _ a b hb
  · rfl

/-- `Keeps` of map `k` of a family, embedded with the index set of the family. -/
theorem Keeps.sigmaEmbed {n : ℕ} {G : Fin n → IndexedKrausMap (QueryReg W 1 X Y)} {k : Fin n}
    {S : Set W} (h : Keeps S (G k).K) : Keeps S (KrausMap.sigmaEmbed G k) := fun p a b hb hne => by
  simp only [KrausMap.sigmaEmbed] at hne
  split_ifs at hne with hh
  · exact h _ a b hb hne
  · exact absurd rfl hne

open QROM.KrausRel in
/-- `Rel` along `(σ, σ` then `w)` is `OpRel` along `σ` against the map read after `w`. -/
theorem Rel.opRel_permConj {σ w : Equiv.Perm W} {S : Set W}
    {K : KrausMap R (QueryReg W 1 X Y) (QueryReg W 1 X Y)} (h : Rel σ (σ.trans w) S K) :
    OpRel (wq σ) {p | p.1 ∈ S} K (K.permConj (wq w) (Equiv.refl _)) := fun r a b hb =>
  h r a b hb

open QROM.KrausRel in
/-- `Keeps` as `KrausRel.Keeps` on the query registers. -/
theorem Keeps.keeps {S : Set W} {K : KrausMap R (QueryReg W 1 X Y) (QueryReg W 1 X Y)}
    (h : Keeps S K) : QROM.KrausRel.Keeps {p | p.1 ∈ S} K :=
  h

end Sigma

end WorkRel

/-! ### Permutations of a product that keep the second factor -/

namespace ProdPerm

variable {P Q L : Type*}

/-- **A permutation of `P × Q` that acts on `P` alone**: it keeps the second factor, and its
first factor does not read it. -/
def SndFix (π : Equiv.Perm (P × Q)) : Prop :=
  ∀ p q q', π (p, q) = ((π (p, q')).1, q)

/-- The identity acts on the first factor alone. -/
theorem sndFix_refl : SndFix (Equiv.refl (P × Q)) := fun _ _ _ => rfl

/-- A composition of permutations acting on the first factor alone acts on it alone. -/
theorem SndFix.trans {π₁ π₂ : Equiv.Perm (P × Q)} (h₁ : SndFix π₁) (h₂ : SndFix π₂) :
    SndFix (π₁.trans π₂) := fun p q q' => by
  simp only [Equiv.trans_apply]
  rw [h₁ p q q', h₂ _ q q', ← h₁ p q' q']

/-- The inverse of a permutation acting on the first factor alone acts on it alone. -/
theorem SndFix.symm {π : Equiv.Perm (P × Q)} (h : SndFix π) : SndFix π.symm := fun p q q' => by
  rw [Equiv.symm_apply_eq, h _ q (π.symm (p, q')).2, Prod.mk.eta, Equiv.apply_symm_apply]

/-- **A controlled permutation of `P × Q` acting on `P` alone, as a permutation of `P`**: at `p`,
the permutation `π (ℓ p)`, for a control `ℓ` that the permutations keep. -/
def ctrlFst (ℓ : P → L) (π : L → Equiv.Perm (P × Q)) (q₀ : Q) (hq : ∀ l, SndFix (π l))
    (hℓ : ∀ l p q, ℓ (π l (p, q)).1 = ℓ p) : Equiv.Perm P where
  toFun p := (π (ℓ p) (p, q₀)).1
  invFun p := ((π (ℓ p)).symm (p, q₀)).1
  left_inv p := by
    dsimp only
    rw [hℓ, ← hq (ℓ p) p q₀ q₀, Equiv.symm_apply_apply]
  right_inv p := by
    dsimp only
    have h1 : ℓ ((π (ℓ p)).symm (p, q₀)).1 = ℓ p := by
      have := hℓ (ℓ p) ((π (ℓ p)).symm (p, q₀)).1 ((π (ℓ p)).symm (p, q₀)).2
      rw [Prod.mk.eta, Equiv.apply_symm_apply] at this
      exact this.symm
    rw [h1, ← (hq (ℓ p)).symm p q₀ q₀, Equiv.apply_symm_apply]

/-- **`ctrlFst` is the controlled permutation**: `π (ℓ p)` sends `(p, q)` to `(ctrlFst p, q)`. -/
theorem ctrlFst_spec (ℓ : P → L) (π : L → Equiv.Perm (P × Q)) (q₀ : Q) (hq : ∀ l, SndFix (π l))
    (hℓ : ∀ l p q, ℓ (π l (p, q)).1 = ℓ p) (p : P) (q : Q) :
    π (ℓ p) (p, q) = (ctrlFst ℓ π q₀ hq hℓ p, q) :=
  hq (ℓ p) p q q₀

end ProdPerm

/-! ### Circuits along permutations of the work register -/

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] (τ : Equiv.Perm V) (w : ℕ → Equiv.Perm V) (S : Set V)

open WorkRel in
/-- **Every Kraus map of the circuit is along the table swap `τ` with the writes `w`**
(proof-internal), read with `k` reprogrammed queries before the circuit, with the column
permutation `σ` at the start and `σe` at the end: every Kraus map keeps `S` and is along `σ` on
both sides, or absorbs the column permutation (along `τ` and `σ`, after which the column
permutation is `τ`). A reprogrammed query needs the column permutation `τ`, reads its assignments
independently of `τ` and of the next write `w (k + 1)`, and starts the next segment with the
column permutation `τ` then `w (k + 1)`. -/
def RelAt : ReprogrammedCircuit V X Y → ℕ → Equiv.Perm V → Equiv.Perm V → Prop
  | nil, _, σ, σe => σ = σe
  | kraus K c, k, σ, σe => Keeps S K ∧
      ((Rel σ σ S K ∧ RelAt c k σ σe) ∨ (Rel τ σ S K ∧ RelAt c k τ σe))
  | rquery a c, k, σ, σe => σ = τ ∧ (∀ v, a (τ v) = a v) ∧
      (∀ v, a (w (k + 1) v) = a v) ∧ RelAt c (k + 1) (τ.trans (w (k + 1))) σe

variable {τ w S}

/-- **A concatenation**, the second circuit read after the first one's queries, from the first
one's end permutation. -/
theorem RelAt.append : ∀ {c d : ReprogrammedCircuit V X Y} {k : ℕ} {σ σ' σ'' : Equiv.Perm V},
    RelAt τ w S c k σ σ' → RelAt τ w S d (k + c.queries) σ' σ'' → RelAt τ w S (c ++ d) k σ σ''
  | nil, _, _, _, _, _, hc, hd => by
    change _ = _ at hc
    subst hc
    exact hd
  | kraus _ c, _, _, _, _, _, ⟨hk, Or.inl ⟨hK, hc⟩⟩, hd =>
    ⟨hk, Or.inl ⟨hK, RelAt.append (c := c) hc hd⟩⟩
  | kraus _ c, _, _, _, _, _, ⟨hk, Or.inr ⟨hK, hc⟩⟩, hd =>
    ⟨hk, Or.inr ⟨hK, RelAt.append (c := c) hc hd⟩⟩
  | rquery _ c, d, k, _, _, _, ⟨h1, h2, h3, hc⟩, hd => by
    refine ⟨h1, h2, h3, RelAt.append (c := c) hc ?_⟩
    rw [show k + 1 + c.queries = k + (rquery _ c).queries by simp [queries]; omega]
    exact hd

/-- **A concatenation of circuits with `L` queries each**, piece `i` read from query `k₀ + i * L`
from the column permutation `σ i` to `σ (i + 1)`. -/
theorem RelAt.concat_of {L : ℕ} :
    ∀ {cs : List (ReprogrammedCircuit V X Y)} {k₀ : ℕ} {σ : ℕ → Equiv.Perm V},
      (∀ c ∈ cs, c.queries = L) →
      (∀ i (hi : i < cs.length), RelAt τ w S cs[i] (k₀ + i * L) (σ i) (σ (i + 1))) →
      RelAt τ w S (concat cs) k₀ (σ 0) (σ cs.length)
  | [], _, _, _, _ => rfl
  | c :: cs, k₀, σ, hq, h => by
    refine RelAt.append (by have := h 0 (by simp); simpa using this) ?_
    rw [hq c (List.mem_cons_self ..)]
    exact RelAt.concat_of (cs := cs) (k₀ := k₀ + L) (σ := fun i => σ (i + 1))
      (fun d hd => hq d (List.mem_cons_of_mem _ hd)) fun i hi => by
        have h' := h (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h'
        have e : k₀ + L + i * L = k₀ + (i + 1) * L := by ring
        rw [e]
        exact h'

/-- `RelAt.concat_of` for the circuits of a function on `Fin n`. -/
theorem RelAt.concat_finRange {n L k₀ : ℕ} {f : Fin n → ReprogrammedCircuit V X Y}
    {σ : ℕ → Equiv.Perm V} (hq : ∀ i, (f i).queries = L)
    (h : ∀ i : Fin n, RelAt τ w S (f i) (k₀ + i * L) (σ i) (σ (i + 1))) :
    RelAt τ w S (concat ((List.finRange n).map f)) k₀ (σ 0) (σ n) := by
  have := RelAt.concat_of (τ := τ) (w := w) (S := S) (L := L)
    (cs := (List.finRange n).map f) (k₀ := k₀) (σ := σ) (fun c hc => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hc
      exact hq i)
    fun i hi => by
      simp only [List.getElem_map, List.getElem_finRange]
      exact h _
  simpa using this

/-- The column permutation at the start of segment `j`: `σ` for the first, `τ` then the write
`w (k + j)` for the others. -/
def segStart (τ : Equiv.Perm V) (w : ℕ → Equiv.Perm V) (σ : Equiv.Perm V) (k : ℕ) :
    ℕ → Equiv.Perm V
  | 0 => σ
  | j + 1 => τ.trans (w (k + (j + 1)))

/-- The column permutation at the end of segment `j` of a circuit with `d` queries: `σe` for the
last, `τ` for the others. -/
def segEnd (τ σe : Equiv.Perm V) (d j : ℕ) : Equiv.Perm V :=
  if j = d then σe else τ

variable [AddGroup Y]

open WorkRel in
/-- **Every segment of the compiled circuit is along the table swap with the writes**: segment
`j` is along `segEnd` and `segStart` and keeps `S`. -/
theorem relAt_seg : ∀ (c : ReprogrammedCircuit V X Y) {k : ℕ} {σ σe : Equiv.Perm V},
    RelAt τ w S c k σ σe → ∀ j ≤ c.queries,
      Rel (wa (segEnd τ σe c.queries j)) (wa (segStart τ w σ k j)) (ancSet S)
        ((toCircuit c).seg j).K ∧ Keeps (ancSet S) ((toCircuit c).seg j).K
  | nil, k, σ, σe, hc, j, hj => by
    obtain rfl : j = 0 := by simpa [queries] using hj
    change _ = _ at hc
    subst hc
    rw [toCircuit, Circuit.seg_nil]
    exact ⟨rel_identity _ _, keeps_identity _⟩
  | kraus K c, k, σ, σe, ⟨hk, Or.inl ⟨hK, hc⟩⟩, 0, _ => by
    have ih := relAt_seg c hc 0 (Nat.zero_le _)
    change Rel _ _ _ ((Circuit.head (toCircuit c)).K.comp K.liftAnc) ∧
      Keeps _ ((Circuit.head (toCircuit c)).K.comp K.liftAnc)
    exact ⟨ih.1.comp hK.liftAnc hk.liftAnc, ih.2.comp hk.liftAnc⟩
  | kraus K c, k, σ, σe, ⟨hk, Or.inr ⟨hK, hc⟩⟩, 0, _ => by
    have ih := relAt_seg c hc 0 (Nat.zero_le _)
    change Rel _ _ _ ((Circuit.head (toCircuit c)).K.comp K.liftAnc) ∧
      Keeps _ ((Circuit.head (toCircuit c)).K.comp K.liftAnc)
    exact ⟨ih.1.comp hK.liftAnc hk.liftAnc, ih.2.comp hk.liftAnc⟩
  | kraus K c, k, σ, σe, ⟨_, Or.inl ⟨_, hc⟩⟩, j + 1, hj => relAt_seg c hc (j + 1) hj
  | kraus K c, k, σ, σe, ⟨_, Or.inr ⟨_, hc⟩⟩, j + 1, hj => relAt_seg c hc (j + 1) hj
  | rquery a c, k, σ, σe, ⟨h1, h2, _, _⟩, 0, _ => by
    change Rel _ _ _ ((KrausMap.identity _).comp (KrausMap.ofPerm (reprogSwap a))) ∧
      Keeps _ ((KrausMap.identity _).comp (KrausMap.ofPerm (reprogSwap a)))
    have e : segEnd τ σe (rquery a c).queries 0 = τ := if_neg (by simp [queries])
    rw [e, segStart, h1]
    exact ⟨(rel_identity _ _).comp (rel_reprogSwap a h2 S) (WorkRel.keeps_reprogSwap a S),
      (keeps_identity _).comp (WorkRel.keeps_reprogSwap a S)⟩
  | rquery a c, k, σ, σe, ⟨_, h2, h3, hc⟩, 1, hj => by
    have ih := relAt_seg c hc 0 (Nat.zero_le _)
    change Rel _ _ _ ((Circuit.head (toCircuit c)).K.comp
        ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a)))) ∧
      Keeps _ ((Circuit.head (toCircuit c)).K.comp
        ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a))))
    have e1 : segEnd τ σe (rquery a c).queries 1 = segEnd τ σe c.queries 0 :=
      if_congr (by simp [queries]; omega) rfl rfl
    have e2 : segStart τ w σ k 1 = segStart τ w (τ.trans (w (k + 1))) (k + 1) 0 := rfl
    rw [e1, e2]
    have hτw : ∀ v, a ((τ.trans (w (k + 1))) v) = a v := fun v => by
      change a (w (k + 1) (τ v)) = a v
      rw [h3, h2]
    have hs := rel_reprogSwap a hτw S
    have ha := rel_reprogAdd a hτw S
    exact ⟨ih.1.comp (ha.comp hs (WorkRel.keeps_reprogSwap a S))
      ((WorkRel.keeps_reprogAdd a S).comp (WorkRel.keeps_reprogSwap a S)),
      ih.2.comp ((WorkRel.keeps_reprogAdd a S).comp (WorkRel.keeps_reprogSwap a S))⟩
  | rquery a c, k, σ, σe, ⟨_, _, _, hc⟩, j + 2, hj => by
    have ih := relAt_seg c hc (j + 1) (by simp [queries] at hj; omega)
    have e1 : segEnd τ σe (rquery a c).queries (j + 2) = segEnd τ σe c.queries (j + 1) :=
      if_congr (by simp [queries]) rfl rfl
    have e2 : segStart τ w σ k (j + 2) =
        segStart τ w (τ.trans (w (k + 1))) (k + 1) (j + 1) := by
      show τ.trans (w (k + (j + 1 + 1))) = τ.trans (w (k + 1 + (j + 1)))
      rw [show k + 1 + (j + 1) = k + (j + 1 + 1) by omega]
    rw [e1, e2]
    exact ih

open WorkRel in
/-- **Every Kraus map of the compiled algorithm is along the table swap with the writes**, for a
circuit along them from the first write to `τ`: map `i` along `τ` and `τ` then `w i`, keeping
`S`. -/
theorem relAt_toAlg_step {c : ReprogrammedCircuit V X Y}
    (hR : RelAt τ w S c 0 (τ.trans (w 0)) τ) {O : Type} (init : MState (ReprogrammedQueryReg V X Y))
    (out : V × (X × Y × Bool) → O) (i : Fin ((toCircuit c).queries + 1)) :
    Rel (wa τ) (wa (τ.trans (w i))) (ancSet S) (((toCircuit c).toAlg init out).step i) ∧
      Keeps (ancSet S) (((toCircuit c).toAlg init out).step i) := by
  have hi : (i : ℕ) ≤ c.queries := by
    have h1 := i.isLt
    have h2 := queries_toCircuit c
    omega
  have h := relAt_seg c hR i hi
  have e1 : segEnd τ τ c.queries i = τ := ite_self _
  have e2 : segStart τ w (τ.trans (w 0)) 0 i = τ.trans (w i) := by
    obtain ⟨_ | n, hn⟩ := i
    · rfl
    · change τ.trans (w (0 + (n + 1))) = _
      rw [Nat.zero_add]
  rw [e1, e2] at h
  exact ⟨h.1.sigmaEmbed, h.2.sigmaEmbed⟩

end ReprogrammedCircuit

/-! ### The composition along a permutation of the adversary's registers -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (Ch : Challenger X Y Req Resp)

/-- **A permutation of the adversary's registers other than its query pairs**, on the composed
registers. -/
def advOne (g : Equiv.Perm (B.W × Req × Option Resp)) : Equiv.Perm (B.CW Ch) where
  toFun v := ⟨(g v.adv.1, v.adv.2), v.chal⟩
  invFun v := ⟨(g.symm v.adv.1, v.adv.2), v.chal⟩
  left_inv v := by
    simp only [Equiv.symm_apply_apply]
  right_inv v := by
    simp only [Equiv.apply_symm_apply]

variable {B Ch}

/-- `advOne` of a composition. -/
theorem advOne_trans (g g' : Equiv.Perm (B.W × Req × Option Resp)) :
    (B.advOne Ch g).trans (B.advOne Ch g') = B.advOne Ch (g.trans g') :=
  Equiv.ext fun _ => rfl

/-- `advOne` of the identity. -/
theorem advOne_refl : B.advOne Ch (Equiv.refl _) = Equiv.refl _ :=
  Equiv.ext fun _ => rfl

/-- **A Kraus map of the adversary along permutations of its registers other than the query
pairs**, on the columns whose workspace is in `Sw`. -/
def DRel {R : Type} [Fintype R] (g' g : Equiv.Perm (B.W × Req × Option Resp)) (Sw : Set B.W)
    (K : KrausMap R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp)) : Prop :=
  ∀ r a b, b.1.1 ∈ Sw → K.op r (g' a.1, a.2) (g b.1, b.2) = K.op r a b

/-- **A Kraus map of the adversary keeps the workspaces in `Sw`.** -/
def DKeeps {R : Type} [Fintype R] (Sw : Set B.W)
    (K : KrausMap R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp)) : Prop :=
  ∀ r a b, b.1.1 ∈ Sw → K.op r a b ≠ 0 → a.1.1 ∈ Sw

open WorkRel in
/-- **The adversary's Kraus map on the composed registers along `advOne`**, from its Kraus map
along the permutations of its registers. -/
theorem rel_advKraus {g' g : Equiv.Perm (B.W × Req × Option Resp)} {Sw : Set B.W}
    {k : StepIdx B.slots B.post} (h : DRel g' g Sw (B.step k)) :
    Rel (B.advOne Ch g') (B.advOne Ch g) (B.advIn Ch Sw) (B.advKraus Ch k) := fun r a b hb => by
  rw [advKraus, KrausMap.tensorId_reindex_op_apply, KrausMap.tensorId_reindex_op_apply]
  exact congrArg (· * _) (h r a.1.adv b.1.adv hb)

open WorkRel in
/-- The adversary's Kraus map on the composed registers keeps the workspaces it keeps. -/
theorem keeps_advKraus {Sw : Set B.W} {k : StepIdx B.slots B.post} (h : DKeeps Sw (B.step k)) :
    Keeps (B.advIn Ch Sw) (B.advKraus Ch k) := fun r a b hb hne => by
  rw [advKraus, KrausMap.tensorId_reindex_op_apply] at hne
  exact h r a.1.adv b.1.adv hb (left_ne_zero_of_mul hne)

variable [Nonempty X] [AddCommGroup Y]

omit [AddCommGroup Y] in
open WorkRel in
/-- The preparation of a challenger query commutes with `advOne`. -/
theorem rel_prepChal (g : Equiv.Perm (B.W × Req × Option Resp)) (Sw : Set B.W) (j : Fin B.slots)
    (i : Fin Ch.q) :
    Rel (B.advOne Ch g) (B.advOne Ch g) (B.advIn Ch Sw) (KrausMap.ofPerm (B.prepChal Ch j i)) :=
  rel_ofPerm fun _ _ => rfl

omit [Nonempty X] [AddCommGroup Y] in
open WorkRel in
/-- The exchange into a challenger query register commutes with `advOne`. -/
theorem rel_garSwap (g : Equiv.Perm (B.W × Req × Option Resp)) (Sw : Set B.W) (j : Fin B.slots)
    (i : Fin Ch.q) :
    Rel (B.advOne Ch g) (B.advOne Ch g) (B.advIn Ch Sw) (KrausMap.ofPerm (B.garSwap Ch j i)) :=
  rel_ofPerm fun _ _ => rfl

omit [Nonempty X] [AddCommGroup Y] in
open WorkRel in
/-- The exchange with an adversary query pair commutes with `advOne`. -/
theorem rel_advSwap (g : Equiv.Perm (B.W × Req × Option Resp)) (Sw : Set B.W) (i : Fin B.width) :
    Rel (B.advOne Ch g) (B.advOne Ch g) (B.advIn Ch Sw) (KrausMap.ofPerm (B.advSwap Ch i)) :=
  rel_ofPerm fun _ _ => rfl

omit [Nonempty X] [AddCommGroup Y] in
open WorkRel in
/-- A basis permutation that keeps the workspace keeps every set of workspaces. -/
theorem keeps_ofPerm_ws {π : Equiv.Perm (QueryReg (B.CW Ch) 1 X Y)}
    (hπ : ∀ p, (π p).1.adv.workspace = p.1.adv.workspace) (Sw : Set B.W) :
    Keeps (B.advIn Ch Sw) (KrausMap.ofPerm π) :=
  keeps_ofPerm fun b hb => by
    change (π b).1.adv.workspace ∈ Sw
    rw [hπ]
    exact hb

/-- The permutation of the workspace `φ` on the adversary's registers other than the query
pairs. -/
abbrev wsOne (φ : Equiv.Perm B.W) : Equiv.Perm (B.W × Req × Option Resp) :=
  φ.prodCongr (Equiv.refl _)

omit [Nonempty X] [AddCommGroup Y] in
open WorkRel in
/-- Writing a reply commutes with a permutation of the workspace. -/
theorem rel_writeReply {φ : Equiv.Perm B.W} (Sw : Set B.W) (j : Fin B.slots) :
    Rel (B.advOne Ch (wsOne φ)) (B.advOne Ch (wsOne φ)) (B.advIn Ch Sw)
      (KrausMap.ofPerm (B.writeReply Ch j)) :=
  rel_ofPerm fun b _ => by
    change (if _ then _ else _) = WorkRel.wq _ (if _ then _ else _)
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl

omit [Nonempty X] [AddCommGroup Y] in
open WorkRel in
/-- The request measurement commutes with a permutation of the workspace that keeps the kind. -/
theorem rel_measReq {φ : Equiv.Perm B.W} (hφ : ∀ x, B.kind (φ x) = B.kind x) (Sw : Set B.W)
    (j : Fin B.slots) :
    Rel (B.advOne Ch (wsOne φ)) (B.advOne Ch (wsOne φ)) (B.advIn Ch Sw) (B.measReq Ch j) :=
  fun o a b _ => by
  rw [AdaptiveIAlg.measReq_op_apply, AdaptiveIAlg.measReq_op_apply]
  have hc : B.copyReq Ch j (wq (B.advOne Ch (wsOne φ)) b) =
      wq (B.advOne Ch (wsOne φ)) (B.copyReq Ch j b) := by
    rw [copyReq_apply, copyReq_apply]
    change (if B.kind (φ b.1.adv.workspace) = true then _ else _) = _
    rw [hφ]
    split_ifs <;> rfl
  have hr : B.reqOutcome Ch (wq (B.advOne Ch (wsOne φ)) b) = B.reqOutcome Ch b := by
    change (if B.kind (φ b.1.adv.workspace) then _ else _) =
      (if B.kind b.1.adv.workspace then _ else _)
    rw [hφ]
    rfl
  rw [hc, hr]
  exact congrArg (· * _) (if_congr (wq (B.advOne Ch (wsOne φ))).injective.eq_iff rfl rfl)

open WorkRel in
/-- The request measurement keeps every set of workspaces. -/
theorem keeps_measReq (Sw : Set B.W) (j : Fin B.slots) :
    Keeps (B.advIn Ch Sw) (B.measReq Ch j) := fun o a b hb hne => by
  rw [AdaptiveIAlg.measReq_op_apply] at hne
  have hy : a = B.copyReq Ch j b := by
    by_contra h'
    exact hne (mul_eq_zero_of_left (if_neg h') _)
  subst hy
  change (B.copyReq Ch j b).1.adv.workspace ∈ Sw
  rw [copyReq_workspace]
  exact hb

/-! #### The circuit of the composition along the table swap with the writes -/

section Circ

open WorkRel ReprogrammedCircuit

variable (φ : Equiv.Perm B.W) (ψ : ℕ → Equiv.Perm (B.W × Req × Option Resp)) (Sw : Set B.W)

/-- The writes `ψ k` on the composed registers. -/
abbrev wOf {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (Ch : Challenger X Y Req Resp)
    (ψ : ℕ → Equiv.Perm (B.W × Req × Option Resp)) : ℕ → Equiv.Perm (B.CW Ch) :=
  fun k => B.advOne Ch (ψ k)

variable {φ ψ Sw}

/-- **One challenger query of slot `j` is along the table swap**, from `τ` to `τ` then the next
write. -/
theorem relAt_chalPiece (j : Fin B.slots) (i : Fin Ch.q) (k : ℕ) :
    RelAt (B.advOne Ch (wsOne φ)) (B.wOf Ch ψ) (B.advIn Ch Sw)
      (.kraus (KrausMap.ofPerm (B.prepChal Ch j i))
        (.rquery (fun v => B.chalAss Ch j i v.chal)
          (.kraus (KrausMap.ofPerm (B.garSwap Ch j i)) .nil))) k
      (B.advOne Ch (wsOne φ)) ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (k + 1))) :=
  ⟨keeps_ofPerm_ws (fun _ => rfl) Sw, Or.inl ⟨rel_prepChal _ Sw j i, rfl, fun _ => rfl,
    fun _ => rfl, keeps_ofPerm_ws (fun _ => rfl) Sw,
    Or.inl ⟨by rw [wOf, advOne_trans]; exact rel_garSwap _ Sw j i, rfl⟩⟩⟩

omit [Nonempty X] [AddCommGroup Y] in
/-- **One adversary query is along the table swap**, from `τ` to `τ` then the next write, for
assignments read from the challenger's registers. -/
theorem relAt_advPiece (ass : B.CW Ch → List (Assignment X Y))
    (hass : ∀ g v, ass (B.advOne Ch g v) = ass v) (i : Fin B.width) (k : ℕ) :
    RelAt (B.advOne Ch (wsOne φ)) (B.wOf Ch ψ) (B.advIn Ch Sw)
      (.kraus (KrausMap.ofPerm (B.advSwap Ch i))
        (.rquery ass (.kraus (KrausMap.ofPerm (B.advSwap Ch i)) .nil))) k
      (B.advOne Ch (wsOne φ)) ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (k + 1))) :=
  ⟨keeps_ofPerm_ws (fun _ => rfl) Sw, Or.inl ⟨rel_advSwap _ Sw i, rfl, hass _, hass _,
    keeps_ofPerm_ws (fun _ => rfl) Sw,
    Or.inl ⟨by rw [wOf, advOne_trans]; exact rel_advSwap _ Sw i, rfl⟩⟩⟩

omit [Nonempty X] [AddCommGroup Y] in
/-- `τ` then a trivial write is `τ`. -/
theorem trans_wOf_of_refl {k : ℕ} (h : ψ k = Equiv.refl _) :
    (B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ k) = B.advOne Ch (wsOne φ) := by
  rw [wOf, h, advOne_refl, Equiv.trans_refl]

/-- **The challenger's queries of slot `j` are along the table swap**, when the writes inside them
are trivial. -/
theorem relAt_chalQueries (j : Fin B.slots) (k₀ : ℕ)
    (hw : ∀ i, 1 ≤ i → i ≤ Ch.q → ψ (k₀ + i) = Equiv.refl _) :
    RelAt (B.advOne Ch (wsOne φ)) (B.wOf Ch ψ) (B.advIn Ch Sw) (B.chalQueries Ch j) k₀
      (B.advOne Ch (wsOne φ)) (B.advOne Ch (wsOne φ)) := by
  set σ : ℕ → Equiv.Perm (B.CW Ch) := fun i =>
    if i = 0 then B.advOne Ch (wsOne φ) else (B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (k₀ + i))
  have hσ : ∀ i, i ≤ Ch.q → σ i = B.advOne Ch (wsOne φ) := fun i hi => by
    by_cases h0 : i = 0
    · exact if_pos h0
    · rw [show σ i = _ from if_neg h0]
      exact trans_wOf_of_refl (hw i (by omega) hi)
  have h := RelAt.concat_finRange (τ := B.advOne Ch (wsOne φ)) (w := B.wOf Ch ψ)
    (S := B.advIn Ch Sw) (L := 1) (k₀ := k₀) (σ := σ)
    (f := fun i => .kraus (KrausMap.ofPerm (B.prepChal Ch j i))
        (.rquery (fun v => B.chalAss Ch j i v.chal)
          (.kraus (KrausMap.ofPerm (B.garSwap Ch j i)) .nil))) (fun _ => rfl) fun i => by
    rw [hσ i (by omega), show σ (i + 1) = _ from if_neg (by omega), mul_one]
    exact relAt_chalPiece j i _
  rw [hσ 0 (Nat.zero_le _), hσ Ch.q le_rfl] at h
  exact h

omit [Nonempty X] [AddCommGroup Y] in
/-- **The adversary's queries are along the table swap**, up to the write after them, when the
writes inside them are trivial and the assignments are read from the challenger's registers. -/
theorem relAt_advQueries (ass : B.CW Ch → List (Assignment X Y))
    (hass : ∀ g v, ass (B.advOne Ch g v) = ass v) (k₀ : ℕ)
    (hw : ∀ i, 1 ≤ i → i < B.width → ψ (k₀ + i) = Equiv.refl _) :
    RelAt (B.advOne Ch (wsOne φ)) (B.wOf Ch ψ) (B.advIn Ch Sw) (B.advQueries Ch ass) k₀
      (B.advOne Ch (wsOne φ)) ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (k₀ + B.width))) := by
  set σ : ℕ → Equiv.Perm (B.CW Ch) := fun i =>
    if i = 0 then B.advOne Ch (wsOne φ) else (B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (k₀ + i))
  have hσ : ∀ i, i < B.width → σ i = B.advOne Ch (wsOne φ) := fun i hi => by
    by_cases h0 : i = 0
    · exact if_pos h0
    · rw [show σ i = _ from if_neg h0]
      exact trans_wOf_of_refl (hw i (by omega) hi)
  have h := RelAt.concat_finRange (τ := B.advOne Ch (wsOne φ)) (w := B.wOf Ch ψ)
    (S := B.advIn Ch Sw) (L := 1) (k₀ := k₀) (σ := σ)
    (f := fun i => .kraus (KrausMap.ofPerm (B.advSwap Ch i))
        (.rquery ass (.kraus (KrausMap.ofPerm (B.advSwap Ch i)) .nil))) (fun _ => rfl) fun i => by
    rw [hσ i i.isLt, show σ (i + 1) = _ from if_neg (by omega), mul_one]
    exact relAt_advPiece ass hass i _
  rw [hσ 0 B.width_pos, show σ B.width = _ from if_neg (by have := B.width_pos; omega)] at h
  exact h

/-- **Slot `j` is along the table swap**, from the write before it to the write after it, when
the adversary's Kraus map before it absorbs the write before it (`hadv`) and the writes inside the
slot are trivial (`hw`). -/
theorem relAt_slotCircBoth (hφ : ∀ x, B.kind (φ x) = B.kind x) (j : Fin B.slots) (k₀ : ℕ)
    (hadv : WorkRel.Rel (B.advOne Ch (wsOne φ)) ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ k₀))
        (B.advIn Ch Sw) (B.advKraus Ch (slotStep j)) ∧
      WorkRel.Keeps (B.advIn Ch Sw) (B.advKraus Ch (slotStep j)))
    (hw : ∀ i, 1 ≤ i → i < Ch.q + B.width → ψ (k₀ + i) = Equiv.refl _) :
    RelAt (B.advOne Ch (wsOne φ)) (B.wOf Ch ψ) (B.advIn Ch Sw) (B.slotCircBoth Ch j) k₀
      ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ k₀))
      ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (k₀ + (Ch.q + B.width)))) := by
  refine ⟨hadv.2, Or.inr ⟨hadv.1, keeps_measReq Sw j, Or.inl ⟨rel_measReq hφ Sw j, ?_⟩⟩⟩
  refine RelAt.append
    (relAt_chalQueries j k₀ fun i h1 h2 => hw i h1 (by have := B.width_pos; omega)) ?_
  rw [queries_chalQueries]
  refine ⟨keeps_ofPerm_ws (writeReply_workspace j) Sw, Or.inl ⟨rel_writeReply Sw j, ?_⟩⟩
  have h := relAt_advQueries (φ := φ) (ψ := ψ) (Sw := Sw) (fun v => B.advAss Ch j v.chal)
    (fun _ _ => rfl) (k₀ + Ch.q) fun i h1 h2 => by
      rw [Nat.add_assoc]
      exact hw _ (by omega) (by omega)
  rwa [Nat.add_assoc] at h

omit [Nonempty X] [AddCommGroup Y] in
/-- **Post batch `b` is along the table swap**, from the write before it to the write after it,
when the adversary's Kraus map before it absorbs the write before it (`hadv`) and the writes inside
the batch are trivial (`hw`). -/
theorem relAt_postCirc (b : Fin B.post) (k₀ : ℕ)
    (hadv : WorkRel.Rel (B.advOne Ch (wsOne φ)) ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ k₀))
        (B.advIn Ch Sw) (B.advKraus Ch (postStep b)) ∧
      WorkRel.Keeps (B.advIn Ch Sw) (B.advKraus Ch (postStep b)))
    (hw : ∀ i, 1 ≤ i → i < B.width → ψ (k₀ + i) = Equiv.refl _) :
    RelAt (B.advOne Ch (wsOne φ)) (B.wOf Ch ψ) (B.advIn Ch Sw) (B.postCirc Ch b) k₀
      ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ k₀))
      ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (k₀ + B.width))) :=
  ⟨hadv.2, Or.inr ⟨hadv.1, relAt_advQueries (fun v => B.postAss Ch v.chal) (fun _ _ => rfl) k₀ hw⟩⟩

omit [Nonempty X] [AddCommGroup Y] in
/-- The queries of a concatenation of `n` circuits with `L` queries each. -/
theorem queries_concat_finRange {V : Type} [Fintype V] [DecidableEq V] {n L : ℕ}
    {f : Fin n → ReprogrammedCircuit V X Y} (hq : ∀ i, (f i).queries = L) :
    (concat ((List.finRange n).map f)).queries = n * L := by
  rw [queries_concat, List.map_map]
  have h : (List.finRange n).map ((fun c => ReprogrammedCircuit.queries c) ∘ f) =
      (List.finRange n).map fun _ => L := List.map_congr_left fun i _ => hq i
  rw [h]
  simp

/-- **The composition's circuit is along the table swap with the writes**, when the adversary's
Kraus map before each slot and each post batch, and the last one, absorb the write before them
(`hslot`, `hpost`, `hlast`) and every write other than at the end of a slot is trivial (`hψ`). -/
theorem relAt_fullCircBoth (hφ : ∀ x, B.kind (φ x) = B.kind x)
    (hψ : ∀ k, (∀ j < B.slots, k ≠ (j + 1) * (Ch.q + B.width)) → ψ k = Equiv.refl _)
    (hslot : ∀ j : Fin B.slots,
      WorkRel.Rel (B.advOne Ch (wsOne φ))
          ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ ((j : ℕ) * (Ch.q + B.width))))
          (B.advIn Ch Sw) (B.advKraus Ch (slotStep j)) ∧
        WorkRel.Keeps (B.advIn Ch Sw) (B.advKraus Ch (slotStep j)))
    (hpost : ∀ b : Fin B.post,
      WorkRel.Rel (B.advOne Ch (wsOne φ)) ((B.advOne Ch (wsOne φ)).trans
          (B.wOf Ch ψ (B.slots * (Ch.q + B.width) + (b : ℕ) * B.width)))
          (B.advIn Ch Sw) (B.advKraus Ch (postStep b)) ∧
        WorkRel.Keeps (B.advIn Ch Sw) (B.advKraus Ch (postStep b)))
    (hlast : WorkRel.Rel (B.advOne Ch (wsOne φ)) ((B.advOne Ch (wsOne φ)).trans
          (B.wOf Ch ψ (B.slots * (Ch.q + B.width) + B.post * B.width)))
          (B.advIn Ch Sw) (B.advKraus Ch lastStep) ∧
        WorkRel.Keeps (B.advIn Ch Sw) (B.advKraus Ch lastStep)) :
    RelAt (B.advOne Ch (wsOne φ)) (B.wOf Ch ψ) (B.advIn Ch Sw) (B.fullCircBoth Ch) 0
      ((B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ 0)) (B.advOne Ch (wsOne φ)) := by
  have hL := B.width_pos
  set L := Ch.q + B.width with hLdef
  unfold KindAlg.fullCircBoth
  have h1 := RelAt.concat_finRange (τ := B.advOne Ch (wsOne φ)) (w := B.wOf Ch ψ)
    (S := B.advIn Ch Sw) (L := L) (k₀ := 0)
    (σ := fun i => (B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (i * L)))
    (f := fun j => B.slotCircBoth Ch j) (fun j => B.queries_slotCircBoth Ch j) fun j => by
      have h := relAt_slotCircBoth (ψ := ψ) (Sw := Sw) hφ j ((j : ℕ) * L)
        (by simpa using hslot j) fun i h1 h2 => hψ _ fun j' hj' he => by
          rcases Nat.lt_or_ge (j' + 1) ((j : ℕ) + 1) with hlt | hge
          · have := Nat.mul_le_mul_right L (show j' + 1 ≤ (j : ℕ) by omega)
            omega
          · have := Nat.mul_le_mul_right L hge
            have e : ((j : ℕ) + 1) * L = (j : ℕ) * L + L := by ring
            omega
      rw [show (j : ℕ) * L + L = ((j : ℕ) + 1) * L by ring] at h
      simpa using h
  have h2 := RelAt.concat_finRange (τ := B.advOne Ch (wsOne φ)) (w := B.wOf Ch ψ)
    (S := B.advIn Ch Sw) (L := B.width) (k₀ := B.slots * L)
    (σ := fun i => (B.advOne Ch (wsOne φ)).trans (B.wOf Ch ψ (B.slots * L + i * B.width)))
    (f := B.postCirc Ch) (fun b => B.queries_postCirc Ch b) fun b => by
      have h := relAt_postCirc (φ := φ) (ψ := ψ) (Sw := Sw) b (B.slots * L + (b : ℕ) * B.width)
        (hpost b) fun i h1 h2 => hψ _ fun j' hj' he => by
          have := Nat.mul_le_mul_right L (show j' + 1 ≤ B.slots by omega)
          omega
      rw [show B.slots * L + (b : ℕ) * B.width + B.width = B.slots * L + ((b : ℕ) + 1) * B.width
        by ring] at h
      exact h
  simp only [zero_mul, Nat.add_zero] at h1 h2
  refine RelAt.append (σ' := (B.advOne Ch (wsOne φ)).trans
    (B.wOf Ch ψ (B.slots * L + B.post * B.width))) (RelAt.append h1 ?_) ?_
  · rw [queries_concat_finRange (fun j => B.queries_slotCircBoth Ch j), Nat.zero_add]
    simpa using h2
  · rw [queries_append, queries_concat_finRange (fun j => B.queries_slotCircBoth Ch j),
      queries_concat_finRange (fun b => B.queries_postCirc Ch b), Nat.zero_add]
    exact ⟨hlast.2, Or.inr ⟨by simpa [mul_comm] using hlast.1, rfl⟩⟩

end Circ

end KindAlg

/-! ### The trace-preserving form along permutations of the adversary's registers -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **A permutation of the adversary's registers other than the query pairs, with the query
counter kept**, on the registers of the trace-preserving form. -/
def cntOne (ρ : Equiv.Perm (A.W × Req × Option Resp)) :
    Equiv.Perm (A.CntW × Req × Option Resp) where
  toFun x := (AlgShape.CntW.mk (ρ (x.1.work, x.2)).1 x.1.cnt, (ρ (x.1.work, x.2)).2)
  invFun x := (AlgShape.CntW.mk (ρ.symm (x.1.work, x.2)).1 x.1.cnt, (ρ.symm (x.1.work, x.2)).2)
  left_inv x := by simp
  right_inv x := by simp

variable {A}

/-- `cntOne` of a composition. -/
theorem cntOne_trans (ρ' ρ : Equiv.Perm (A.W × Req × Option Resp)) :
    (A.cntOne ρ').trans (A.cntOne ρ) = A.cntOne (ρ'.trans ρ) :=
  Equiv.ext fun _ => rfl

/-- The counter step of the trace-preserving form commutes with `cntOne ρ` for `ρ` keeping the
kind. -/
theorem tpShift_symm_cntOne {ρ : Equiv.Perm (A.W × Req × Option Resp)}
    (hρ : ∀ p, A.kind (ρ p).1 = A.kind p.1) (a : A.CReg) :
    A.tpShift.symm (A.cntOne ρ a.1, a.2) =
      (A.cntOne ρ (A.tpShift.symm a).1, (A.tpShift.symm a).2) := by
  obtain ⟨⟨wc, rq, rs⟩, u⟩ := a
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc
  simp only [cntOne, Equiv.coe_fn_mk, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk,
    tpShift_symm_apply, hρ]

/-- The move to the ended value commutes with `cntOne ρ`. -/
theorem endSwap_symm_cntOne (ρ : Equiv.Perm (A.W × Req × Option Resp)) (a : A.CReg) :
    A.endSwap.symm (A.cntOne ρ a.1, a.2) =
      (A.cntOne ρ (A.endSwap.symm a).1, (A.endSwap.symm a).2) :=
  rfl

/-- `cntOne ρ` keeps the budget test for `ρ` keeping the kind. -/
theorem inBudget_cntOne {ρ : Equiv.Perm (A.W × Req × Option Resp)}
    (hρ : ∀ p, A.kind (ρ p).1 = A.kind p.1) (a : A.CReg) :
    A.inBudget (A.cntOne ρ a.1, a.2) = A.inBudget a := by
  obtain ⟨⟨wc, rq, rs⟩, u⟩ := a
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc
  simp only [cntOne, Equiv.coe_fn_mk, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, inBudget_mk,
    hρ]

/-- The entries of the adversary's Kraus map with the counter, at rows and columns moved by
`cntOne`. -/
theorem cntKraus_op_cntOne (ρ' ρ : Equiv.Perm (A.W × Req × Option Resp))
    (k : StepIdx A.slots A.post) (r : A.R) (a b : A.CReg) :
    (A.cntKraus k).op r (A.cntOne ρ' a.1, a.2) (A.cntOne ρ b.1, b.2) =
      (A.step k).op r (ρ' (a.1.1.work, a.1.2), a.2) (ρ (b.1.1.work, b.1.2), b.2) *
      (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ) a.1.1.cnt b.1.1.cnt := by
  rw [cntKraus_op_apply]
  rfl

/-- The entries of the adversary's Kraus map with the counter. -/
theorem cntKraus_op_apply' (k : StepIdx A.slots A.post) (r : A.R) (a b : A.CReg) :
    (A.cntKraus k).op r a b =
      (A.step k).op r ((a.1.1.work, a.1.2), a.2) ((b.1.1.work, b.1.2), b.2) *
      (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ) a.1.1.cnt b.1.1.cnt := by
  rw [cntKraus_op_apply]
  rfl

theorem tpOp_inl_entry (k : StepIdx A.slots A.post) (r : A.R) (y x : A.CReg) :
    A.tpOp false k (.inl r) y x = if (k : ℕ) < A.slots then
      (if A.inBudget (A.tpShift.symm y) then 1 else 0) * (A.cntKraus k).op r (A.tpShift.symm y) x
    else (A.cntKraus k).op r y x := by
  by_cases hk : (k : ℕ) < A.slots
  · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk, ↓reduceIte,
      restrict_permConj_op_apply]
  · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk, ↓reduceIte]

theorem tpOp_inr_inl_entry (k : StepIdx A.slots A.post) (r : A.R) (y x : A.CReg) :
    A.tpOp false k (.inr (.inl r)) y x = if (k : ℕ) < A.slots then
      (if !A.inBudget (A.endSwap.symm y) then 1 else 0) *
        (A.cntKraus k).op r (A.endSwap.symm y) x
    else 0 := by
  by_cases hk : (k : ℕ) < A.slots
  · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk, ↓reduceIte,
      restrict_permConj_op_apply]
  · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk, ↓reduceIte,
      Matrix.zero_apply]

theorem tpOp_inr_inr_of_haltOp {k : StepIdx A.slots A.post} (hA : (A.step k).haltOp = 0)
    (c : Fin (A.budget + 2)) : A.tpOp false k (.inr (.inr c)) = 0 := by
  simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hA, Matrix.zero_kronecker]
  rfl

/-- **The trace-preserving forms of `A.withStep st'` and `A` along `cntOne ρ'` and `cntOne ρ`**:
when `st' k` at the rows moved by `ρ'` and the columns moved by `ρ` is `A`'s step `k`, on the rows
in `Sr` and the columns in `Sc`, `ρ'` keeps the kind, and the halting operators of both vanish. -/
theorem tpOp_withStep_cntOne
    (st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
      (DReg A.W A.width X Y Req Resp)) {k : StepIdx A.slots A.post}
    (hA : (A.step k).haltOp = 0) (hA' : (st' k).haltOp = 0)
    {ρ' ρ : Equiv.Perm (A.W × Req × Option Resp)} (hρ' : ∀ p, A.kind (ρ' p).1 = A.kind p.1)
    {Sr Sc : Set (DReg A.W A.width X Y Req Resp)}
    (h : ∀ r a b, a ∈ Sr → b ∈ Sc → (st' k).op r (ρ' a.1, a.2) (ρ b.1, b.2) = (A.step k).op r a b)
    (z : A.R ⊕ (A.R ⊕ Fin (A.budget + 2))) (a b : A.CReg) (ha : ((a.1.1.work, a.1.2), a.2) ∈ Sr)
    (hb : ((b.1.1.work, b.1.2), b.2) ∈ Sc) :
    (A.withStep st').tpOp false k z (A.cntOne ρ' a.1, a.2) (A.cntOne ρ b.1, b.2) = A.tpOp false k z
        a b := by
  -- the entries of the two Kraus maps with the counter
  have hc : ∀ r (y : A.CReg), ((y.1.1.work, y.1.2), y.2) ∈ Sr →
      ((A.withStep st').cntKraus k).op r (A.cntOne ρ' y.1, y.2) (A.cntOne ρ b.1, b.2) =
        (A.cntKraus k).op r y b := fun r y hy => by
    have e : ((A.withStep st').cntKraus k).op r (A.cntOne ρ' y.1, y.2) (A.cntOne ρ b.1, b.2) =
        (st' k).op r (ρ' (y.1.1.work, y.1.2), y.2) (ρ (b.1.1.work, b.1.2), b.2) *
          (1 : Matrix (Fin (A.budget + 2)) (Fin (A.budget + 2)) ℂ) y.1.1.cnt b.1.1.cnt :=
      cntKraus_op_cntOne (A := A.withStep st') ρ' ρ k r y b
    rw [e, cntKraus_op_apply' k r y b]
    exact congrArg (· * _) (h r _ _ hy hb)
  -- the counter's maps keep the rest of the registers
  have hs : ∀ y : A.CReg, (((A.tpShift.symm y).1.1.work, (A.tpShift.symm y).1.2),
      (A.tpShift.symm y).2) = ((y.1.1.work, y.1.2), y.2) := fun y => by
    obtain ⟨⟨wc_, q, p⟩, u⟩ := y
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    rfl
  have he : ∀ y : A.CReg, (((A.endSwap.symm y).1.1.work, (A.endSwap.symm y).1.2),
      (A.endSwap.symm y).2) = ((y.1.1.work, y.1.2), y.2) := fun y => by
    obtain ⟨⟨wc_, q, p⟩, u⟩ := y
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    rfl
  rcases z with r | r | c
  · have e : (A.withStep st').tpOp false k (.inl r) (A.cntOne ρ' a.1, a.2) (A.cntOne ρ b.1, b.2) =
        if (k : ℕ) < A.slots then
          (if A.inBudget (A.tpShift.symm (A.cntOne ρ' a.1, a.2)) then 1 else 0) *
            ((A.withStep st').cntKraus k).op r (A.tpShift.symm (A.cntOne ρ' a.1, a.2))
              (A.cntOne ρ b.1, b.2)
        else ((A.withStep st').cntKraus k).op r (A.cntOne ρ' a.1, a.2) (A.cntOne ρ b.1, b.2) :=
      tpOp_inl_entry (A := A.withStep st') k r _ _
    refine e.trans ?_
    rw [tpOp_inl_entry]
    by_cases hk : (k : ℕ) < A.slots
    · simp only [hk, ↓reduceIte]
      rw [tpShift_symm_cntOne hρ', inBudget_cntOne hρ']
      exact congrArg (_ * ·) (hc r _ ((hs a).symm ▸ ha))
    · simp only [hk, ↓reduceIte]
      exact hc r a ha
  · have e : (A.withStep st').tpOp false k (.inr (.inl r)) (A.cntOne ρ' a.1, a.2)
          (A.cntOne ρ b.1, b.2) =
        if (k : ℕ) < A.slots then
          (if !A.inBudget (A.endSwap.symm (A.cntOne ρ' a.1, a.2)) then 1 else 0) *
            ((A.withStep st').cntKraus k).op r (A.endSwap.symm (A.cntOne ρ' a.1, a.2))
              (A.cntOne ρ b.1, b.2)
        else 0 :=
      tpOp_inr_inl_entry (A := A.withStep st') k r _ _
    refine e.trans ?_
    rw [tpOp_inr_inl_entry]
    by_cases hk : (k : ℕ) < A.slots
    · simp only [hk, ↓reduceIte]
      rw [endSwap_symm_cntOne, inBudget_cntOne hρ']
      exact congrArg (_ * ·) (hc r _ ((he a).symm ▸ ha))
    · simp only [hk, ↓reduceIte]
  · have e : (A.withStep st').tpOp false k (.inr (.inr c)) (A.cntOne ρ' a.1, a.2)
        (A.cntOne ρ b.1, b.2) = 0 :=
      congrFun (congrFun (tpOp_inr_inr_of_haltOp (A := A.withStep st') hA' c) _) _
    have e' : A.tpOp false k (.inr (.inr c)) a b = 0 :=
      congrFun (congrFun (tpOp_inr_inr_of_haltOp hA c) _) _
    exact e.trans e'.symm

/-- The operators of the trace-preserving form along `cntOne ρ'` and `cntOne ρ`, on the columns
whose workspace is in `Sd` (`drel_toTPKindAlg` on the registers with the counter): the case
`st' = A.step` of `tpOp_withStep_cntOne`. -/
theorem tpOp_cntOne (hA : ∀ k, (A.step k).haltOp = 0)
    {ρ' ρ : Equiv.Perm (A.W × Req × Option Resp)}
    (hρ' : ∀ p, A.kind (ρ' p).1 = A.kind p.1) {Sd : Set A.W} {k : StepIdx A.slots A.post}
    (h : ∀ r a b, b.1.1 ∈ Sd → (A.step k).op r (ρ' a.1, a.2) (ρ b.1, b.2) = (A.step k).op r a b)
    (z : A.R ⊕ (A.R ⊕ Fin (A.budget + 2))) (a b : A.CReg) (hb : b.1.1.work ∈ Sd) :
    A.tpOp false k z (A.cntOne ρ' a.1, a.2) (A.cntOne ρ b.1, b.2) = A.tpOp false k z a b :=
  tpOp_withStep_cntOne A.step (hA k) (hA k) hρ' (Sr := Set.univ) (Sc := {d | d.1.1 ∈ Sd})
    (fun r a b _ hb => h r a b hb) z a b trivial hb

/-- **The trace-preserving form along permutations of the adversary's registers**: when the
adversary's step `k` is along `ρ'` and `ρ` on the columns whose workspace is in `Sd`, `ρ'` keeps
the kind, and the halting operators vanish, so is the trace-preserving form's step `k`. -/
theorem drel_toTPKindAlg (hA : ∀ k, (A.step k).haltOp = 0)
    {ρ' ρ : Equiv.Perm (A.W × Req × Option Resp)}
    (hρ' : ∀ p, A.kind (ρ' p).1 = A.kind p.1) {Sd : Set A.W} {k : StepIdx A.slots A.post}
    (h : ∀ r a b, b.1.1 ∈ Sd → (A.step k).op r (ρ' a.1, a.2) (ρ b.1, b.2) = (A.step k).op r a b) :
    KindAlg.DRel (B := A.toTPKindAlg) (A.cntOne ρ') (A.cntOne ρ) {w | w.work ∈ Sd}
      (A.toTPKindAlg.step k) :=
  fun z a b hb => by
    rw [toTPKindAlg_step_op]
    exact A.tpOp_cntOne hA hρ' h z a b hb

/-- **The trace-preserving form keeps a set of workspaces** that the adversary's step keeps, when
the halting operators vanish. -/
theorem dkeeps_toTPKindAlg (hA : ∀ k, (A.step k).haltOp = 0) {Sd : Set A.W}
    {k : StepIdx A.slots A.post}
    (h : ∀ r a b, b.1.1 ∈ Sd → (A.step k).op r a b ≠ 0 → a.1.1 ∈ Sd) :
    KindAlg.DKeeps (B := A.toTPKindAlg) {w | w.work ∈ Sd} (A.toTPKindAlg.step k) :=
  fun z a b hb hne => by
  obtain ⟨r, hr⟩ := A.toTPKindAlg_op_ne_zero hA hne
  exact h r _ (A.cntSplit b).1 hb hr

/-- **`drel_toTPKindAlg` with the Kraus maps replaced by `st`**, at `A`'s registers
(`tpStepOf`). -/
theorem drel_tpStepOf
    {st : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
      (DReg A.W A.width X Y Req Resp)} (hA : ∀ k, (st k).haltOp = 0)
    {ρ' ρ : Equiv.Perm (A.W × Req × Option Resp)}
    (hρ' : ∀ p, A.kind (ρ' p).1 = A.kind p.1) {Sd : Set A.W} {k : StepIdx A.slots A.post}
    (h : ∀ r a b, b.1.1 ∈ Sd → (st k).op r (ρ' a.1, a.2) (ρ b.1, b.2) = (st k).op r a b) :
    KindAlg.DRel (B := A.toTPKindAlg) (A.cntOne ρ') (A.cntOne ρ) {w | w.work ∈ Sd}
      (A.tpStepOf false st k) :=
  drel_toTPKindAlg (A := A.withStep st) hA hρ' h

/-- **`dkeeps_toTPKindAlg` with the Kraus maps replaced by `st`**, at `A`'s registers
(`tpStepOf`). -/
theorem dkeeps_tpStepOf
    {st : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
      (DReg A.W A.width X Y Req Resp)} (hA : ∀ k, (st k).haltOp = 0) {Sd : Set A.W}
    {k : StepIdx A.slots A.post}
    (h : ∀ r a b, b.1.1 ∈ Sd → (st k).op r a b ≠ 0 → a.1.1 ∈ Sd) :
    KindAlg.DKeeps (B := A.toTPKindAlg) {w | w.work ∈ Sd} (A.tpStepOf false st k) :=
  dkeeps_toTPKindAlg (A := A.withStep st) hA h

end AdaptiveIAlg

/-! ### The adversary absorbed with a table, across the table swap -/

section AbsTab

open GordieHowe.QROM

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-- **The swap of the table register between `tab` and the empty table**, on the registers of the
adversary absorbed with a table. -/
def absTabSwap (tab : A.OuterTab Req₂ Resp₂) : Equiv.Perm (AbsD A Req₁ Resp₁ Req₂ Resp₂) :=
  Function.Involutive.toPerm (fun d => (((d.1.1.1, Equiv.swap tab (tab₀ A) d.1.1.2), d.1.2), d.2))
    fun d => by simp

/-- The registers of the adversary absorbed with a table, the table register dropped. -/
abbrev absStrip (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁ :=
  ((d.1.1.1, d.1.2), d.2)

/-- The absorbed registers with the table register `t`. -/
abbrev absIns (t : A.OuterTab Req₂ Resp₂)
    (s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁) :
    AbsD A Req₁ Resp₁ Req₂ Resp₂ :=
  (((s.1.1, t), s.1.2), s.2)

omit [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
/-- The empty table replies `none`. -/
theorem tabAt_tab₀ (c : ℕ) (q : Req₂) : A.tabAt (tab₀ (Resp₂ := Resp₂) A) c q = none := by
  unfold AdaptiveIAlg.tabAt
  by_cases h : c < A.slots
  · rw [dif_pos h]
    rfl
  · rw [dif_neg h]

omit [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] in
/-- Before step `0` and from step `slots + 1` on, the table's handling is trivial. -/
theorem afterAtTab_of_not {k : ℕ} (h : ¬ (0 < k ∧ k - 1 < A.slots)) :
    A.afterAtTab F k = Equiv.refl _ :=
  dif_neg h

/-- **Before step `j + 1`, the table's handling of slot `j`**, read at the table register. -/
theorem afterAtTab_succ (j : Fin A.slots) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    A.afterAtTab F ((j : ℕ) + 1) d =
      absIns A d.1.1.2 (A.afterPermTab F d.1.1.2 j (absStrip A d)) := by
  obtain ⟨j, hj⟩ := j
  unfold AdaptiveIAlg.afterAtTab
  rw [dif_pos ⟨Nat.succ_pos j, by simpa using hj⟩]
  simp only [Nat.add_sub_cancel]
  rfl

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- Storing the main reply of slot `j` changes nothing without a logged request. -/
theorem storePerm_of_none (j : Fin A.slots)
    {s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁}
    (h : s.1.1.logs j = none) : A.storePerm j s = s := by
  change (if (s.1.1.logs j).isSome then _ else s) = s
  simp [h]

omit [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Fintype Req₁] [Fintype
  Resp₁] [DecidableEq Resp₁] in
/-- After slot `j` with no request logged, the table's handling changes nothing. -/
theorem afterPermTab_of_none (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    {s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁}
    (h : s.1.1.logs j = none) : A.afterPermTab F t j s = s := by
  have h2 : A.answerPermTab F t j s = s := by
    change (match s.1.1.logs j with | none => s | some r => _) = s
    rw [h]
  have h3 : A.clearPerm F.base j s = s := by
    change (match s.1.1.logs j with | none => s | some r => _) = s
    rw [h]
  rw [AdaptiveIAlg.afterPermTab, Equiv.trans_apply, Equiv.trans_apply, storePerm_of_none A j h, h2,
    h3]

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂] [DecidableEq Req₂] [Fintype
  Resp₂] [DecidableEq Resp₂] in
/-- **After slot `j` with request `r` logged, with the table `t`.** -/
theorem afterPermTab_of_some (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) {r : Req}
    {s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁}
    (h : s.1.1.logs j = some r) :
    A.afterPermTab F t j s = ((⟨s.1.1.work, s.1.1.request,
        Equiv.swap none (A.tabAnswer F t s.1.1.logs j r s.1.2.2) s.1.1.response, s.1.1.logs,
        Function.update s.1.1.store j s.1.2.2⟩,
      Equiv.swap default (F.base.route (A.reqCount s.1.1.logs j) r) s.1.2.1, s.1.1.store j),
        s.2) := by
  have h1 : A.storePerm j s = ((⟨s.1.1.work, s.1.1.request, s.1.1.response, s.1.1.logs,
      Function.update s.1.1.store j s.1.2.2⟩, s.1.2.1, s.1.1.store j), s.2) := by
    change (if (s.1.1.logs j).isSome then _ else s) = _
    simp [h]
  rw [AdaptiveIAlg.afterPermTab, Equiv.trans_apply, Equiv.trans_apply, h1]
  change (A.clearPerm F.base j) (match s.1.1.logs j with | none => _ | some r => _) = _
  rw [h]
  change (match s.1.1.logs j with | none => _ | some r => _) = _
  rw [h]
  simp

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] in
/-- **The reply of the table at the count of the earlier outer requests, written in place of the
reply to `none`, is the table's handling of slot `j`** (`absOuterSwap` after the empty table's
handling), when `x` is the table's reply to the logged outer request. -/
theorem absOuterSwap_afterPermTab (tab : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (x : Option Resp₂)
    (s : DReg (A.AbsW (Resp' := Resp₁)) A.width (Bits m) (BitStr I J) Req₁ Resp₁)
    (hx : ∀ r q, s.1.1.logs j = some r → F.outer (A.reqCount s.1.1.logs j) r = some q →
      x = A.tabAt tab (A.outerCount F s.1.1.logs j) q) :
    absOuterSwap A F j x (absIns A (tab₀ A) (A.afterPermTab F (tab₀ A) j s)) =
      absIns A (tab₀ A) (A.afterPermTab F tab j s) := by
  rcases hl : s.1.1.logs j with _ | r
  · rw [afterPermTab_of_none A F _ j hl, afterPermTab_of_none A F _ j hl]
    simp only [absOuterSwap, Equiv.coe_fn_mk, hl]
  · rw [afterPermTab_of_some A F _ j hl, afterPermTab_of_some A F _ j hl]
    rcases hq : F.outer (A.reqCount s.1.1.logs j) r with _ | q
    · simp only [absOuterSwap, Equiv.coe_fn_mk, hl, hq, AdaptiveIAlg.tabAnswer]
    · simp only [absOuterSwap, Equiv.coe_fn_mk, hl, hq, AdaptiveIAlg.tabAnswer,
        TwoRelay.replyFix, Equiv.trans_apply, Equiv.swap_apply_self, tabAt_tab₀,
        hx r q hl hq]

/-- **Step `j + 1` reads the request point of slot `j` as the table**: the table's handling of
slot `j` at the empty table after the request point (`answerDelta`) is, across the table swap, the
handling at the table `tab`. -/
theorem afterAtTab_answerDelta (tab : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) (x : Option Resp₂)
    (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) (hd : d.1.1.2 = tab)
    (hx : ∀ r q, d.1.1.1.logs j = some r → F.outer (A.reqCount d.1.1.1.logs j) r = some q →
      x = A.tabAt tab (A.outerCount F d.1.1.1.logs j) q) :
    A.afterAtTab F ((j : ℕ) + 1) (answerDelta A F j x (absTabSwap A tab d)) =
      absTabSwap A tab (A.afterAtTab F ((j : ℕ) + 1) d) := by
  have h1 : A.afterAtTab F ((j : ℕ) + 1) (answerDelta A F j x (absTabSwap A tab d)) =
      absOuterSwap A F j x (A.afterAtTab F ((j : ℕ) + 1) (absTabSwap A tab d)) := by
    simp only [answerDelta, Equiv.trans_apply, Equiv.apply_symm_apply]
  have h2 : (absTabSwap A tab d).1.1.2 = tab₀ A := by
    change Equiv.swap tab (tab₀ A) d.1.1.2 = tab₀ A
    rw [hd, Equiv.swap_apply_left]
  rw [h1, afterAtTab_succ, afterAtTab_succ, h2]
  have h3 : absTabSwap A tab (absIns A d.1.1.2 (A.afterPermTab F d.1.1.2 j (absStrip A d))) =
      absIns A (tab₀ A) (A.afterPermTab F tab j (absStrip A d)) := by
    rw [hd]
    change (((_, Equiv.swap tab (tab₀ A) tab), _), _) = _
    rw [Equiv.swap_apply_left]
  rw [h3]
  exact absOuterSwap_afterPermTab A F tab j x (absStrip A d) hx

/-- **The entries of a step of the adversary absorbed with a table**: the adversary's lifted step
between the table's handling before it and the relayed request after it. -/
theorem stepTab_op_apply (k : StepIdx A.slots A.post) (r : (A.absorb F.base).R)
    (y x : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (A.stepTab F k).op r y x =
      (((A.liftedStep (Resp' := Resp₁) k).tensorId (A.OuterTab Req₂ Resp₂)).reindex
        ((A.absorb F.base).constSplit (A.OuterTab Req₂ Resp₂)).symm).op r.1.2
        ((A.tabLift F (A.setAt F.base k)).symm y) (A.afterAtTab F k x) := by
  rw [AdaptiveIAlg.stepTab_eq]
  exact KrausMap.ofPerm_comp_comp_op_apply _ _ _ r y x

/-- The table's handling keeps the table register. -/
theorem afterAtTab_table (k : ℕ) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    (A.afterAtTab F k d).1.1.2 = d.1.1.2 := by
  unfold AdaptiveIAlg.afterAtTab
  split <;> rfl

/-- **A step of the adversary absorbed with a table across the table swap**: its operator at the
swapped rows and a column `b'` whose handling before the step is the swapped handling of `b` is
the operator at `b`. -/
theorem stepTab_op_absTabSwap (tab : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post)
    (r : (A.absorb F.base).R) (a b b' : AbsD A Req₁ Resp₁ Req₂ Resp₂)
    (hb : A.afterAtTab F k b' = absTabSwap A tab (A.afterAtTab F k b)) :
    (A.stepTab F k).op r (absTabSwap A tab a) b' = (A.stepTab F k).op r a b := by
  rw [stepTab_op_apply, stepTab_op_apply, hb, KrausMap.tensorId_reindex_op_apply,
    KrausMap.tensorId_reindex_op_apply]
  change _ * (1 : Matrix (A.OuterTab Req₂ Resp₂) (A.OuterTab Req₂ Resp₂) ℂ)
      (Equiv.swap tab (tab₀ A) ((A.tabLift F (A.setAt F.base k)).symm a).1.1.2)
      (Equiv.swap tab (tab₀ A) (A.afterAtTab F k b).1.1.2) = _ * (1 : Matrix _ _ ℂ)
      ((A.tabLift F (A.setAt F.base k)).symm a).1.1.2 (A.afterAtTab F k b).1.1.2
  rw [Matrix.one_apply, Matrix.one_apply]
  simp only [(Equiv.swap tab (tab₀ A)).injective.eq_iff]
  rfl

/-- **A step of the adversary absorbed with a table keeps the table register.** -/
theorem stepTab_table {k : StepIdx A.slots A.post} {r : (A.absorb F.base).R}
    {a b : AbsD A Req₁ Resp₁ Req₂ Resp₂} (h : (A.stepTab F k).op r a b ≠ 0) :
    a.1.1.2 = b.1.1.2 := by
  rw [stepTab_op_apply, KrausMap.tensorId_reindex_op_apply] at h
  have h1 := right_ne_zero_of_mul h
  by_contra hne
  apply h1
  refine Matrix.one_apply_ne ?_
  change ((A.tabLift F (A.setAt F.base k)).symm a).1.1.2 ≠ (A.afterAtTab F k b).1.1.2
  rw [afterAtTab_table]
  exact hne

end AbsTab

/-! ### The request points read from the absorbed logs -/

section Logs

open GordieHowe.QROM

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)

/-- **The request of the request point `k` read from absorbed logs** `lg` (as `reqV`). -/
def reqLog (k : ℕ) (lg : LogReg Req A.slots) : Req₂ :=
  match answerSlot A C₁ k with
  | none => d₂
  | some j => match lg j with
    | none => d₂
    | some r => (F.outer (A.reqCount lg j) r).getD d₂

/-- **The requests before the request point `k` read from absorbed logs** (as `histV`). -/
def histLog (T k : ℕ) (lg : LogReg Req A.slots) : LogReg Req₂ (T + 1) :=
  fun i => if (i : ℕ) < k then some (reqLog A C₁ F d₂ i lg) else none

/-- **The reply of the table `tab` at the request point `k` read from absorbed logs** (as
`repV`). -/
def repLog (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (lg : LogReg Req A.slots) : Option Resp₂ :=
  A.tabAt tab (ReqQueryAlg.countND d₂ (requestsBefore (histLog A C₁ F d₂ T k lg) k))
    (reqLog A C₁ F d₂ k lg)

/-- `repV` reads the absorbed logs. -/
theorem repV_eq_repLog (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (c : (bridgeCompose A C₁ F).V) :
    repV A C₁ F d₂ tab T k c = repLog A C₁ F d₂ tab T k c.1.adv.1.1.1.1.logs :=
  rfl

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **A step that reads slot `j`'s reply is the end of slot `j`.** -/
theorem answerSlot_eq_some {k : ℕ} {j : Fin A.slots} (h : answerSlot A C₁ k = some j) :
    k = ((j : ℕ) + 1) * (C₁.q + A.width) := by
  unfold answerSlot at h
  split_ifs at h with hk
  obtain rfl := Option.some_injective _ h
  change k = (k / (C₁.q + A.width) - 1 + 1) * (C₁.q + A.width)
  rw [Nat.sub_add_cancel hk.2.1, Nat.div_mul_cancel hk.1]

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **The end of slot `j` reads slot `j`'s reply.** -/
theorem answerSlot_mul (j : Fin A.slots) :
    answerSlot A C₁ (((j : ℕ) + 1) * (C₁.q + A.width)) = some j := by
  have hL : 0 < C₁.q + A.width := by have := A.width_pos; omega
  have hd : ((j : ℕ) + 1) * (C₁.q + A.width) / (C₁.q + A.width) = (j : ℕ) + 1 :=
    Nat.mul_div_cancel _ hL
  unfold answerSlot
  rw [dif_pos ⟨Dvd.intro_left _ rfl, by rw [hd]; omega, by rw [hd]; simp⟩]
  congr 1
  exact Fin.ext (by simp [hd])

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **No request point outside the ends of the slots.** -/
theorem answerSlot_eq_none {k : ℕ} (h : ∀ j < A.slots, k ≠ (j + 1) * (C₁.q + A.width)) :
    answerSlot A C₁ k = none := by
  rcases hs : answerSlot A C₁ k with _ | j
  · rfl
  · exact absurd (answerSlot_eq_some A C₁ hs) (h j j.isLt)

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂]
  [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁] in
/-- The requests before `n ≤ k` of `histLog T k` are those of the request points `0, …, n - 1`,
for `n ≤ T + 1`. -/
theorem requestsBefore_histLog (T k : ℕ) (lg : LogReg Req A.slots) :
    ∀ n, n ≤ k → n ≤ T + 1 →
      requestsBefore (histLog A C₁ F d₂ T k lg) n =
        (List.range n).map fun i => reqLog A C₁ F d₂ i lg
  | 0, _, _ => rfl
  | n + 1, h1, h2 => by
    rw [requestsBefore_succ_of_lt _ (by omega),
      requestsBefore_histLog T k lg n (by omega) (by omega),
      List.range_succ, List.map_append]
    simp only [histLog, show n < k by omega, ↓reduceIte, Option.toList_some, List.map_cons,
      List.map_nil]

/-- The number of the logged requests before slot `n` with an outer request at their request
number (`outerCount` at a natural number). -/
def outerCountN (lg : LogReg Req A.slots) (n : ℕ) : ℕ :=
  (((requestsBefore lg n).zipIdx).filter fun p => (F.outer p.2 p.1).isSome).length

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Fintype Req₂]
  [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁] in
/-- `outerCountN` after slot `n`: one more for an outer request logged at slot `n`. -/
theorem outerCountN_succ (lg : LogReg Req A.slots) (n : Fin A.slots) :
    outerCountN A F lg ((n : ℕ) + 1) = outerCountN A F lg n +
      (match lg n with
        | none => 0
        | some r => if (F.outer (A.reqCount lg n) r).isSome then 1 else 0) := by
  unfold outerCountN
  rw [requestsBefore_succ_of_lt _ n.isLt, List.zipIdx_append, List.filter_append,
    List.length_append]
  congr 1
  rcases h : lg ⟨n, n.isLt⟩ with _ | r
  · simp
  · simp only [Option.toList_some, List.zipIdx_cons, List.zipIdx_nil, zero_add]
    by_cases hq : (F.outer (A.reqCount lg n) r).isSome <;> simp [hq, AdaptiveIAlg.reqCount]

omit [Fintype Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Fintype Req₁] [DecidableEq Req₁] [Fintype
  Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **The count of the earlier requests other than the dummy is the count of the earlier outer
requests** (P6): at the end of slot `j`, the requests of the request points before it other than
`d₂` are the outer requests of the logged requests of the earlier slots, for a relay whose outer
requests are never `d₂`. -/
theorem countND_reqLog (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂) (lg : LogReg Req A.slots) :
    ∀ n < A.slots, ReqQueryAlg.countND d₂
      ((List.range ((n + 1) * (C₁.q + A.width))).map fun i => reqLog A C₁ F d₂ i lg) =
        outerCountN A F lg n := by
  have hL : 0 < C₁.q + A.width := by have := A.width_pos; omega
  -- the block of the queries of slot `n`, after its first, holds no request point
  have hblock : ∀ n : ℕ, ∀ i, i < C₁.q + A.width - 1 →
      reqLog A C₁ F d₂ (n * (C₁.q + A.width) + (i + 1)) lg = d₂ := fun n i hi => by
    unfold reqLog
    rw [answerSlot_eq_none A C₁ fun j _ he => ?_]
    have h1 : n * (C₁.q + A.width) < (j + 1) * (C₁.q + A.width) := by omega
    have h2 : (j + 1) * (C₁.q + A.width) < (n + 1) * (C₁.q + A.width) := by
      rw [Nat.add_mul n 1, one_mul]
      omega
    have h3 := Nat.lt_of_mul_lt_mul_right h1
    have h4 := Nat.lt_of_mul_lt_mul_right h2
    omega
  have hcnt : ∀ n : ℕ, ReqQueryAlg.countND d₂
      ((List.range (C₁.q + A.width)).map fun i => reqLog A C₁ F d₂ (n * (C₁.q + A.width) + i) lg) =
      ReqQueryAlg.countND d₂ [reqLog A C₁ F d₂ (n * (C₁.q + A.width)) lg] := fun n => by
    obtain ⟨L', hL'⟩ : ∃ L', C₁.q + A.width = L' + 1 := ⟨C₁.q + A.width - 1, by omega⟩
    rw [hL', List.range_succ_eq_map, List.map_cons, List.map_map]
    unfold ReqQueryAlg.countND
    rw [List.filter_cons, List.filter_cons]
    have hnil : (List.map ((fun i => reqLog A C₁ F d₂ (n * (L' + 1) + i) lg) ∘ Nat.succ)
        (List.range L')).filter (fun r => decide (r ≠ d₂)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      have := hblock n i (by rw [hL']; simpa using hi)
      rw [hL'] at this
      simp [this]
    simp only [Nat.add_zero, hnil, List.filter_nil]
  intro n hn
  induction n with
  | zero =>
    rw [zero_add, one_mul, ← zero_mul (C₁.q + A.width), ← Nat.zero_add (0 * (C₁.q + A.width))]
    have := hcnt 0
    simp only [zero_mul, zero_add] at this ⊢
    rw [this]
    unfold ReqQueryAlg.countND reqLog
    rw [answerSlot_eq_none A C₁ fun j _ he => by
      have := Nat.le_mul_of_pos_left (C₁.q + A.width) (show 0 < j + 1 by omega)
      omega]
    simp [outerCountN, requestsBefore]
  | succ n ih =>
    rw [show (n + 1 + 1) * (C₁.q + A.width) = (n + 1) * (C₁.q + A.width) + (C₁.q + A.width) by ring,
      List.range_add, List.map_append, List.map_map]
    unfold ReqQueryAlg.countND at ih ⊢
    rw [List.filter_append, List.length_append, ih (by omega)]
    have h := hcnt (n + 1)
    unfold ReqQueryAlg.countND at h
    rw [show ((fun i => reqLog A C₁ F d₂ i lg) ∘ fun x => (n + 1) * (C₁.q + A.width) + x) =
      fun i => reqLog A C₁ F d₂ ((n + 1) * (C₁.q + A.width) + i) lg from rfl, h,
      outerCountN_succ A F lg ⟨n, by omega⟩]
    congr 1
    unfold reqLog
    rw [answerSlot_mul A C₁ ⟨n, by omega⟩]
    dsimp only
    rcases hl : lg ⟨n, by omega⟩ with _ | r
    · simp
    · rcases hq : F.outer (A.reqCount lg ⟨n, by omega⟩) r with _ | q
      · simp [hq]
      · simp [hq, hout _ _ _ hq]

end Logs

/-! ### The writes and the table swap of the bridge on the adversary's registers -/

section Writes

open GordieHowe.QROM ProdPerm

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)

omit [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Fintype Req₁] [Fintype
  Resp₁] [DecidableEq Resp₁] in
/-- The table's handling of slot `j` acts on the registers other than the query pairs alone. -/
theorem afterPermTab_sndFix (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots) :
    SndFix (A.afterPermTab F t j) := fun p q q' => by
  rcases hl : p.1.logs j with _ | r
  · rw [afterPermTab_of_none A F t j (s := (p, q)) hl,
      afterPermTab_of_none A F t j (s := (p, q')) hl]
  · rw [afterPermTab_of_some A F t j (s := (p, q)) hl,
      afterPermTab_of_some A F t j (s := (p, q')) hl]

/-- The table's handling before step `k` acts on the registers other than the query pairs
alone. -/
theorem afterAtTab_sndFix (k : ℕ) : SndFix (A.afterAtTab F k) := by
  by_cases h : 0 < k ∧ k - 1 < A.slots
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    intro p q q'
    rw [afterAtTab_succ A F ⟨n, by omega⟩ (p, q), afterAtTab_succ A F ⟨n, by omega⟩ (p, q'),
      afterPermTab_sndFix A F _ _ ((p.1.1, p.2)) q q']
  · rw [afterAtTab_of_not A F h]
    exact sndFix_refl

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- `absOuterSwap` acts on the registers other than the query pairs alone. -/
theorem absOuterSwap_sndFix (j : Fin A.slots) (x : Option Resp₂) :
    SndFix (absOuterSwap A F j x) := fun p q q' => by
  simp only [absOuterSwap, Equiv.coe_fn_mk]
  rcases hl : p.1.1.logs j with _ | r
  · rfl
  · rcases hq : F.outer (A.reqCount p.1.1.logs j) r with _ | q₂
    · simp only [hq]
    · simp only [hq]

/-- The request point of slot `j` acts on the registers other than the query pairs alone. -/
theorem answerDelta_sndFix (j : Fin A.slots) (x : Option Resp₂) :
    SndFix (answerDelta A F j x) :=
  (afterAtTab_sndFix A F _).trans ((absOuterSwap_sndFix A F j x).trans
    (afterAtTab_sndFix A F _).symm)

/-- **The swap of the table register**, on the adversary's registers other than the query pairs. -/
def tabP (tab : A.OuterTab Req₂ Resp₂) :
    Equiv.Perm ((A.absorbTab F (tab₀ A)).W × Req₁ × Option Resp₁) :=
  Function.Involutive.toPerm (fun p => ((p.1.1, Equiv.swap tab (tab₀ A) p.1.2), p.2))
    fun p => by
      simp only [Equiv.swap_apply_self]

/-- **The write of the request point `k`** on the adversary's registers other than the query pairs:
at the end of slot `j`, `answerDelta` with the table's reply read from the absorbed logs. -/
noncomputable def writeP (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) :
    Equiv.Perm ((A.absorbTab F (tab₀ A)).W × Req₁ × Option Resp₁) :=
  match answerSlot A C₁ k with
  | none => Equiv.refl _
  | some j => ctrlFst (fun p : (A.absorbTab F (tab₀ A)).W × Req₁ × Option Resp₁ => p.1.1.logs)
      (fun lg => answerDelta A F j (repLog A C₁ F d₂ tab T k lg)) default
      (fun _ => answerDelta_sndFix A F j _) fun _ p q => answerDelta_logs A F j _ (p, q)

/-- **The table swap does not read the Kraus maps.** -/
theorem tabP_withStep
    (s : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)) (tab : A.OuterTab Req₂ Resp₂) :
    tabP (A.withStep s) F tab = tabP A F tab :=
  rfl

/-- `writeP` as `answerDelta` on the adversary's registers. -/
theorem writeP_spec (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (j : Fin A.slots)
    (hj : answerSlot A C₁ k = some j) (d : AbsD A Req₁ Resp₁ Req₂ Resp₂) :
    ((writeP A C₁ F d₂ tab T k d.1 : (A.absorbTab F (tab₀ A)).W × Req₁ × Option Resp₁), d.2) =
      answerDelta A F j (repLog A C₁ F d₂ tab T k d.1.1.1.logs) d := by
  unfold writeP
  rw [hj]
  exact (ctrlFst_spec (fun p : (A.absorbTab F (tab₀ A)).W × Req₁ × Option Resp₁ => p.1.1.logs)
      (fun lg => answerDelta A F j (repLog A C₁ F d₂ tab T k lg)) default
      (fun _ => answerDelta_sndFix A F j _) (fun _ p q => answerDelta_logs A F j _ (p, q))
      d.1 d.2).symm

/-- `writeP` is trivial at a step that is no request point. -/
theorem writeP_of_none (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (hk : answerSlot A C₁ k = none) :
    writeP A C₁ F d₂ tab T k = Equiv.refl _ := by
  unfold writeP
  rw [hk]

end Writes

/-! ### The bridge's composition across the table swap -/

section Bridge

open GordieHowe.QROM ProdPerm KindAlg

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)

/-- **The swap of the table register** on the workspace of the trace-preserving form. -/
def tabW (tab : A.OuterTab Req₂ Resp₂) :
    Equiv.Perm (A.absorbTab F (tab₀ A)).toTPKindAlg.W :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (A.AbsW (Resp' := Resp₁)))
    (Equiv.swap tab (tab₀ A))) (Equiv.refl (Fin (A.budget + 2)))

/-- **The write of the request point `k`** on the adversary's registers of the trace-preserving
form, the query counter kept. -/
noncomputable def writeW (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) :
    Equiv.Perm ((A.absorbTab F (tab₀ A)).toTPKindAlg.W × Req₁ × Option Resp₁) :=
  (A.absorbTab F (tab₀ A)).cntOne (writeP A C₁ F d₂ tab T k)

/-- `tabP` with the counter kept is `tabW` on the workspace. -/
theorem cntOne_tabP (tab : A.OuterTab Req₂ Resp₂) :
    ((A.absorbTab F (tab₀ A)).cntOne (tabP A F tab) :
      Equiv.Perm ((A.absorbTab F (tab₀ A)).toTPKindAlg.W × Req₁ × Option Resp₁)) =
      wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab) :=
  Equiv.ext fun _ => rfl

/-- The table swap keeps the kind. -/
theorem kind_tabW (tab : A.OuterTab Req₂ Resp₂) (x : (A.absorbTab F (tab₀ A)).toTPKindAlg.W) :
    (A.absorbTab F (tab₀ A)).toTPKindAlg.kind (tabW A F tab x) =
      (A.absorbTab F (tab₀ A)).toTPKindAlg.kind x :=
  rfl

/-- **The table swap of the composition** is the table swap of the adversary's workspace. -/
theorem tabSwap_eq (tab : A.OuterTab Req₂ Resp₂) :
    tabSwap A C₁ F tab = WorkRel.wa ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
      (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))) :=
  Equiv.ext fun _ => rfl

/-- **The write of the request point `k` of the composition** is `writeW` on the adversary's
registers. -/
theorem writeV_eq (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) :
    writeV A C₁ F d₂ tab T k = WorkRel.wa ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
      (writeW A C₁ F d₂ tab T k)) := by
  ext c : 1
  rcases h : answerSlot A C₁ k with _ | j
  · simp only [writeV, writeW, writeP, h]
    rfl
  · have key : answerDelta A F j (repV A C₁ F d₂ tab T k c) (absV A C₁ F c) =
        (writeP A C₁ F d₂ tab T k (absV A C₁ F c).1, (absV A C₁ F c).2) :=
      (writeP_spec A C₁ F d₂ tab T k j h (absV A C₁ F c)).symm
    simp only [writeV, h, liftV, Equiv.coe_fn_mk]
    rw [key]
    rfl

/-- `writeW` is trivial at a step that is no request point. -/
theorem writeW_of_none (tab : A.OuterTab Req₂ Resp₂) (T k : ℕ) (hk : answerSlot A C₁ k = none) :
    writeW A C₁ F d₂ tab T k = Equiv.refl _ := by
  rw [writeW, writeP_of_none A C₁ F d₂ tab T k hk]
  exact Equiv.ext fun _ => rfl

/-- **`stepTab_tabRel` with the adversary's Kraus maps replaced by `s`**, the table swap and the
writes of `A`: neither reads the Kraus maps. -/
theorem stepTab_tabRel_steps
    (s : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (tab : A.OuterTab Req₂ Resp₂) (T off : ℕ) (k : StepIdx A.slots A.post)
    (hk : (∃ j : Fin A.slots, answerSlot A C₁ off = some j ∧ (k : ℕ) = (j : ℕ) + 1) ∨
      (answerSlot A C₁ off = none ∧ ¬ (0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots)))
    (hoff : off ≤ T + 1) (r : (A.absorb F.base).R)
    (a b : DReg (A.absorbTab F (tab₀ A)).W A.width (Bits m) (BitStr I J) Req₁ Resp₁)
    (hb : b.1.1.2 = tab) :
    ((A.withStep s).stepTab F k).op r (tabP A F tab a.1, a.2)
        (((tabP A F tab).trans (writeP A C₁ F d₂ tab T off)) b.1, b.2) =
      ((A.withStep s).stepTab F k).op r a b := by
  refine stepTab_op_absTabSwap (A.withStep s) F tab k r a b _ ?_
  change A.afterAtTab F k _ = absTabSwap A tab (A.afterAtTab F k b)
  rcases hk with ⟨j, hj, hkj⟩ | ⟨hnone, hnot⟩
  · have e1 : (((tabP A F tab).trans (writeP A C₁ F d₂ tab T off)) b.1, b.2) =
        answerDelta A F j (repLog A C₁ F d₂ tab T off b.1.1.1.logs) (absTabSwap A tab b) :=
      writeP_spec A C₁ F d₂ tab T off j hj (absTabSwap A tab b)
    refine (congrArg (A.afterAtTab F k) e1).trans ?_
    rw [hkj]
    refine afterAtTab_answerDelta A F tab j _ b hb fun r q hl hq => ?_
    have hoffe := answerSlot_eq_some A C₁ hj
    subst hoffe
    unfold repLog
    rw [requestsBefore_histLog A C₁ F d₂ T _ _ _ le_rfl hoff,
      countND_reqLog A C₁ F d₂ hout _ j j.isLt]
    congr 1
    unfold reqLog
    rw [answerSlot_mul A C₁ j]
    simp [hl, hq]
  · rw [writeP_of_none A C₁ F d₂ tab T off hnone, afterAtTab_of_not A F hnot]
    rfl

/-- **A step of the adversary absorbed with the empty table across the table swap, after the write
of the request point `off`**: at the step after slot `j` with `off` the end of slot `j`, the step
absorbs the write (`afterAtTab_answerDelta`, with the count identity `countND_reqLog`); at a step
whose handling and write are trivial, it commutes with the swap. -/
theorem stepTab_tabRel (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (tab : A.OuterTab Req₂ Resp₂) (T off : ℕ) (k : StepIdx A.slots A.post)
    (hk : (∃ j : Fin A.slots, answerSlot A C₁ off = some j ∧ (k : ℕ) = (j : ℕ) + 1) ∨
      (answerSlot A C₁ off = none ∧ ¬ (0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots)))
    (hoff : off ≤ T + 1) (r : (A.absorb F.base).R)
    (a b : DReg (A.absorbTab F (tab₀ A)).W A.width (Bits m) (BitStr I J) Req₁ Resp₁)
    (hb : b.1.1.2 = tab) :
    (A.stepTab F k).op r (tabP A F tab a.1, a.2)
        (((tabP A F tab).trans (writeP A C₁ F d₂ tab T off)) b.1, b.2) =
      (A.stepTab F k).op r a b :=
  stepTab_tabRel_steps A C₁ F d₂ A.step hout tab T off k hk hoff r a b hb

/-- **The per-step facts of the bridge's steps `st`**: the composition at `st` is
trace-preserving step by step (`tp`), every step keeps the table register (`keeps`), and every
step absorbs, across the table swap, the write of the request point `off` before it (`rel`, at the
offsets `stepCase` yields). -/
structure BridgeStepsOK (st : BridgeSteps A F) : Prop where
  tp : ({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } :
    KindAlg _ O).StepsTP
  keeps : ∀ (tab : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post),
    KindAlg.DKeeps (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) {w | w.1.2 = tab} (st k)
  rel : ∀ (tab : A.OuterTab Req₂ Resp₂) (T off : ℕ) (k : StepIdx A.slots A.post),
    ((∃ j : Fin A.slots, answerSlot A C₁ off = some j ∧ (k : ℕ) = (j : ℕ) + 1) ∨
      (answerSlot A C₁ off = none ∧ ¬ (0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots))) →
    off ≤ T + 1 →
    KindAlg.DRel (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))
      ((wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab)).trans (writeW A C₁ F d₂ tab T off))
      {w | w.1.2 = tab} (st k)

/-- **The base's steps keep the table register**, for a trace-preserving adversary. -/
theorem dkeeps_toTP (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂)
    (k : StepIdx A.slots A.post) :
    KindAlg.DKeeps (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) {w | w.1.2 = tab} ((A.absorbTab F (tab₀ A)).toTPKindAlg.step k) := by
  have hA' : ∀ k, ((A.absorbTab F (tab₀ A)).step k).haltOp = 0 := fun k =>
    AdaptiveIAlg.TracePreserving.haltOp_eq_zero (A.absorbTab_tracePreserving F hA (tab₀ A)) k
  exact AdaptiveIAlg.dkeeps_toTPKindAlg hA' (Sd := {w | w.2 = tab}) (k := k)
    fun r a b hb hne => (stepTab_table A F hne).trans hb

/-- **The base's steps satisfy `BridgeStepsOK`**, for a trace-preserving adversary and a relay
whose outer requests are never `d₂` (`stepTab_tabRel`). -/
theorem bridgeStepsOK_toTP (hA : A.TracePreserving)
    (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂) :
    BridgeStepsOK A C₁ F d₂ (A.absorbTab F (tab₀ A)).toTPKindAlg.step := by
  have hA' : ∀ k, ((A.absorbTab F (tab₀ A)).step k).haltOp = 0 := fun k =>
    AdaptiveIAlg.TracePreserving.haltOp_eq_zero (A.absorbTab_tracePreserving F hA (tab₀ A)) k
  refine ⟨AdaptiveIAlg.stepsTP_toTPKindAlg _, fun tab k => ?_, fun tab T off k hk hoff => ?_⟩
  · exact dkeeps_toTP A F hA tab k
  · exact AdaptiveIAlg.drel_toTPKindAlg hA' (ρ' := tabP A F tab)
      (ρ := (tabP A F tab).trans (writeP A C₁ F d₂ tab T off)) (fun _ => rfl)
      (Sd := {w | w.2 = tab}) (k := k)
      fun r a b hb => stepTab_tabRel A C₁ F d₂ hout tab T off k hk hoff r a b hb

/-- **The steps with the adversary's Kraus maps replaced by `s₀` satisfy `BridgeStepsOK`**, for
trace-preserving Kraus maps and a relay whose outer requests are never `d₂`: the steps of the
trace-preserving form of `A.withStep s₀` absorbed with the empty table, at the registers of `A`'s
(`AdaptiveIAlg.tpStepOf`). -/
theorem bridgeStepsOK_steps
    (s₀ : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width (Bits m) (BitStr I J) Req Resp)
      (DReg A.W A.width (Bits m) (BitStr I J) Req Resp))
    (hA : (A.withStep s₀).TracePreserving) (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂) :
    BridgeStepsOK A C₁ F d₂ ((A.absorbTab F (tab₀ A)).tpStepOf false
      ((A.withStep s₀).stepTab F)) := by
  have hA' : ∀ k, (((A.withStep s₀).stepTab F) k).haltOp = 0 := fun k =>
    AdaptiveIAlg.TracePreserving.haltOp_eq_zero
      ((A.withStep s₀).absorbTab_tracePreserving F hA (tab₀ A)) k
  refine ⟨fun k => (A.absorbTab F (tab₀ A)).tpStepOf_tp false _ k, fun tab k => ?_,
    fun tab T off k hk hoff => ?_⟩
  · exact AdaptiveIAlg.dkeeps_tpStepOf (A := A.absorbTab F (tab₀ A))
      (st := (A.withStep s₀).stepTab F) hA' (Sd := {w | w.2 = tab}) (k := k)
      fun r a b hb hne => (stepTab_table (A.withStep s₀) F hne).trans hb
  · exact AdaptiveIAlg.drel_tpStepOf (A := A.absorbTab F (tab₀ A))
      (st := (A.withStep s₀).stepTab F) hA' (ρ' := tabP A F tab)
      (ρ := (tabP A F tab).trans (writeP A C₁ F d₂ tab T off)) (fun _ => rfl)
      (Sd := {w | w.2 = tab}) (k := k)
      fun r a b hb => stepTab_tabRel_steps A C₁ F d₂ s₀ hout tab T off k hk hoff r a b hb

/-- **The adversary's Kraus map `k` of the composition at the steps `st` across the table swap**,
after the write of the request point `off`, and it keeps the table register (`BridgeStepsOK`). -/
theorem advKraus_tabRelAt {st : BridgeSteps A F} (hst : BridgeStepsOK A C₁ F d₂ st)
    (tab : A.OuterTab Req₂ Resp₂) (T off : ℕ) (k : StepIdx A.slots A.post)
    (hk : (∃ j : Fin A.slots, answerSlot A C₁ off = some j ∧ (k : ℕ) = (j : ℕ) + 1) ∨
      (answerSlot A C₁ off = none ∧ ¬ (0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots)))
    (hoff : off ≤ T + 1) :
    WorkRel.Rel ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
          (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab)))
        (((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
          (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))).trans
          ((A.absorbTab F (tab₀ A)).toTPKindAlg.wOf C₁ (writeW A C₁ F d₂ tab T) off))
        ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ {w | w.1.2 = tab})
        (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } : KindAlg _ O).advKraus C₁ k) ∧
      WorkRel.Keeps ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ {w | w.1.2 = tab})
        (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } : KindAlg _ O).advKraus C₁ k) := by
  refine ⟨?_, keeps_advKraus (B := { (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st }) (hst.keeps tab k)⟩
  rw [wOf, advOne_trans]
  exact rel_advKraus (B := { (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st }) (hst.rel tab T off k hk hoff)

/-- **The adversary's Kraus map `k` of the composition across the table swap**, after the write
of the request point `off` (`stepTab_tabRel`), and it keeps the table register. -/
theorem advKraus_tabRel (hA : A.TracePreserving) (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (tab : A.OuterTab Req₂ Resp₂) (T off : ℕ) (k : StepIdx A.slots A.post)
    (hk : (∃ j : Fin A.slots, answerSlot A C₁ off = some j ∧ (k : ℕ) = (j : ℕ) + 1) ∨
      (answerSlot A C₁ off = none ∧ ¬ (0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots)))
    (hoff : off ≤ T + 1) :
    WorkRel.Rel ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
          (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab)))
        (((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
          (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))).trans
          ((A.absorbTab F (tab₀ A)).toTPKindAlg.wOf C₁ (writeW A C₁ F d₂ tab T) off))
        ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ {w | w.1.2 = tab})
        ((A.absorbTab F (tab₀ A)).toTPKindAlg.advKraus C₁ k) ∧
      WorkRel.Keeps ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ {w | w.1.2 = tab})
        ((A.absorbTab F (tab₀ A)).toTPKindAlg.advKraus C₁ k) :=
  advKraus_tabRelAt A C₁ F d₂ (bridgeStepsOK_toTP A C₁ F d₂ hA hout) tab T off k hk hoff

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **The request point at the adversary's step `n + b`**: before slot `n` (`b = 0`) or before post
batch `b` (`n = slots`), the offset `n · (q + width) + b · width` is the end of slot `j` with
`n + b = j + 1`, or it is no request point and the step's handling is trivial. -/
theorem stepCase (n b : ℕ) (h1 : b = 0 → n ≤ A.slots) (h2 : b ≠ 0 → n = A.slots) :
    (∃ j : Fin A.slots, answerSlot A C₁ (n * (C₁.q + A.width) + b * A.width) = some j ∧
        n + b = (j : ℕ) + 1) ∨
      (answerSlot A C₁ (n * (C₁.q + A.width) + b * A.width) = none ∧
        ¬ (0 < n + b ∧ n + b - 1 < A.slots)) := by
  have hW := A.width_pos
  by_cases hb : b = 0
  · subst hb
    simp only [zero_mul, add_zero]
    rcases n with _ | n
    · refine Or.inr ⟨answerSlot_eq_none A C₁ fun j _ he => ?_, by omega⟩
      have := Nat.le_mul_of_pos_left (C₁.q + A.width) (show 0 < j + 1 by omega)
      omega
    · exact Or.inl ⟨⟨n, by have := h1 rfl; omega⟩, answerSlot_mul A C₁ ⟨n, _⟩, rfl⟩
  · have hn := h2 hb
    subst hn
    refine Or.inr ⟨answerSlot_eq_none A C₁ fun j hj he => ?_, by omega⟩
    have h3 := Nat.mul_le_mul_right (C₁.q + A.width) (show j + 1 ≤ A.slots by omega)
    have h4 := Nat.le_mul_of_pos_left A.width (show 0 < b by omega)
    omega

/-- **The composition's circuit is along the table swap with the writes of the table** `tab`, for
a trace-preserving adversary, a relay whose outer requests are never `d₂`, and `T` at least the
query depth. -/
theorem relAt_bridgeAt {st : BridgeSteps A F} (hst : BridgeStepsOK A C₁ F d₂ st)
    (tab : A.OuterTab Req₂ Resp₂) (T : ℕ)
    (hT : A.slots * (C₁.q + A.width) + A.post * A.width ≤ T) :
    ReprogrammedCircuit.RelAt ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab)))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.wOf C₁ (writeW A C₁ F d₂ tab T))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ {w | w.1.2 = tab})
      (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } :
        KindAlg _ O).fullCircBoth C₁) 0
      (((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))).trans
        ((A.absorbTab F (tab₀ A)).toTPKindAlg.wOf C₁ (writeW A C₁ F d₂ tab T) 0))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))) := by
  have hW := A.width_pos
  refine relAt_fullCircBoth (B := { (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st })
    (kind_tabW A F tab)
    (fun k h => writeW_of_none A C₁ F d₂ tab T k (answerSlot_eq_none A C₁ h)) (fun j => ?_)
    (fun b => ?_) ?_
  · have h := stepCase A C₁ j 0 (fun _ => j.isLt.le) (fun h => absurd rfl h)
    simp only [zero_mul, add_zero] at h
    have hle : (j : ℕ) * (C₁.q + A.width) ≤ A.slots * (C₁.q + A.width) :=
      Nat.mul_le_mul_right _ j.isLt.le
    exact advKraus_tabRelAt A C₁ F d₂ hst tab T ((j : ℕ) * (C₁.q + A.width)) (slotStep j) h
      (by omega)
  · have h := stepCase A C₁ A.slots b (fun _ => le_rfl) (fun _ => rfl)
    have hle : (b : ℕ) * A.width ≤ A.post * A.width := Nat.mul_le_mul_right _ b.isLt.le
    exact advKraus_tabRelAt A C₁ F d₂ hst tab T
      (A.slots * (C₁.q + A.width) + (b : ℕ) * A.width) (postStep b) h (by omega)
  · have h := stepCase A C₁ A.slots A.post (fun _ => le_rfl) (fun _ => rfl)
    exact advKraus_tabRelAt A C₁ F d₂ hst tab T
      (A.slots * (C₁.q + A.width) + A.post * A.width) lastStep h (by omega)

/-- **The composition's circuit is along the table swap with the writes of the table** `tab`, for
a trace-preserving adversary, a relay whose outer requests are never `d₂`, and `T` at least the
query depth. -/
theorem relAt_bridge (hA : A.TracePreserving) (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (tab : A.OuterTab Req₂ Resp₂) (T : ℕ)
    (hT : A.slots * (C₁.q + A.width) + A.post * A.width ≤ T) :
    ReprogrammedCircuit.RelAt ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab)))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.wOf C₁ (writeW A C₁ F d₂ tab T))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ {w | w.1.2 = tab})
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁) 0
      (((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))).trans
        ((A.absorbTab F (tab₀ A)).toTPKindAlg.wOf C₁ (writeW A C₁ F d₂ tab T) 0))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advOne C₁
        (wsOne (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) (tabW A F tab))) :=
  relAt_bridgeAt A C₁ F d₂ (bridgeStepsOK_toTP A C₁ F d₂ hA hout) tab T hT

/-- **The query depth of the composition at the steps `st`.** -/
theorem depth_bridgeComposeAt (st : BridgeSteps A F) :
    (bridgeComposeAt A C₁ F st).depth = A.slots * (C₁.q + A.width) + A.post * A.width := by
  show (ReprogrammedCircuit.toCircuit _).queries = _
  rw [ReprogrammedCircuit.queries_toCircuit, queries_fullCircBoth]
  change A.slots * (C₁.q + A.width) + A.width * A.post = _
  ring

/-- **The query depth of the composition.** -/
theorem depth_bridgeCompose :
    (bridgeCompose A C₁ F).depth = A.slots * (C₁.q + A.width) + A.post * A.width :=
  depth_bridgeComposeAt A C₁ F _

open QROM.KrausRel in
/-- **`BridgeHopAt`**: on every column whose table register holds `tab`, Kraus map `i` of the
composition at the steps `st` read after the request point `i` and along the table swap is Kraus
map `i`, for steps with `BridgeStepsOK` and `T` at least the query depth. -/
theorem bridgeHopAt {st : BridgeSteps A F} (hst : BridgeStepsOK A C₁ F d₂ st)
    (tab : A.OuterTab Req₂ Resp₂) (T : ℕ) (hT : (bridgeComposeAt A C₁ F st).depth ≤ T) :
    BridgeHopAt A C₁ F d₂ st tab T := by
  intro i
  have hT' := hT
  rw [depth_bridgeComposeAt] at hT'
  have h := ReprogrammedCircuit.relAt_toAlg_step (relAt_bridgeAt A C₁ F d₂ hst tab T hT')
    (MState.withAnc KindAlg.x₀ (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } :
      KindAlg _ O).initSys C₁))
    (fun v => id v.1) i
  rw [tabSwap_eq, writeV_eq]
  exact WorkRel.Rel.opRel_permConj fun r a b hb => h.1 r a b hb

open QROM.KrausRel in
/-- **`BridgeHop`**: `bridgeHopAt` at the base's steps, for a trace-preserving adversary, a relay
whose outer requests are never `d₂`, and `T` at least the query depth. -/
theorem bridgeHop (hA : A.TracePreserving) (hout : ∀ c r q, F.outer c r = some q → q ≠ d₂)
    (tab : A.OuterTab Req₂ Resp₂) (T : ℕ) (hT : (bridgeCompose A C₁ F).depth ≤ T) :
    BridgeHop A C₁ F d₂ tab T :=
  bridgeHopAt A C₁ F d₂ (bridgeStepsOK_toTP A C₁ F d₂ hA hout) tab T hT

open QROM.KrausRel in
/-- **`BridgeKeepsAt`**: every Kraus map of the composition at the steps `st` keeps the table
register, for steps whose every step keeps it. -/
theorem bridgeKeepsAt {st : BridgeSteps A F}
    (hst : ∀ (tab : A.OuterTab Req₂ Resp₂) (k : StepIdx A.slots A.post),
      KindAlg.DKeeps (B := (A.absorbTab F (tab₀ A)).toTPKindAlg) {w | w.1.2 = tab} (st k))
    (tab : A.OuterTab Req₂ Resp₂) : BridgeKeepsAt A C₁ F st tab := by
  intro i
  have hK : ∀ k : StepIdx A.slots A.post,
      WorkRel.Keeps ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ {w | w.1.2 = tab})
        (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } : KindAlg _ O).advKraus C₁ k) :=
    fun k => keeps_advKraus (B := { (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st }) (hst tab k)
  have hR := relAt_fullCircBoth (B := { (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st }) (Ch := C₁)
    (φ := Equiv.refl _) (ψ := fun _ => Equiv.refl _) (Sw := {w | w.1.2 = tab}) (fun _ => rfl)
    (fun _ _ => rfl) (fun j => ⟨fun _ _ _ _ => rfl, hK _⟩) (fun b => ⟨fun _ _ _ _ => rfl, hK _⟩)
    ⟨fun _ _ _ _ => rfl, hK _⟩
  exact (ReprogrammedCircuit.relAt_toAlg_step hR
    (MState.withAnc KindAlg.x₀ (({ (A.absorbTab F (tab₀ A)).toTPKindAlg with step := st } :
      KindAlg _ O).initSys C₁))
    (fun v => id v.1) i).2.keeps

open QROM.KrausRel in
/-- **`BridgeKeeps`**: every Kraus map of the composition keeps the table register, for a
trace-preserving adversary. -/
theorem bridgeKeeps (hA : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂) :
    BridgeKeeps A C₁ F tab :=
  bridgeKeepsAt A C₁ F (dkeeps_toTP A F hA) tab

end Bridge

end GordieHowe.Quantum
