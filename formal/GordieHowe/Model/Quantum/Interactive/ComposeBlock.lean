-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.BlockPair
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeCirc
public import GordieHowe.Model.Quantum.Interactive.BlockRel

@[expose] public section

/-!
# Two circuits on the blocks of a label

Two reprogrammed circuits of the same shape (`ReprogrammedCircuit.BTwin`), along states of twin
circuits (`TwinState`: sets of work registers of the two circuits and a permutation carrying the
first onto the second on the block): the same reprogrammed queries, whose assignments do not see
the permutation; the same block isometries (`QROM.BlockIso`) keeping the current sets
(`QROM.SetIso`) and agreeing with themselves along the permutation, their operators relabelled; and,
at most once between two queries, changed gates moving to the next state that agree on the rows
with label `none` with the same overlaps (`QROM.PairNone`) and on the block `r` along the next and
the current permutation (`QROM.PairOn`).

- `BTwin.segs`, `BTwin.alg`, `Circuit.toAlg_eq_of_seg`: the segments of the compiled circuits
  are such pairs, and the second's compiled algorithm is the first's with other Kraus maps.
- `BTwin.alg_block`: the two compiled algorithms satisfy `Alg.BlockNone` and `Alg.BlockRel`.
- `KindAlg.twin_fullCircBoth`, `KindAlg.composeBothOut_block`: the composition of a core algorithm
  with run-time kinds and a challenger, against the composition with other Kraus maps, at the
  identity permutations, from step hypotheses on the adversary's registers (`KindAlg.StepPairs`)
  along sets closed under changes of the response.
- `AdaptiveIAlg.pairs_of_block`, `AdaptiveIAlg.pairs_of_block_perm`: the step hypotheses from
  `BlockRel` and `BlockNone`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

variable {V X Y L : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [DecidableEq L] (ℓ : V → Option L)

/-! ### Gates on the registers with the ancilla -/

theorem onFst_liftAnc {R : Type} [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) :
    OnFst (ancSplit V X Y) K K.liftAnc := fun r p' p =>
  WorkRel.liftAnc_op_apply K r p' p

variable {ℓ}

theorem ancSplit_wq_wa (τ : Equiv.Perm V) (p : ReprogrammedQueryReg V X Y) :
    ancSplit V X Y (WorkRel.wq (WorkRel.wa τ) p) =
      (WorkRel.wq τ (ancSplit V X Y p).1, (ancSplit V X Y p).2) :=
  rfl

theorem BlockIso.liftAnc {R : Type} [Fintype R]
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h : BlockIso (fun q : QueryReg V 1 X Y => ℓ q.1) K) :
    BlockIso (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) K.liftAnc :=
  (onFst_liftAnc K).blockIso h

theorem PairNone.liftAnc {R : Type} [Fintype R] {Sc Sr Sc' Sr' : Set V}
    {K K' : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h : PairNone (fun q : QueryReg V 1 X Y => ℓ q.1) {q | q.1 ∈ Sc} {q | q.1 ∈ Sr}
      {q | q.1 ∈ Sc'} {q | q.1 ∈ Sr'} K K') :
    PairNone (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) {p | p.1.1 ∈ Sc} {p | p.1.1 ∈ Sr}
      {p | p.1.1 ∈ Sc'} {p | p.1.1 ∈ Sr'} K.liftAnc K'.liftAnc :=
  (onFst_liftAnc K).pairNone (onFst_liftAnc K') h

theorem PairOn.liftAnc {R : Type} [Fintype R] {r : L} {ρ : Equiv.Perm R} {τr τc : Equiv.Perm V}
    {Sr Sc : Set V} {K K' : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h : PairOn (fun q : QueryReg V 1 X Y => ℓ q.1) r ρ (WorkRel.wq τr) (WorkRel.wq τc)
      {q | q.1 ∈ Sr} {q | q.1 ∈ Sc} K K') :
    PairOn (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) r ρ (WorkRel.wq (WorkRel.wa τr))
      (WorkRel.wq (WorkRel.wa τc)) {p | p.1.1 ∈ Sr} {p | p.1.1 ∈ Sc} K.liftAnc K'.liftAnc :=
  (onFst_liftAnc K).pairOn (ancSplit_wq_wa τr) (ancSplit_wq_wa τc) (onFst_liftAnc K') h

theorem SetIso.liftAnc {R : Type} [Fintype R] {S : Set V}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)} (h : SetIso {q | q.1 ∈ S} K) :
    SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S} K.liftAnc :=
  (onFst_liftAnc K).setIso h

/-- **A Kraus map agrees with itself along `τ` on both sides**, its operators relabelled by
`ρ`. -/
def SelfRel {ι R : Type} [Fintype ι] [DecidableEq ι] [Fintype R] (ρ : Equiv.Perm R)
    (π : Equiv.Perm ι) (K : KrausMap R ι ι) : Prop :=
  ∀ i a b, K.op (ρ i) (π a) (π b) = K.op i a b

theorem SelfRel.pairOn {ι R : Type} [Fintype ι] [DecidableEq ι] [Fintype R] {ℓι : ι → Option L}
    {ρ : Equiv.Perm R} {π : Equiv.Perm ι} {K : KrausMap R ι ι} (h : SelfRel ρ π K) (r : L)
    (Sr Sc : Set ι) : PairOn ℓι r ρ π π Sr Sc K K :=
  fun i a b _ _ _ _ => h i a b

theorem SelfRel.liftAnc {R : Type} [Fintype R] {ρ : Equiv.Perm R} {τ : Equiv.Perm V}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)} (h : SelfRel ρ (WorkRel.wq τ) K) :
    SelfRel ρ (WorkRel.wq (WorkRel.wa τ)) K.liftAnc := fun i a b => by
  rw [WorkRel.liftAnc_op_apply, WorkRel.liftAnc_op_apply]
  exact congrArg (· * _) (h i (a.1.1, a.2) (b.1.1, b.2))

theorem SelfRel.comp {ι R₁ R₂ : Type} [Fintype ι] [DecidableEq ι] [Fintype R₁] [Fintype R₂]
    {ρ₁ : Equiv.Perm R₁} {ρ₂ : Equiv.Perm R₂} {π : Equiv.Perm ι} {K₂ : KrausMap R₂ ι ι}
    {K₁ : KrausMap R₁ ι ι} (h₂ : SelfRel ρ₂ π K₂) (h₁ : SelfRel ρ₁ π K₁) :
    SelfRel (ρ₁.prodCongr ρ₂) π (K₂.comp K₁) := fun i a b => by
  change (K₂.op (ρ₂ i.2) * K₁.op (ρ₁ i.1)) (π a) (π b) = (K₂.op i.2 * K₁.op i.1) a b
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp π]
  exact Finset.sum_congr rfl fun m _ => by rw [h₂, h₁]

theorem selfRel_ofPerm {ι : Type} [Fintype ι] [DecidableEq ι] {g π : Equiv.Perm ι}
    (hg : ∀ x, g (π x) = π (g x)) : SelfRel (Equiv.refl Unit) π (KrausMap.ofPerm g) :=
  fun u a b => by simp only [Equiv.refl_apply, ofPerm_op_eq, hg, π.injective.eq_iff]

theorem selfRel_identity {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) :
    SelfRel (Equiv.refl Unit) π (KrausMap.identity ι) := fun u a b => by
  change (1 : Matrix ι ι ℂ) (π a) (π b) = (1 : Matrix ι ι ℂ) a b
  simp only [Matrix.one_apply, π.injective.eq_iff]

theorem selfRel_measureFn {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    {f : ι → M} {π : Equiv.Perm ι} {φ : Equiv.Perm M} (hf : ∀ x, f (π x) = φ (f x)) :
    SelfRel φ π (KrausMap.measureFn f) := fun o a b => by
  change Matrix.diagonal _ (π a) (π b) = Matrix.diagonal _ a b
  simp only [Matrix.diagonal_apply, π.injective.eq_iff, hf, φ.injective.eq_iff]

variable [AddGroup Y]

theorem blockIso_reprogSwap (a : V → List (Assignment X Y)) :
    BlockIso (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) (KrausMap.ofPerm (reprogSwap a)) :=
  BlockIso.ofPerm fun p => by
    rw [reprogSwap_apply]
    split_ifs <;> rfl

theorem blockIso_reprogAdd (a : V → List (Assignment X Y)) :
    BlockIso (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) (KrausMap.ofPerm (reprogAdd a)) :=
  BlockIso.ofPerm fun _ => rfl

theorem setIso_reprogSwap (a : V → List (Assignment X Y)) (S : Set V) :
    SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S} (KrausMap.ofPerm (reprogSwap a)) :=
  SetIso.ofPerm fun p => by
    rw [reprogSwap_apply]
    split_ifs <;> rfl

theorem setIso_reprogAdd (a : V → List (Assignment X Y)) (S : Set V) :
    SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S} (KrausMap.ofPerm (reprogAdd a)) :=
  SetIso.ofPerm fun _ => Iff.rfl

theorem selfRel_reprogSwap (a : V → List (Assignment X Y)) {τ : Equiv.Perm V}
    (ha : ∀ v, a (τ v) = a v) :
    SelfRel (Equiv.refl Unit) (WorkRel.wq (WorkRel.wa τ)) (KrausMap.ofPerm (reprogSwap a)) :=
  selfRel_ofPerm fun p => WorkRel.reprogSwap_wa a ha p

theorem selfRel_reprogAdd (a : V → List (Assignment X Y)) {τ : Equiv.Perm V}
    (ha : ∀ v, a (τ v) = a v) :
    SelfRel (Equiv.refl Unit) (WorkRel.wq (WorkRel.wa τ)) (KrausMap.ofPerm (reprogAdd a)) :=
  selfRel_ofPerm fun p => WorkRel.reprogAdd_wa a ha p

/-! ### Twin circuits -/

namespace ReprogrammedCircuit

variable (ℓ) (r : L)

/-- **A state of twin circuits**: the sets `S`, `S'` of work registers of the two circuits have
the same registers of label `none`, `τ` carries `S` onto `S'` on the block `r` and keeps the
label. -/
structure TwinState (S S' : Set V) (τ : Equiv.Perm V) : Prop where
  /-- The registers of label `none` are the same. -/
  none_eq : ∀ v, ℓ v = none → (v ∈ S' ↔ v ∈ S)
  /-- `τ` carries `S` onto `S'` on the block. -/
  set_eq : ∀ v, InBlock ℓ r v → (τ v ∈ S' ↔ v ∈ S)
  /-- `τ` keeps the label. -/
  label_eq : ∀ v, ℓ (τ v) = ℓ v

variable (Q : Set V → Set V → Equiv.Perm V → Prop)

/-- **Two reprogrammed circuits on the blocks of `ℓ`**, from the sets `S`, `S'` of work registers
of the two circuits, the permutation `τ` and the flag `b` at the start to `Se`, `Se'`, `τe`, `be`
at the end; the flag records whether the current query interval already has a changed gate. The
circuits have the same reprogrammed queries (each clearing the flag), whose assignments do not see
`τ`; the same block isometries keeping the current sets and agreeing with themselves along `τ`; and
changed gates `K`, `K'` (one per query interval, setting the flag and moving to the next state)
agreeing on the rows with label `none` with the same overlaps, and on the block `r` along the next
permutation on the rows and the current one on the columns. -/
inductive BTwin : ReprogrammedCircuit V X Y → ReprogrammedCircuit V X Y → Set V → Set V →
    Equiv.Perm V → Bool → Set V → Set V → Equiv.Perm V → Bool → Prop
  | nil {S S' : Set V} {τ : Equiv.Perm V} {b : Bool} : BTwin .nil .nil S S' τ b S S' τ b
  | same {R : Type} [Fintype R] {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
      {c c' : ReprogrammedCircuit V X Y} {S S' Se Se' : Set V} {τ τe : Equiv.Perm V}
      {b be : Bool} :
      BlockIso (fun q : QueryReg V 1 X Y => ℓ q.1) K → SetIso {q | q.1 ∈ S} K →
        SetIso {q | q.1 ∈ S'} K → (∃ ρ, PairOn (fun q : QueryReg V 1 X Y => ℓ q.1) r ρ
          (WorkRel.wq τ) (WorkRel.wq τ) {q | q.1 ∈ S} {q | q.1 ∈ S} K K) →
        BTwin c c' S S' τ b Se Se' τe be → BTwin (.kraus K c) (.kraus K c') S S' τ b Se Se' τe be
  | diff {R : Type} [Fintype R] {K K' : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
      {c c' : ReprogrammedCircuit V X Y} {S S' T T' Se Se' : Set V} {τ τ' τe : Equiv.Perm V}
      {be : Bool} :
      PairNone (fun q : QueryReg V 1 X Y => ℓ q.1) {q | q.1 ∈ S} {q | q.1 ∈ T} {q | q.1 ∈ S'}
          {q | q.1 ∈ T'} K K' →
        (∃ ρ, PairOn (fun q : QueryReg V 1 X Y => ℓ q.1) r ρ (WorkRel.wq τ') (WorkRel.wq τ)
          {q | q.1 ∈ T} {q | q.1 ∈ S} K K') →
        Q T T' τ' → BTwin c c' T T' τ' true Se Se' τe be →
          BTwin (.kraus K c) (.kraus K' c') S S' τ false Se Se' τe be
  | rquery {a : V → List (Assignment X Y)} {c c' : ReprogrammedCircuit V X Y}
      {S S' Se Se' : Set V} {τ τe : Equiv.Perm V} {b be : Bool} : (∀ v, a (τ v) = a v) →
      BTwin c c' S S' τ false Se Se' τe be →
        BTwin (.rquery a c) (.rquery a c') S S' τ b Se Se' τe be

variable {ℓ r Q}

/-- **Twin circuits concatenated.** -/
theorem BTwin.append {c c' d d' : ReprogrammedCircuit V X Y} {S S' Sm Sm' Se Se' : Set V}
    {τ τm τe : Equiv.Perm V} {b bm be : Bool} (h₁ : BTwin ℓ r Q c c' S S' τ b Sm Sm' τm bm)
    (h₂ : BTwin ℓ r Q d d' Sm Sm' τm bm Se Se' τe be) :
    BTwin ℓ r Q (c ++ d) (c' ++ d') S S' τ b Se Se' τe be := by
  induction h₁ with
  | nil => exact h₂
  | same hK hS hS' hτ _ ih => exact .same hK hS hS' hτ (ih h₂)
  | diff hn ho hst _ ih => exact .diff hn ho hst (ih h₂)
  | rquery ha _ ih => exact .rquery ha (ih h₂)

/-- **Concatenated circuits of block isometries and reprogrammed queries**, each twin with itself
at fixed sets and permutation from any flag to the cleared one: twin from `b` to `b` when the list
is empty, else to the cleared flag. -/
theorem BTwin.concat_same {S S' : Set V} {τ : Equiv.Perm V} :
    ∀ (cs : List (ReprogrammedCircuit V X Y)),
      (∀ x ∈ cs, ∀ b, BTwin ℓ r Q x x S S' τ b S S' τ false) →
      ∀ b, BTwin ℓ r Q (concat cs) (concat cs) S S' τ b S S' τ (if cs = [] then b else false)
  | [], _, b => by
    change BTwin ℓ r Q .nil .nil S S' τ b S S' τ
      (if ([] : List (ReprogrammedCircuit V X Y)) = [] then b else false)
    rw [if_pos rfl]
    exact .nil
  | c :: cs, h, b => by
    have h1 := h c (List.mem_cons_self ..) b
    have h2 := BTwin.concat_same cs (fun x hx => h x (List.mem_cons_of_mem _ hx)) false
    simp only [ite_self] at h2
    change BTwin ℓ r Q (c ++ concat cs) (c ++ concat cs) S S' τ b S S' τ
      (if c :: cs = [] then b else false)
    rw [if_neg (List.cons_ne_nil _ _)]
    exact h1.append h2

/-- **Concatenated twins along a chain of states**, piece `i` from state `i` to state `i + 1`
with the cleared flag at both ends. -/
theorem BTwin.concat_finRange :
    ∀ (n : ℕ) (f f' : Fin n → ReprogrammedCircuit V X Y) (T T' : ℕ → Set V)
      (P : ℕ → Equiv.Perm V),
      (∀ i : Fin n, BTwin ℓ r Q (f i) (f' i) (T i) (T' i) (P i) false (T (i + 1)) (T' (i + 1))
        (P (i + 1)) false) →
        BTwin ℓ r Q (concat ((List.finRange n).map f)) (concat ((List.finRange n).map f')) (T 0)
          (T' 0) (P 0) false (T n) (T' n) (P n) false
  | 0, _, _, _, _, _, _ => BTwin.nil
  | n + 1, f, f', T, T', P, h => by
    rw [List.finRange_succ, List.map_cons, List.map_cons, List.map_map, List.map_map]
    exact (h 0).append (BTwin.concat_finRange n (f ∘ Fin.succ) (f' ∘ Fin.succ)
      (fun i => T (i + 1)) (fun i => T' (i + 1)) (fun i => P (i + 1))
      fun i => by simpa [Nat.add_assoc] using h i.succ)

variable (ℓ r) in
/-- **Two segments of compiled circuits on the blocks**, from the sets `Sc`, `Sc'` and the
permutation `τc` to `Sr`, `Sr'`, `τr`: the second has the first's index type, agrees with it on
the rows with label `none` with the same overlaps, and agrees on the block `r` along `τr` on the
rows and `τc` on the columns, its operators relabelled. -/
def SegRel (Sc Sc' : Set V) (τc : Equiv.Perm V) (Sr Sr' : Set V) (τr : Equiv.Perm V)
    (G G' : IndexedKrausMap (ReprogrammedQueryReg V X Y)) : Prop :=
  ∃ K'' : KrausMap G.R (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y),
    G' = ⟨G.R, K''⟩ ∧ PairNone (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1)
      {p | p.1.1 ∈ Sc} {p | p.1.1 ∈ Sr} {p | p.1.1 ∈ Sc'} {p | p.1.1 ∈ Sr'} G.K K'' ∧
      ∃ ρ, PairOn (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) r ρ (WorkRel.wq (WorkRel.wa τr))
        (WorkRel.wq (WorkRel.wa τc)) {p | p.1.1 ∈ Sr} {p | p.1.1 ∈ Sc} G.K K''

/-- A segment twin with itself: a block isometry keeping the sets, agreeing with itself along the
permutation. -/
theorem SegRel.refl {S S' : Set V} {τ : Equiv.Perm V}
    {G : IndexedKrausMap (ReprogrammedQueryReg V X Y)}
    (h : BlockIso (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) G.K)
    (hS : SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S} G.K)
    (hS' : SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S'} G.K)
    (hτ : ∃ ρ, PairOn (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) r ρ
      (WorkRel.wq (WorkRel.wa τ)) (WorkRel.wq (WorkRel.wa τ)) {p | p.1.1 ∈ S} {p | p.1.1 ∈ S}
      G.K G.K) : SegRel ℓ r S S' τ S S' τ G G :=
  ⟨G.K, rfl, PairNone.refl h.keeps hS hS', hτ⟩

variable (ℓ r) in
/-- The head of a circuit after the interval's changed gate: equal in the two circuits, a block
isometry keeping the sets, agreeing with itself along the permutation. -/
def HeadSame (S S' : Set V) (τ : Equiv.Perm V)
    (G G' : IndexedKrausMap (ReprogrammedQueryReg V X Y)) :
    Prop :=
  G' = G ∧ BlockIso (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) G.K ∧
    SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S} G.K ∧
    SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S'} G.K ∧
    ∃ ρ, PairOn (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) r ρ (WorkRel.wq (WorkRel.wa τ))
      (WorkRel.wq (WorkRel.wa τ)) {p | p.1.1 ∈ S} {p | p.1.1 ∈ S} G.K G.K

theorem wq_wa_mem {S S' : Set V} {τ : Equiv.Perm V}
    (h : ∀ v, InBlock ℓ r v → (τ v ∈ S' ↔ v ∈ S)) (p : ReprogrammedQueryReg V X Y)
    (hp : InBlock (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) r p) :
    (WorkRel.wq (WorkRel.wa τ) p).1.1 ∈ S' ↔ p.1.1 ∈ S :=
  h p.1.1 hp

variable [AddGroup Y]

/-- **The segments of twin circuits**: states `T j`, `T' j`, `P j` with the start's at `0` such
that segment `j` is related from state `j` to state `j + 1` by `SegRel`; the first segment is
`HeadSame` when the flag is set at the start, and the state is the end's from the last segment
on. -/
theorem BTwin.segs {c c' : ReprogrammedCircuit V X Y} {S S' Se Se' : Set V} {τ τe : Equiv.Perm V}
    {b be : Bool} (h : BTwin ℓ r Q c c' S S' τ b Se Se' τe be)
    (hQ : ∀ S S' τ, Q S S' τ → TwinState ℓ r S S' τ) (hst : Q S S' τ) :
    ∃ (T T' : ℕ → Set V) (P : ℕ → Equiv.Perm V), T 0 = S ∧ T' 0 = S' ∧ P 0 = τ ∧
      (∀ j, Q (T j) (T' j) (P j)) ∧
      (∀ j, c.queries < j → T j = Se ∧ T' j = Se' ∧ P j = τe) ∧
      (b = true → T 1 = S ∧ T' 1 = S' ∧ P 1 = τ ∧
        HeadSame ℓ r S S' τ (Circuit.head (toCircuit c)) (Circuit.head (toCircuit c'))) ∧
      ∀ j, SegRel ℓ r (T j) (T' j) (P j) (T (j + 1)) (T' (j + 1)) (P (j + 1))
        (Circuit.seg (toCircuit c) j) (Circuit.seg (toCircuit c') j) := by
  induction h with
  | @nil S S' τ b =>
    refine ⟨fun _ => S, fun _ => S', fun _ => τ, rfl, rfl, rfl, fun _ => hst,
      fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl, rfl, BlockIso.identity,
      SetIso.identity _, SetIso.identity _, ⟨_, (selfRel_identity _).pairOn r _ _⟩⟩, fun j => ?_⟩
    rw [toCircuit, Circuit.seg_nil]
    exact SegRel.refl BlockIso.identity (SetIso.identity _) (SetIso.identity _)
      ⟨_, (selfRel_identity _).pairOn r _ _⟩
  | @same R _ K c c' S S' Se Se' τ τe b be hK hS hS' hτ _ ih =>
    obtain ⟨T, T', P, hT0, hT0', hP0, hst', hTe, hb, hseg⟩ := ih hst
    have hK' := BlockIso.liftAnc hK
    have hSl := SetIso.liftAnc hS
    have hSl' := SetIso.liftAnc hS'
    obtain ⟨ρK, hρK⟩ := hτ
    have hρl := PairOn.liftAnc hρK
    refine ⟨T, T', P, hT0, hT0', hP0, hst', hTe, fun hbt => ?_, fun j => ?_⟩
    · obtain ⟨h1, h1', h1'', h2, h3, h4, h4', ⟨ρ, h5⟩⟩ := hb hbt
      refine ⟨h1, h1', h1'', ?_, h3.comp hK', h4.comp hSl, h4'.comp hSl', ⟨_, h5.comp hρl
        hSl.keepsSet hSl'.keepsSet (fun i => (h3.keeps i).on _) (fun i => (h3.keeps i).on _)
        (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst).set_eq x hb).2 hx)
        (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst).set_eq x hb).1 hx)
        (fun x => (hQ _ _ _ hst).label_eq x.1.1) (fun x => (hQ _ _ _ hst).label_eq x.1.1)⟩⟩
      change (⟨_, (Circuit.head (toCircuit c')).K.comp K.liftAnc⟩ :
          IndexedKrausMap (ReprogrammedQueryReg V X Y)) =
        ⟨_, (Circuit.head (toCircuit c)).K.comp K.liftAnc⟩
      rw [h2]
    · cases j with
      | zero =>
        obtain ⟨K'', h1, h2, ρ, h3⟩ := hseg 0
        rw [hT0, hT0'] at h2
        rw [hT0, hP0] at h3
        rw [hT0, hT0', hP0]
        change ∃ K₃, (⟨_, (Circuit.head (toCircuit c')).K.comp K.liftAnc⟩ :
            IndexedKrausMap (ReprogrammedQueryReg V X Y)) = ⟨_, K₃⟩ ∧ _
        change Circuit.head (toCircuit c') = _ at h1
        rw [h1]
        refine ⟨K''.comp K.liftAnc, rfl, h2.comp_left hK' hSl hSl', ⟨_, h3.comp
          hρl hSl.keepsSet hSl'.keepsSet h2.keeps h2.keeps'
          (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst).set_eq x hb).2 hx)
          (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst).set_eq x hb).1 hx)
          (fun x => (hQ _ _ _ (hst' 1)).label_eq x.1.1) (fun x => (hQ _ _ _ hst).label_eq x.1.1)⟩⟩
      | succ j => exact hseg (j + 1)
  | @diff R _ K K' c c' S S' T₁ T₁' Se Se' τ τ' τe be hn ho hst₁ _ ih =>
    obtain ⟨T, T', P, hT0, hT0', hP0, hst', hTe, hb, hseg⟩ := ih hst₁
    obtain ⟨h1, h1', h1'', h2, h3, h4, h4', ⟨ρh, h5⟩⟩ := hb rfl
    obtain ⟨ρK, hoK⟩ := ho
    refine ⟨fun j => if j = 0 then S else T j, fun j => if j = 0 then S' else T' j,
      fun j => if j = 0 then τ else P j, rfl, rfl, rfl, fun j => ?_, fun j hj => ?_,
      fun h => absurd h (by simp), fun j => ?_⟩
    · by_cases hj : j = 0
      · simp only [hj, if_true]
        exact hst
      · simp only [hj, if_false]
        exact hst' j
    · simp only [show j ≠ 0 by omega, if_false]
      exact hTe j hj
    · cases j with
      | zero =>
        simp only [if_true, show (0 + 1 : ℕ) ≠ 0 by omega, if_false, h1, h1', h1'']
        change ∃ K₃, (⟨_, (Circuit.head (toCircuit c')).K.comp K'.liftAnc⟩ :
            IndexedKrausMap (ReprogrammedQueryReg V X Y)) = ⟨_, K₃⟩ ∧ _
        rw [h2]
        have hn' := PairNone.liftAnc hn
        refine ⟨(Circuit.head (toCircuit c)).K.comp K'.liftAnc, rfl, hn'.comp_right h3 h4 h4',
          ⟨_, h5.comp (PairOn.liftAnc hoK) hn'.keepsSet hn'.keepsSet'
            (fun i => (h3.keeps i).on _) (fun i => (h3.keeps i).on _)
            (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst).set_eq x hb).2 hx)
            (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst₁).set_eq x hb).1 hx)
            (fun x => (hQ _ _ _ hst₁).label_eq x.1.1) (fun x => (hQ _ _ _ hst₁).label_eq x.1.1)⟩⟩
      | succ j =>
        simp only [show j + 1 ≠ 0 by omega, show j + 1 + 1 ≠ 0 by omega, if_false]
        exact hseg (j + 1)
  | @rquery a c c' S S' Se Se' τ τe b be ha _ ih =>
    obtain ⟨T, T', P, hT0, hT0', hP0, hst', hTe, -, hseg⟩ := ih hst
    have hI : BlockIso (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1)
        ((KrausMap.identity _).comp (KrausMap.ofPerm (reprogSwap a))) :=
      BlockIso.identity.comp (blockIso_reprogSwap a)
    have hIS : ∀ S₀ : Set V, SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S₀}
        ((KrausMap.identity _).comp (KrausMap.ofPerm (reprogSwap a))) := fun S₀ =>
      (SetIso.identity _).comp (setIso_reprogSwap a S₀)
    have hIr : SelfRel ((Equiv.refl Unit).prodCongr (Equiv.refl Unit)) (WorkRel.wq (WorkRel.wa τ))
        ((KrausMap.identity _).comp (KrausMap.ofPerm (reprogSwap a))) :=
      (selfRel_identity _).comp (selfRel_reprogSwap a ha)
    have hD : BlockIso (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1)
        ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a))) :=
      (blockIso_reprogAdd a).comp (blockIso_reprogSwap a)
    have hDS : ∀ S₀ : Set V, SetIso {p : ReprogrammedQueryReg V X Y | p.1.1 ∈ S₀}
        ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a))) := fun S₀ =>
      (setIso_reprogAdd a S₀).comp (setIso_reprogSwap a S₀)
    have hDr : SelfRel ((Equiv.refl Unit).prodCongr (Equiv.refl Unit)) (WorkRel.wq (WorkRel.wa τ))
        ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a))) :=
      (selfRel_reprogAdd a ha).comp (selfRel_reprogSwap a ha)
    refine ⟨fun j => if j = 0 then S else T (j - 1), fun j => if j = 0 then S' else T' (j - 1),
      fun j => if j = 0 then τ else P (j - 1), rfl, rfl, rfl, fun j => ?_, fun j hj => ?_,
      fun _ => ⟨by simp [hT0], by simp [hT0'], by simp [hP0], rfl, hI, hIS _, hIS _,
        ⟨_, hIr.pairOn r _ _⟩⟩,
      fun j => ?_⟩
    · by_cases hj : j = 0
      · simp only [hj, if_true]
        exact hst
      · simp only [hj, if_false]
        exact hst' (j - 1)
    · have : j ≠ 0 := by simp [queries] at hj; omega
      simp only [this, if_false]
      exact hTe (j - 1) (by simp [queries] at hj; omega)
    · match j with
      | 0 =>
        simp only [if_true, show (0 + 1 : ℕ) ≠ 0 by omega, if_false, Nat.sub_self, hT0, hT0', hP0]
        exact SegRel.refl hI (hIS _) (hIS _) ⟨_, hIr.pairOn r _ _⟩
      | 1 =>
        simp only [show (1 : ℕ) ≠ 0 by omega, show (1 + 1 : ℕ) ≠ 0 by omega, if_false,
          Nat.sub_self, Nat.add_sub_cancel]
        obtain ⟨K'', h1, h2, ρ, h3⟩ := hseg 0
        rw [hT0, hT0'] at h2
        rw [hT0, hP0] at h3
        rw [hT0, hT0', hP0]
        change ∃ K₃, (⟨_, (Circuit.head (toCircuit c')).K.comp
            ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a)))⟩ :
            IndexedKrausMap (ReprogrammedQueryReg V X Y)) = ⟨_, K₃⟩ ∧ _
        change Circuit.head (toCircuit c') = _ at h1
        rw [h1]
        refine ⟨K''.comp ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a))),
          rfl, h2.comp_left hD (hDS _) (hDS _), ⟨_, h3.comp (hDr.pairOn r _ _)
          (hDS _).keepsSet (hDS _).keepsSet h2.keeps h2.keeps'
          (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst).set_eq x hb).2 hx)
          (fun x hb hx => (wq_wa_mem (hQ _ _ _ hst).set_eq x hb).1 hx)
          (fun x => (hQ _ _ _ (hst' 1)).label_eq x.1.1) (fun x => (hQ _ _ _ hst).label_eq x.1.1)⟩⟩
      | j + 2 =>
        simp only [show j + 2 ≠ 0 by omega, show j + 2 + 1 ≠ 0 by omega, if_false,
          show j + 2 - 1 = j + 1 by omega, show j + 2 + 1 - 1 = j + 1 + 1 by omega]
        exact hseg (j + 1)

end ReprogrammedCircuit

/-! ### Embedded with the index set of a family -/

section Sigma

variable {ι : Type} [Fintype ι] [DecidableEq ι] {ℓι : ι → Option L} {n : ℕ}

theorem sigmaEmbed_op_eq_zero {F : Fin n → IndexedKrausMap ι} {k : Fin n}
    (p : Σ j, (F j).R) (h : p.1 ≠ k) (a b : ι) : (KrausMap.sigmaEmbed F k).op p a b = 0 := by
  simp [KrausMap.sigmaEmbed, h]

theorem sigmaEmbed_op_mk (F : Fin n → IndexedKrausMap ι) (k : Fin n) (x : (F k).R) :
    (KrausMap.sigmaEmbed F k).op ⟨k, x⟩ = (F k).K.op x := by
  simp [KrausMap.sigmaEmbed]

theorem rowGram_sigmaEmbed (F : Fin n → IndexedKrausMap ι) (k : Fin n) (r : L) (c d : ι) :
    rowGram ℓι r (KrausMap.sigmaEmbed F k) c d = rowGram ℓι r (F k).K c d := by
  unfold rowGram
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp only [sigmaEmbed_op_mk]
  · intro j _ hj
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun a _ => ?_
    rw [sigmaEmbed_op_eq_zero ⟨j, x⟩ hj]
    simp
  · simp

variable {F : Fin n → IndexedKrausMap ι} (G : ∀ j, KrausMap (F j).R ι ι) {k : Fin n}

theorem sigmaEmbed_op_mk' (x : (F k).R) :
    (KrausMap.sigmaEmbed (fun j => (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) k).op ⟨k, x⟩ =
      (G k).op x :=
  sigmaEmbed_op_mk (fun j => (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) k x

variable {G}

theorem PairNone.sigmaEmbed {Sc Sr Sc' Sr' : Set ι}
    (h : PairNone ℓι Sc Sr Sc' Sr' (F k).K (G k)) :
    PairNone ℓι Sc Sr Sc' Sr' (KrausMap.sigmaEmbed F k)
      (KrausMap.sigmaEmbed (fun j => (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) k) where
  keepsSet := fun ⟨j, x⟩ => by
    by_cases hj : j = k
    · subst hj
      rw [sigmaEmbed_op_mk]
      exact h.keepsSet x
    · exact fun a b _ hne => absurd (sigmaEmbed_op_eq_zero ⟨j, x⟩ hj a b) hne
  keepsSet' := fun ⟨j, x⟩ => by
    by_cases hj : j = k
    · subst hj
      rw [sigmaEmbed_op_mk']
      exact h.keepsSet' x
    · exact fun a b _ hne => absurd (sigmaEmbed_op_eq_zero (F := fun j =>
        (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) ⟨j, x⟩ hj a b) hne
  keeps := fun ⟨j, x⟩ => by
    by_cases hj : j = k
    · subst hj
      rw [sigmaEmbed_op_mk]
      exact h.keeps x
    · exact fun _ a b _ _ hne => absurd (sigmaEmbed_op_eq_zero ⟨j, x⟩ hj a b) hne
  keeps' := fun ⟨j, x⟩ => by
    by_cases hj : j = k
    · subst hj
      rw [sigmaEmbed_op_mk']
      exact h.keeps' x
    · exact fun _ a b _ _ hne => absurd (sigmaEmbed_op_eq_zero (F := fun j =>
        (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) ⟨j, x⟩ hj a b) hne
  row_none_eq := fun ⟨j, x⟩ a b ha hb hal hbl => by
    by_cases hj : j = k
    · subst hj
      rw [sigmaEmbed_op_mk, sigmaEmbed_op_mk']
      exact h.row_none_eq x a b ha hb hal hbl
    · rw [sigmaEmbed_op_eq_zero ⟨j, x⟩ hj, sigmaEmbed_op_eq_zero (F := fun j =>
        (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) ⟨j, x⟩ hj]
  gram_eq r c d hc hd hcl hdl := by
    rw [rowGram_sigmaEmbed, rowGram_sigmaEmbed]
    exact h.gram_eq r c d hc hd hcl hdl

theorem PairOn.sigmaEmbed {r : L} {ρs : ∀ j, Equiv.Perm (F j).R} {πr πc : Equiv.Perm ι}
    {Sr Sc : Set ι} (h : PairOn ℓι r (ρs k) πr πc Sr Sc (F k).K (G k)) :
    PairOn ℓι r (Equiv.sigmaCongrRight ρs) πr πc Sr Sc (KrausMap.sigmaEmbed F k)
      (KrausMap.sigmaEmbed (fun j => (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) k) :=
  fun ⟨j, x⟩ a b ha has hb hbs => by
  by_cases hj : j = k
  · subst hj
    rw [Equiv.sigmaCongrRight_apply, sigmaEmbed_op_mk, sigmaEmbed_op_mk']
    exact h x a b ha has hb hbs
  · rw [Equiv.sigmaCongrRight_apply, sigmaEmbed_op_eq_zero ⟨j, x⟩ hj,
      sigmaEmbed_op_eq_zero (F := fun j => (⟨(F j).R, G j⟩ : IndexedKrausMap ι)) ⟨j, ρs j x⟩ hj]

end Sigma

/-! ### The compiled algorithm with other Kraus maps -/

namespace Circuit

variable {W O : Type} [Fintype W] [DecidableEq W]

/-- The core algorithm of `n + 1` Kraus maps `F`, each embedded with the index set of the family. -/
abbrev algOfSegs (n : ℕ) (F : Fin (n + 1) → IndexedKrausMap (QueryReg W 1 X Y))
    (init : MState (QueryReg W 1 X Y)) (out : W → O) : Alg X Y O where
  V := W
  depth := n
  R := Σ k : Fin (n + 1), (F k).R
  init := init
  step := KrausMap.sigmaEmbed F
  out := out

theorem algOfSegs_congr {n n' : ℕ} (h : n = n')
    {F : Fin (n + 1) → IndexedKrausMap (QueryReg W 1 X Y)}
    {F' : Fin (n' + 1) → IndexedKrausMap (QueryReg W 1 X Y)}
    (hF : ∀ k : Fin (n' + 1), F (Fin.cast (by omega) k) = F' k) (init : MState (QueryReg W 1 X Y))
    (out : W → O) : algOfSegs n F init out = algOfSegs n' F' init out := by
  subst h
  have : F = F' := funext fun k => hF k
  rw [this]

/-- **The compiled algorithm of a circuit with the same queries and segments of the first's index
types** is the first's compiled algorithm with the other Kraus maps. -/
theorem toAlg_eq_of_seg (C C' : Circuit (QueryReg W 1 X Y)) (hq : C'.queries = C.queries)
    (G : ∀ k : Fin (C.queries + 1), KrausMap (C.seg k).R (QueryReg W 1 X Y) (QueryReg W 1 X Y))
    (hs : ∀ k : Fin (C.queries + 1), C'.seg k = ⟨(C.seg k).R, G k⟩)
    (init : MState (QueryReg W 1 X Y)) (out : W → O) :
    C'.toAlg init out =
      { C.toAlg init out with step := KrausMap.sigmaEmbed fun k => ⟨(C.seg k).R, G k⟩ } :=
  algOfSegs_congr (F := fun k => C'.seg k) (F' := fun k => ⟨(C.seg k).R, G k⟩) hq
    (fun k => hs k) init out

end Circuit

/-! ### The compiled algorithms of twin circuits -/

namespace ReprogrammedCircuit

variable {r : L} {Q : Set V → Set V → Equiv.Perm V → Prop}

omit [AddGroup Y] in
theorem BTwin.queries_eq {c c' : ReprogrammedCircuit V X Y} {S S' Se Se' : Set V}
    {τ τe : Equiv.Perm V} {b be : Bool} (h : BTwin ℓ r Q c c' S S' τ b Se Se' τe be) :
    c'.queries = c.queries := by
  induction h with
  | nil => rfl
  | same _ _ _ _ _ ih => exact ih
  | diff _ _ _ _ ih => exact ih
  | rquery _ _ ih => simp [queries, ih]

variable {O : Type}

/-- **The compiled algorithms of twin circuits**: the second's is the first's with other Kraus
maps, which, from the states `i` to `i + 1` of the segments, agree with the first's on the rows
with label `none` with the same overlaps and agree on the block `r` along the permutations, the
operators relabelled by `ρs`. -/
theorem BTwin.alg {c c' : ReprogrammedCircuit V X Y} {S S' Se Se' : Set V} {τ τe : Equiv.Perm V}
    {be : Bool} (h : BTwin ℓ r Q c c' S S' τ false Se Se' τe be)
    (hQ : ∀ S S' τ, Q S S' τ → TwinState ℓ r S S' τ) (hst : Q S S' τ)
    (init : MState (ReprogrammedQueryReg V X Y)) (out : V × (X × Y × Bool) → O) :
    ∃ (G : ∀ k : Fin ((toCircuit c).queries + 1), KrausMap ((toCircuit c).seg k).R
        (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y))
      (ρs : ∀ k : Fin ((toCircuit c).queries + 1), Equiv.Perm ((toCircuit c).seg k).R)
      (T T' : ℕ → Set V) (P : ℕ → Equiv.Perm V),
      T 0 = S ∧ T' 0 = S' ∧ P 0 = τ ∧ (∀ j, Q (T j) (T' j) (P j)) ∧
      (∀ j, c.queries < j → T j = Se ∧ T' j = Se' ∧ P j = τe) ∧
      (toCircuit c').toAlg init out = { (toCircuit c).toAlg init out with
        step := KrausMap.sigmaEmbed fun k => ⟨((toCircuit c).seg k).R, G k⟩ } ∧
      ∀ k : Fin ((toCircuit c).queries + 1),
        PairNone (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) {p | p.1.1 ∈ T k}
          {p | p.1.1 ∈ T (k + 1)} {p | p.1.1 ∈ T' k} {p | p.1.1 ∈ T' (k + 1)}
          (((toCircuit c).toAlg init out).step k)
          (KrausMap.sigmaEmbed (fun j => ⟨((toCircuit c).seg j).R, G j⟩) k) ∧
        PairOn (fun p : ReprogrammedQueryReg V X Y => ℓ p.1.1) r (Equiv.sigmaCongrRight ρs)
          (WorkRel.wq (WorkRel.wa (P (k + 1)))) (WorkRel.wq (WorkRel.wa (P k)))
          {p | p.1.1 ∈ T (k + 1)} {p | p.1.1 ∈ T k} (((toCircuit c).toAlg init out).step k)
          (KrausMap.sigmaEmbed (fun j => ⟨((toCircuit c).seg j).R, G j⟩) k) := by
  obtain ⟨T, T', P, hT0, hT0', hP0, hst', hTe, -, hseg⟩ := h.segs hQ hst
  choose G hG using fun k : Fin ((toCircuit c).queries + 1) => hseg k
  choose ρs hρ using fun k : Fin ((toCircuit c).queries + 1) => (hG k).2.2
  refine ⟨G, ρs, T, T', P, hT0, hT0', hP0, hst', hTe, ?_, fun k =>
    ⟨PairNone.sigmaEmbed (hG k).2.1, PairOn.sigmaEmbed (hρ k)⟩⟩
  refine Circuit.toAlg_eq_of_seg _ _ ?_ G (fun k => (hG k).1) init out
  rw [queries_toCircuit, queries_toCircuit, h.queries_eq]

section Bits

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}

theorem prevSeq_expSeq_lift {q : ℕ} {T : ℕ → Set V} {S : Set V} (hT0 : T 0 = S)
    (i : Fin (q + 1)) :
    prevSeq (expSeq fun i : Fin (q + 1) => {v : V × (Bits m × BitStr I J × Bool) | v.1 ∈ T (i + 1)})
      {v | v.1 ∈ S} i = {v | v.1 ∈ T i} := by
  unfold prevSeq expSeq
  split_ifs with h
  · rw [h, hT0]
  · have : min ((i : ℕ) - 1) q + 1 = i := by omega
    simp only [this]

theorem prevSeq_expSeq_perm {q : ℕ} {P : ℕ → Equiv.Perm V} {τ : Equiv.Perm V} (hP0 : P 0 = τ)
    (i : Fin (q + 1)) :
    prevSeq (expSeq fun i : Fin (q + 1) =>
        (WorkRel.wa (X := Bits m) (Y := BitStr I J) (P (i + 1))))
      (WorkRel.wa τ) i = WorkRel.wa (P i) := by
  unfold prevSeq expSeq
  split_ifs with h
  · rw [h, hP0]
  · have : min ((i : ℕ) - 1) q + 1 = i := by omega
    simp only [this]

/-- **The block hypotheses of the compiled algorithms of twin circuits**: the second's compiled
algorithm is the first's with other Kraus maps `K'`, and the two satisfy `Alg.BlockNone` and
`Alg.BlockRel` along the sets `T (i + 1)`, `T' (i + 1)` and the permutations `P (i + 1)` after
segment `i` (the start's before the first), the label read on the work register without the
ancilla. -/
theorem BTwin.alg_block {O : Type} {c c' : ReprogrammedCircuit V (Bits m) (BitStr I J)}
    {S S' Se Se' : Set V} {τ τe : Equiv.Perm V} {be : Bool}
    (h : BTwin ℓ r Q c c' S S' τ false Se Se' τe be)
    (hQ : ∀ S S' τ, Q S S' τ → TwinState ℓ r S S' τ) (hst : Q S S' τ)
    (init : MState (ReprogrammedQueryReg V (Bits m) (BitStr I J)))
    (out : V × (Bits m × BitStr I J × Bool) → O)
    (hinit : ∀ a b, init.mat a b ≠ 0 → a.1.1 ∈ S ∧ b.1.1 ∈ S)
    (hinit' : ∀ a b, init.mat a b ≠ 0 → a.1.1 ∈ S' ∧ b.1.1 ∈ S')
    (hinit_eq : ∀ a b : ReprogrammedQueryReg V (Bits m) (BitStr I J), a.1.1 ∈ S → b.1.1 ∈ S →
      InBlock ℓ r a.1.1 → InBlock ℓ r b.1.1 →
      init.mat (WorkRel.wq (WorkRel.wa τ) a) (WorkRel.wq (WorkRel.wa τ) b) = init.mat a b) :
    ∃ (K' : Fin (((toCircuit c).toAlg init out).depth + 1) →
        KrausMap ((toCircuit c).toAlg init out).R
          (QueryReg ((toCircuit c).toAlg init out).V 1 (Bits m) (BitStr I J))
          (QueryReg ((toCircuit c).toAlg init out).V 1 (Bits m) (BitStr I J)))
      (ρ : Equiv.Perm ((toCircuit c).toAlg init out).R) (T T' : ℕ → Set V)
      (P : ℕ → Equiv.Perm V),
      T 0 = S ∧ T' 0 = S' ∧ P 0 = τ ∧ (∀ j, Q (T j) (T' j) (P j)) ∧
      (∀ j, c.queries < j → T j = Se ∧ T' j = Se' ∧ P j = τe) ∧
      (toCircuit c').toAlg init out = { (toCircuit c).toAlg init out with step := K' } ∧
      ((toCircuit c).toAlg init out).BlockNone K' (fun v => ℓ v.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T' (i + 1)}) {v | v.1 ∈ S}
        {v | v.1 ∈ S'} ∧
      ((toCircuit c).toAlg init out).BlockRel K' (fun v => ℓ v.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T' (i + 1)}) {v | v.1 ∈ S}
        {v | v.1 ∈ S'} (fun i => WorkRel.wa (P (i + 1))) (WorkRel.wa τ) (fun _ => ρ) r := by
  obtain ⟨G, ρs, T, T', P, hT0, hT0', hP0, hst', hTe, heq, hp⟩ := h.alg hQ hst init out
  have hprev := fun i : Fin ((toCircuit c).queries + 1) =>
    prevSeq_expSeq_lift (I := I) (J := J) (m := m) hT0 i
  have hprev' := fun i : Fin ((toCircuit c).queries + 1) =>
    prevSeq_expSeq_lift (I := I) (J := J) (m := m) hT0' i
  have hprevP := fun i : Fin ((toCircuit c).queries + 1) =>
    prevSeq_expSeq_perm (I := I) (J := J) (m := m) hP0 i
  refine ⟨KrausMap.sigmaEmbed fun k => ⟨((toCircuit c).seg k).R, G k⟩,
    Equiv.sigmaCongrRight ρs, T, T', P, hT0, hT0', hP0, hst', hTe, heq, ?_, ?_⟩
  · refine ⟨fun i v hv => (hQ _ _ _ (hst' (i + 1))).none_eq v.1 hv,
      fun v hv => (hQ _ _ _ hst).none_eq v.1 hv,
      fun i k' => ?_, fun i k' => ?_, fun i k' => ?_, fun i k' => ?_,
      fun i k' a b ha hb hal hbl => ?_, fun i r' c d hc hd hcl hdl => ?_, hinit, hinit'⟩
    · rw [hprev]
      exact (hp i).1.keepsSet k'
    · rw [hprev']
      exact (hp i).1.keepsSet' k'
    · rw [hprev]
      exact (hp i).1.keeps k'
    · rw [hprev']
      exact (hp i).1.keeps' k'
    · rw [hprev] at hb
      exact (hp i).1.row_none_eq k' a b ha hb hal hbl
    · rw [hprev] at hc hd
      exact (hp i).1.gram_eq r' c d hc hd hcl hdl
  · refine ⟨fun i v => (hQ _ _ _ (hst' (i + 1))).label_eq v.1, fun v => (hQ _ _ _ hst).label_eq v.1,
      fun i v hv => (hQ _ _ _ (hst' (i + 1))).set_eq v.1 hv,
      fun v hv => (hQ _ _ _ hst).set_eq v.1 hv,
      fun i k' => ?_, fun i k' => ?_, fun i k' => ?_, fun i k' => ?_, fun i => ?_, hinit,
      hinit', hinit_eq⟩
    · rw [hprev]
      exact (hp i).1.keepsSet k'
    · rw [hprev']
      exact (hp i).1.keepsSet' k'
    · rw [hprev]
      exact (hp i).1.keeps k'
    · rw [hprev']
      exact (hp i).1.keeps' k'
    · rw [hprev, hprevP]
      intro k' a b ha hb
      exact (hp i).2 k' a b ha.1 ha.2 hb.1 hb.2

end Bits

end ReprogrammedCircuit

/-! ### The composition of a core algorithm with run-time kinds and a challenger -/

/-- A state of twin circuits with the same sets and the identity permutation. -/
def IdState {V : Type} (S S' : Set V) (τ : Equiv.Perm V) : Prop := S' = S ∧ τ = Equiv.refl V

theorem twinState_of_idState {ℓ : V → Option L} {r : L} {S S' : Set V} {τ : Equiv.Perm V}
    (h : IdState S S' τ) : ReprogrammedCircuit.TwinState ℓ r S S' τ := by
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ => rfl⟩

theorem selfRel_refl {R : Type} [Fintype R] {W : Type} [Fintype W] [DecidableEq W]
    (K : KrausMap R (QueryReg W 1 X Y) (QueryReg W 1 X Y)) :
    SelfRel (Equiv.refl R) (WorkRel.wq (Equiv.refl W)) K := fun _ _ _ => rfl

namespace KindAlg

variable {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (C : Challenger X Y Req Resp) {ℓB : B.W → Option L}

/-- The set of composed registers whose adversary's workspace, request and response are in `G`. -/
abbrev liftSet (G : Set (B.W × Req × Option Resp)) : Set (B.CW C) := {v | v.adv.1 ∈ G}

variable {B C}

/-- **A basis permutation keeping the adversary's workspace, request and response** is a block
isometry keeping every lifted set. -/
theorem blockIso_ofPerm_adv {π : Equiv.Perm (QueryReg (B.CW C) 1 X Y)}
    (h : ∀ q, (π q).1.adv.1 = q.1.adv.1) :
    BlockIso (fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1) (KrausMap.ofPerm π) :=
  BlockIso.ofPerm fun q => by rw [h]

theorem setIso_ofPerm_adv {π : Equiv.Perm (QueryReg (B.CW C) 1 X Y)}
    (h : ∀ q, (π q).1.adv.1 = q.1.adv.1) (G : Set (B.W × Req × Option Resp)) :
    SetIso {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.liftSet C G} (KrausMap.ofPerm π) :=
  SetIso.ofPerm fun q => by
    change (π q).1.adv.1 ∈ G ↔ q.1.adv.1 ∈ G
    rw [h]

theorem copyReq_adv (j : Fin B.slots) (q : QueryReg (B.CW C) 1 X Y) :
    (B.copyReq C j q).1.adv.1 = q.1.adv.1 := by
  change (if B.kind q.1.adv.workspace then _ else q).1.adv.1 = _
  split_ifs <;> rfl

theorem blockIso_measReq (j : Fin B.slots) :
    BlockIso (fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1) (B.measReq C j) :=
  (blockIso_ofPerm_adv (copyReq_adv j)).comp (BlockIso.measureFn _)

theorem setIso_measReq (j : Fin B.slots) (G : Set (B.W × Req × Option Resp)) :
    SetIso {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.liftSet C G} (B.measReq C j) :=
  (setIso_ofPerm_adv (copyReq_adv j) G).comp (SetIso.measureFn _ _)

/-- **Writing the reply** keeps the block isometry, the adversary's workspace being kept. -/
theorem blockIso_writeReply (j : Fin B.slots) :
    BlockIso (fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1)
      (KrausMap.ofPerm (B.writeReply C j)) :=
  BlockIso.ofPerm fun q => by
    change ℓB (if (q.1.chal.logs j).isSome then _ else q).1.adv.1.1 = _
    split_ifs <;> rfl

/-- **Writing the reply keeps a set closed under changes of the response.** -/
theorem setIso_writeReply (j : Fin B.slots) {G : Set (B.W × Req × Option Resp)}
    (hG : ∀ w q a a', (w, q, a) ∈ G → (w, q, a') ∈ G) :
    SetIso {q : QueryReg (B.CW C) 1 X Y | q.1 ∈ B.liftSet C G}
      (KrausMap.ofPerm (B.writeReply C j)) :=
  SetIso.ofPerm fun q => by
    change (if (q.1.chal.logs j).isSome then _ else q).1.adv.1 ∈ G ↔ q.1.adv.1 ∈ G
    split_ifs
    · exact ⟨hG _ _ _ _, hG _ _ _ _⟩
    · exact Iff.rfl

theorem onFst_advKraus (k : StepIdx B.slots B.post) :
    OnFst (B.advSplit C).symm (B.step k) (B.advKraus C k) := fun i y x =>
  KrausMap.tensorId_reindex_op_apply _ _ _ _ _

variable [Nonempty X] [AddGroup Y] {r : L}

theorem twin_chalQueries (j : Fin B.slots) (S : Set (B.W × Req × Option Resp)) (b : Bool) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r IdState (B.chalQueries C j)
      (B.chalQueries C j) (B.liftSet C S) (B.liftSet C S) (Equiv.refl _) b (B.liftSet C S)
      (B.liftSet C S) (Equiv.refl _) (if C.q = 0 then b else false) := by
  have h := ReprogrammedCircuit.BTwin.concat_same (ℓ := fun v : B.CW C => ℓB v.adv.1.1) (r := r)
    (Q := IdState)
    (S := B.liftSet C S) (S' := B.liftSet C S) (τ := Equiv.refl _) ((List.finRange C.q).map fun i =>
      .kraus (KrausMap.ofPerm (B.prepChal C j i))
        (.rquery (fun v => B.chalAss C j i v.chal)
          (.kraus (KrausMap.ofPerm (B.garSwap C j i)) .nil)))
    (fun x hx b' => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact .same (blockIso_ofPerm_adv fun _ => rfl) (setIso_ofPerm_adv (fun _ => rfl) S)
        (setIso_ofPerm_adv (fun _ => rfl) S) ⟨_, (selfRel_refl _).pairOn r _ _⟩
        (.rquery (fun _ => rfl)
          (.same (blockIso_ofPerm_adv fun _ => rfl) (setIso_ofPerm_adv (fun _ => rfl) S)
            (setIso_ofPerm_adv (fun _ => rfl) S) ⟨_, (selfRel_refl _).pairOn r _ _⟩ .nil))) b
  have e : ((List.finRange C.q).map fun i =>
      (ReprogrammedCircuit.kraus (KrausMap.ofPerm (B.prepChal C j i))
        (.rquery (fun v => B.chalAss C j i v.chal) (.kraus (KrausMap.ofPerm (B.garSwap C j i))
          .nil)) : ReprogrammedCircuit (B.CW C) X Y)) = [] ↔ C.q = 0 := by
    simp
  simp only [e] at h
  exact h

theorem twin_advQueries (ass : B.CW C → List (Assignment X Y))
    (S : Set (B.W × Req × Option Resp)) (b : Bool) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r IdState (B.advQueries C ass)
      (B.advQueries C ass) (B.liftSet C S) (B.liftSet C S) (Equiv.refl _) b (B.liftSet C S)
      (B.liftSet C S) (Equiv.refl _) false := by
  have h := ReprogrammedCircuit.BTwin.concat_same (ℓ := fun v : B.CW C => ℓB v.adv.1.1) (r := r)
    (Q := IdState)
    (S := B.liftSet C S) (S' := B.liftSet C S) (τ := Equiv.refl _)
    ((List.finRange B.width).map fun k =>
      .kraus (KrausMap.ofPerm (B.advSwap C k))
        (.rquery ass (.kraus (KrausMap.ofPerm (B.advSwap C k)) .nil)))
    (fun x hx b' => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact .same (blockIso_ofPerm_adv fun _ => rfl) (setIso_ofPerm_adv (fun _ => rfl) S)
        (setIso_ofPerm_adv (fun _ => rfl) S) ⟨_, (selfRel_refl _).pairOn r _ _⟩
        (.rquery (fun _ => rfl)
          (.same (blockIso_ofPerm_adv fun _ => rfl) (setIso_ofPerm_adv (fun _ => rfl) S)
            (setIso_ofPerm_adv (fun _ => rfl) S) ⟨_, (selfRel_refl _).pairOn r _ _⟩ .nil))) b
  have e : ((List.finRange B.width).map fun k =>
      (ReprogrammedCircuit.kraus (KrausMap.ofPerm (B.advSwap C k))
        (.rquery ass (.kraus (KrausMap.ofPerm (B.advSwap C k)) .nil)) :
          ReprogrammedCircuit (B.CW C) X Y)) = [] ↔ False := by
    simp [B.width_pos.ne']
  simp only [e, if_false] at h
  exact h

variable (st'' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
  (DReg B.W B.width X Y Req Resp))

/-- **The adversary's step `k` and the other Kraus map** on the composed registers, from the
hypotheses on the adversary's registers. -/
theorem pair_advKraus {k : StepIdx B.slots B.post} {Gc Gr : Set (B.W × Req × Option Resp)}
    (hn : PairNone (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace) {d | d.1 ∈ Gc}
      {d | d.1 ∈ Gr} {d | d.1 ∈ Gc} {d | d.1 ∈ Gr} (B.step k) (st'' k))
    (ho : PairOn (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace) r (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) {d | d.1 ∈ Gr} {d | d.1 ∈ Gc} (B.step k) (st'' k)) :
    PairNone (fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1)
        {q | q.1 ∈ B.liftSet C Gc} {q | q.1 ∈ B.liftSet C Gr} {q | q.1 ∈ B.liftSet C Gc}
        {q | q.1 ∈ B.liftSet C Gr} (B.advKraus C k)
        (({ B with step := st'' } : KindAlg _ O).advKraus C k) ∧
      PairOn (fun q : QueryReg (B.CW C) 1 X Y => ℓB q.1.adv.1.1) r (Equiv.refl _)
        (WorkRel.wq (Equiv.refl _)) (WorkRel.wq (Equiv.refl _))
        {q | q.1 ∈ B.liftSet C Gr} {q | q.1 ∈ B.liftSet C Gc} (B.advKraus C k)
        (({ B with step := st'' } : KindAlg _ O).advKraus C k) :=
  ⟨(onFst_advKraus k).pairNone
      (onFst_advKraus (B := ({ B with step := st'' } : KindAlg _ O)) k) hn,
    (onFst_advKraus k).pairOn (fun _ => rfl) (fun _ => rfl)
      (onFst_advKraus (B := ({ B with step := st'' } : KindAlg _ O)) k) ho⟩

/-- **The step hypotheses on the adversary's registers**: along the sets `G k` after step `k`
(`G₀` before the first), the adversary's step and the other Kraus map agree on the rows with
label `none` with the same overlaps and agree on the block `r`. -/
def StepPairs (ℓB : B.W → Option L) (r : L) (G : ℕ → Set (B.W × Req × Option Resp))
    (G₀ : Set (B.W × Req × Option Resp)) : Prop :=
  ∀ k : StepIdx B.slots B.post,
    PairNone (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace)
      {d | d.1 ∈ QROM.prevSeq G G₀ k} {d | d.1 ∈ G k} {d | d.1 ∈ QROM.prevSeq G G₀ k}
      {d | d.1 ∈ G k} (B.step k) (st'' k) ∧
    PairOn (fun d : DReg B.W B.width X Y Req Resp => ℓB d.workspace) r (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) {d | d.1 ∈ G k} {d | d.1 ∈ QROM.prevSeq G G₀ k} (B.step k)
      (st'' k)

variable {st''}

theorem prevSeq_succ {α : Sort*} (x : ℕ → α) (x₀ : α) (n : ℕ) :
    QROM.prevSeq x x₀ (n + 1) = x n := by
  simp [QROM.prevSeq]

/-- **The composition with the challenger, with the other Kraus maps**, is twin with the
composition along the lifted sets, for sets closed under changes of the response. -/
theorem twin_fullCircBoth {G : ℕ → Set (B.W × Req × Option Resp)}
    {G₀ : Set (B.W × Req × Option Resp)} (h : B.StepPairs st'' ℓB r G G₀)
    (hG : ∀ n w q a a', (w, q, a) ∈ G n → (w, q, a') ∈ G n) :
    ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r IdState (B.fullCircBoth C)
      (({ B with step := st'' } : KindAlg _ O).fullCircBoth C) (B.liftSet C G₀)
      (B.liftSet C G₀) (Equiv.refl _) false (B.liftSet C (G (B.slots + B.post)))
      (B.liftSet C (G (B.slots + B.post))) (Equiv.refl _) true := by
  have hT : ∀ n, B.liftSet C (QROM.prevSeq G G₀ n) = B.liftSet C (QROM.prevSeq G G₀ n) :=
    fun _ => rfl
  have hslot := ReprogrammedCircuit.BTwin.concat_finRange (ℓ := fun v : B.CW C => ℓB v.adv.1.1)
    (r := r) (Q := IdState) B.slots (fun j => B.slotCircBoth C j)
    (fun j => ({ B with step := st'' } : KindAlg _ O).slotCircBoth C j)
    (fun n => B.liftSet C (QROM.prevSeq G G₀ n)) (fun n => B.liftSet C (QROM.prevSeq G G₀ n))
    (fun _ => Equiv.refl _) fun j => by
      obtain ⟨hn, ho⟩ := pair_advKraus (C := C) st'' (h (slotStep j)).1 (h (slotStep j)).2
      rw [prevSeq_succ]
      exact .diff hn ⟨_, ho⟩ ⟨rfl, rfl⟩ (.same (blockIso_measReq j) (setIso_measReq j _)
        (setIso_measReq j _) ⟨_, (selfRel_refl _).pairOn r _ _⟩ ((twin_chalQueries j _ true).append
          (.same (blockIso_writeReply j) (setIso_writeReply j (hG j)) (setIso_writeReply j (hG j))
            ⟨_, (selfRel_refl _).pairOn r _ _⟩ (twin_advQueries _ _ _))))
  have hpost := ReprogrammedCircuit.BTwin.concat_finRange (ℓ := fun v : B.CW C => ℓB v.adv.1.1)
    (r := r) (Q := IdState) B.post (fun b => B.postCirc C b)
    (fun b => ({ B with step := st'' } : KindAlg _ O).postCirc C b)
    (fun n => B.liftSet C (QROM.prevSeq G G₀ (B.slots + n)))
    (fun n => B.liftSet C (QROM.prevSeq G G₀ (B.slots + n))) (fun _ => Equiv.refl _) fun b => by
      obtain ⟨hn, ho⟩ := pair_advKraus (C := C) st'' (h (postStep b)).1 (h (postStep b)).2
      rw [show B.slots + (b + 1) = (B.slots + b) + 1 by omega, prevSeq_succ]
      exact .diff hn ⟨_, ho⟩ ⟨rfl, rfl⟩ (twin_advQueries _ _ _)
  obtain ⟨hn, ho⟩ := pair_advKraus (C := C) st'' (h lastStep).1 (h lastStep).2
  have hlast : ReprogrammedCircuit.BTwin (fun v : B.CW C => ℓB v.adv.1.1) r IdState
      (.kraus (B.advKraus C lastStep) .nil)
      (.kraus (({ B with step := st'' } : KindAlg _ O).advKraus C lastStep) .nil)
      (B.liftSet C (QROM.prevSeq G G₀ (B.slots + B.post)))
      (B.liftSet C (QROM.prevSeq G G₀ (B.slots + B.post))) (Equiv.refl _) false
      (B.liftSet C (G (B.slots + B.post))) (B.liftSet C (G (B.slots + B.post))) (Equiv.refl _)
      true :=
    .diff hn ⟨_, ho⟩ ⟨rfl, rfl⟩ .nil
  have h0 : QROM.prevSeq G G₀ 0 = G₀ := rfl
  rw [h0] at hslot
  simp only [Nat.add_zero] at hpost
  exact (hslot.append hpost).append hlast

variable [Nonempty Y] in
/-- **The initial state of the composition is supported on the lifted set** of the adversary's
initial support. -/
theorem initSys_supp {G₀ : Set (B.W × Req × Option Resp)}
    (hinit : ∀ a b, B.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀)
    (a b : ReprogrammedQueryReg (B.CW C) X Y)
    (h : (MState.withAnc KindAlg.x₀ (B.initSys C)).mat a b ≠ 0) :
    a.1.1 ∈ B.liftSet C G₀ ∧ b.1.1 ∈ B.liftSet C G₀ := by
  change (B.initSys C).mat (a.1.1, a.2) (b.1.1, b.2) * _ ≠ 0 at h
  have h1 := left_ne_zero_of_mul h
  simp only [KindAlg.initSys, MState.mix, Matrix.sum_apply] at h1
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  rw [Matrix.smul_apply] at hω
  have h2 := right_ne_zero_of_mul hω
  simp only [MState.reindex, MState.tensorKet_mat, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply] at h2
  exact hinit _ _ (left_ne_zero_of_mul h2)

end KindAlg

section ComposeBits

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksB : KindShape (Bits m) (BitStr I J) Req Resp} {B : KindAlg ksB O} {C : Challenger (Bits m) (BitStr I J) Req Resp}
  {ℓB : B.W → Option L} {r : L}
  {st'' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width (Bits m) (BitStr I J) Req Resp)
    (DReg B.W B.width (Bits m) (BitStr I J) Req Resp)}

/-- **The block hypotheses of the composition with a challenger**, at the identity permutations:
from step hypotheses on the adversary's registers along sets `G k` closed under changes of the
response, with the initial state supported on `G₀`, the composition with the other Kraus maps is
the composition with other Kraus maps `K'`, and the two satisfy `Alg.BlockNone` and `Alg.BlockRel`
along sets `T (i + 1)` after segment `i` with `T 0` the lifted `G₀`, the label read on the
adversary's workspace. -/
theorem KindAlg.composeBothOut_block {G : ℕ → Set (B.W × Req × Option Resp)}
    {G₀ : Set (B.W × Req × Option Resp)} (h : B.StepPairs st'' ℓB r G G₀)
    (hG : ∀ n w q a a', (w, q, a) ∈ G n → (w, q, a') ∈ G n)
    (hinit : ∀ a b, B.init.mat a b ≠ 0 → a.1 ∈ G₀ ∧ b.1 ∈ G₀) {O' : Type}
    (f : B.CW C → O') :
    ∃ (K' : Fin ((B.composeBothOut C f).depth + 1) → KrausMap (B.composeBothOut C f).R
        (QueryReg (B.composeBothOut C f).V 1 (Bits m) (BitStr I J))
        (QueryReg (B.composeBothOut C f).V 1 (Bits m) (BitStr I J)))
      (ρ : Equiv.Perm (B.composeBothOut C f).R) (T : ℕ → Set (B.CW C)),
      T 0 = B.liftSet C G₀ ∧
      ({ B with step := st'' } : KindAlg _ O).composeBothOut C f =
        { B.composeBothOut C f with step := K' } ∧
      (B.composeBothOut C f).BlockNone K' (fun v => ℓB v.1.adv.1.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T (i + 1)})
        {v | v.1 ∈ B.liftSet C G₀} {v | v.1 ∈ B.liftSet C G₀} ∧
      (B.composeBothOut C f).BlockRel K' (fun v => ℓB v.1.adv.1.1)
        (fun i => {v | v.1 ∈ T (i + 1)}) (fun i => {v | v.1 ∈ T (i + 1)})
        {v | v.1 ∈ B.liftSet C G₀} {v | v.1 ∈ B.liftSet C G₀}
        (fun _ => WorkRel.wa (Equiv.refl _)) (WorkRel.wa (Equiv.refl _)) (fun _ => ρ) r := by
  obtain ⟨K', ρ, T, T', P, hT0, -, -, hQ, -, heq, hn, hr⟩ :=
    (KindAlg.twin_fullCircBoth (C := C) h hG).alg_block (fun _ _ _ h => twinState_of_idState h)
      ⟨rfl, rfl⟩ (MState.withAnc KindAlg.x₀ (B.initSys C)) (fun v => f v.1)
      (KindAlg.initSys_supp hinit) (KindAlg.initSys_supp hinit) (fun _ _ _ _ _ _ => rfl)
  have hT' : T' = T := funext fun j => (hQ j).1
  have hP : P = fun _ => Equiv.refl _ := funext fun j => (hQ j).2
  rw [hT'] at hn hr
  rw [hP] at hr
  exact ⟨K', ρ, T, hT0, heq, hn, hr⟩

end ComposeBits


/-! ### The step hypotheses from the block structures -/

namespace AdaptiveIAlg

variable {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O}
  {st' : StepIdx A.slots A.post → KrausMap A.R (DReg A.W A.width X Y Req Resp)
    (DReg A.W A.width X Y Req Resp)}
  {ℓ : A.W → Option L} {G : ℕ → Set (A.W × Req × Option Resp)}
  {G₀ : Set (A.W × Req × Option Resp)} {r : L}

theorem prevSeq_const {α : Sort*} (a : α) (n : ℕ) : prevSeq (fun _ => a) a n = a := by
  unfold prevSeq
  split_ifs <;> rfl

/-- **The step hypotheses at the identity permutations**: `BlockRel` along the identity and
`BlockNone`, with the same sets for the two families, give, at every step, the pairs on the
`none` block and on the block `r`. -/
theorem pairs_of_block
    (h : A.BlockRel st' ℓ G G G₀ G₀ (fun _ => Equiv.refl _) (Equiv.refl _) r)
    (h' : A.BlockNone st' ℓ G G G₀ G₀) (k : StepIdx A.slots A.post) :
    PairNone (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace)
        {d | d.1 ∈ prevSeq G G₀ k} {d | d.1 ∈ G k} {d | d.1 ∈ prevSeq G G₀ k} {d | d.1 ∈ G k}
        (A.step k) (st' k) ∧
      PairOn (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace) r (Equiv.refl _)
        (Equiv.refl _) (Equiv.refl _) {d | d.1 ∈ G k} {d | d.1 ∈ prevSeq G G₀ k} (A.step k)
        (st' k) := by
  refine ⟨⟨h'.keepsSet k, h'.keepsSet' k, h'.keeps k, h'.keeps' k, h'.row_none_eq k,
    fun r' c d hc hd hcl hdl => h'.gram_eq k r' c d hc hd hcl hdl⟩, fun i a b ha has hb hbs => ?_⟩
  have := h.hop k i a b ⟨ha, has⟩ ⟨hb, hbs⟩
  rwa [prevSeq_const] at this

/-- **The step hypotheses along permutations**: `BlockRel` along `σ` and `BlockNone` give, at
every step, the pairs on the `none` block and on the block `r` along the permutations. -/
theorem pairs_of_block_perm {G' : ℕ → Set (A.W × Req × Option Resp)}
    {G₀' : Set (A.W × Req × Option Resp)} {σ : ℕ → Equiv.Perm (A.W × Req × Option Resp)}
    {σ₀ : Equiv.Perm (A.W × Req × Option Resp)} (h : A.BlockRel st' ℓ G G' G₀ G₀' σ σ₀ r)
    (h' : A.BlockNone st' ℓ G G' G₀ G₀') (k : StepIdx A.slots A.post) :
    PairNone (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace)
        {d | d.1 ∈ prevSeq G G₀ k} {d | d.1 ∈ G k} {d | d.1 ∈ prevSeq G' G₀' k}
        {d | d.1 ∈ G' k} (A.step k) (st' k) ∧
      PairOn (fun d : DReg A.W A.width X Y Req Resp => ℓ d.workspace) r (Equiv.refl _)
        (tripPerm (σ k)) (tripPerm (prevSeq σ σ₀ k)) {d | d.1 ∈ G k}
        {d | d.1 ∈ prevSeq G G₀ k} (A.step k) (st' k) :=
  ⟨⟨h'.keepsSet k, h'.keepsSet' k, h'.keeps k, h'.keeps' k, h'.row_none_eq k,
    fun r' c d hc hd hcl hdl => h'.gram_eq k r' c d hc hd hcl hdl⟩,
    fun i a b ha has hb hbs => h.hop k i a b ⟨ha, has⟩ ⟨hb, hbs⟩⟩

end AdaptiveIAlg

end GordieHowe.Quantum
