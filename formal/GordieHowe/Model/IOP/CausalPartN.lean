-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.CausalSound
public import GordieHowe.Model.IOP.CausalComplete

@[expose] public section

/-!
# The parts of a composite of many subterms

Composite transcripts of `nodeN k m c` from those of its subterms and back (`FullTr.joinN`,
`FullTr.partN`, `partN_joinN`), and the run of `m` causal provers composed by `k` part by part
(`CausalProver.run_nodeN_partN`).
-/

namespace GordieHowe.IOP

open SPTerm

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

/-- **The composite transcript of `nodeN k m c`** from those of its subterms. -/
def FullTr.joinN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (∀ i, FullTr P (c i)) →
    FullTr P (SPTerm.nodeN k m c)
  | 0, _, _ => fun p => nomatch p
  | m + 1, _, f => FullTr.join (f 0) (FullTr.joinN k m fun i => f i.succ)

/-- **The parts of a joined composite transcript** are the parts it was joined from. -/
theorem FullTr.partN_joinN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (f : ∀ i, FullTr P (c i)) → (i : Fin m) → (FullTr.joinN k m f).partN k m i = f i
  | 0, _, _, i => i.elim0
  | m + 1, c, f, i => by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact FullTr.partN_joinN k m (c := fun i => c i.succ) (fun i => f i.succ) i

/-- **The run of `m` causal provers composed by `k`**, part by part: each prover's run on its part
of the challenges. -/
theorem CausalProver.run_nodeN_partN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {Stmt : Type} → (prv : ∀ i, CausalProver P (c i) Stmt) → (x : Stmt) →
    (ch : Chs P (SPTerm.nodeN k m c)) → (i : Fin m) →
    ((CausalProver.nodeN k m prv).run x ch).partN k m i = (prv i).run x (ch.partN k m i)
  | 0, _, _, _, _, _, i => i.elim0
  | m + 1, c, _, prv, x, ch, i => by
    have h := CausalProver.run_par (k := k) (prv 0) (CausalProver.nodeN k m fun i => prv i.succ)
      x ch
    induction i using Fin.cases with
    | zero =>
      change ((CausalProver.par (k := k) (prv 0) (CausalProver.nodeN k m fun i => prv i.succ)).run
        x ch).left = _
      rw [h]
      rfl
    | succ i =>
      change (((CausalProver.par (k := k) (prv 0)
        (CausalProver.nodeN k m fun i => prv i.succ)).run x ch).right).partN k m i = _
      rw [h]
      exact CausalProver.run_nodeN_partN k m (c := fun i => c i.succ) (fun i => prv i.succ) x
        ch.right i

/-- **A composite transcript of a node** is determined by its two parts. -/
theorem FullTr.ext_node {k : Comp} {a b : SPTerm ι} {f g : FullTr P (node k a b)}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  funext p
  cases p with
  | left p => exact congrFun hl p
  | right p => exact congrFun hr p

/-- **A composite transcript of a one-component term** is its leaf's transcript. -/
theorem FullTr.ext_leaf {j : ι} {f g : FullTr P (leaf j)} (h : f (.here j) = g (.here j)) :
    f = g := by
  funext p
  cases p
  exact h

/-- **A composite transcript of `nodeN k m c`** is determined by its parts. -/
theorem FullTr.ext_partN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {f g : FullTr P (SPTerm.nodeN k m c)} → (∀ i, f.partN k m i = g.partN k m i) → f = g
  | 0, _, _, _, _ => funext fun p => nomatch p
  | m + 1, c, f, g, h => FullTr.ext_node (h 0)
      (FullTr.ext_partN k m (c := fun i => c i.succ) fun i => h i.succ)

/-- **`verifierN` accepts when every composite's verifier accepts its part.** -/
theorem verifierN_of_forall {Stmt : Type} (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {V : ∀ i, Stmt → FullTr P (c i) → Bool} → {x : Stmt} → (f : FullTr P (SPTerm.nodeN k m c)) →
    (∀ i, V i x (f.partN k m i) = true) → verifierN k m V x f = true
  | 0, _, _, _, _, _ => rfl
  | m + 1, c, V, x, f, h => by
    rw [verifierN, Bool.and_eq_true]
    exact ⟨h 0, verifierN_of_forall k m (c := fun i => c i.succ) f.right fun i => h i.succ⟩

open Classical in
/-- **An event on one challenge of a composite** has, over uniform composite challenges, the
probability it has over that challenge. -/
theorem Chs.probUniform_coord_le [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), DecidableEq ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {t : SPTerm ι} (c : ChIdx P t)
    (bad : c.Challenge → Prop) {δ : NNReal} (h : Pr[v ← c.Challenge : bad v] ≤ δ) :
    Pr[ch ← Chs P t : bad (ch c)] ≤ δ := by
  rw [← card_le_iff_probUniform_le] at h ⊢
  exact card_le_of_card_update_le c fun f => by simpa [Function.update_self] using h

open Classical in
/-- **An event bounded at one challenge of a composite whatever the other challenges** has, over
uniform composite challenges, at most that bound: for every composite challenge vector `f`, the
event at `f` with challenge `c` replaced has probability at most `δ` over that challenge. -/
theorem Chs.probUniform_le_of_update [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), DecidableEq ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {t : SPTerm ι} (c : ChIdx P t)
    (bad : Chs P t → Prop) {δ : NNReal}
    (h : ∀ f : Chs P t, Pr[v ← c.Challenge : bad (Function.update f c v)] ≤ δ) :
    Pr[ch ← Chs P t : bad ch] ≤ δ := by
  rw [← card_le_iff_probUniform_le]
  refine card_le_of_card_update_le c fun f => ?_
  have hf := (card_le_iff_probUniform_le _ _ _).mpr (h f)
  simpa using hf

open Classical in
/-- **An event bounded at one coordinate of a uniform function whatever the other coordinates** has,
over uniform functions, at most that bound: for every function `f`, the event at `f` with
coordinate `i` replaced has probability at most `δ` over that coordinate. -/
theorem probUniform_pi_le_of_update {κ : Type} [Fintype κ] [DecidableEq κ] {β : κ → Type}
    [∀ j, Fintype (β j)] [∀ j, Nonempty (β j)] (i : κ) (bad : (∀ j, β j) → Prop) {δ : NNReal}
    (h : ∀ f : ∀ j, β j, Pr[v ← β i : bad (Function.update f i v)] ≤ δ) :
    Pr[f ← (∀ j, β j) : bad f] ≤ δ := by
  rw [← card_le_iff_probUniform_le]
  refine card_le_of_card_update_le i fun f => ?_
  have hf := (card_le_iff_probUniform_le _ _ _).mpr (h f)
  simpa using hf

end GordieHowe.IOP
