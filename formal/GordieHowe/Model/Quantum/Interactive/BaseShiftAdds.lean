-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShiftCirc

@[expose] public section

/-!
# Lists of additions after the adversary's Kraus maps, carried through the composition

A list of additions after each Kraus map of a kind algorithm (`KindAlg.AddsAt`, an instance of
`AddsOn`): after Kraus map
`k`, addition `i` adds `ω` of its point to a part `Lw k i` of the workspace, on the branches
`onw k i`; its point `xr k i w u` is read from the workspace `w` and, if `readsAt k i = some i'`,
from pair `i'`'s input (`u i'`), or from the workspace alone if `readsAt k i = none`. The list is
sorted by its drop point (`optIdx (readsAt k i)`, pair `0` for the workspace readers): the
additions are dropped after the query of their pair, in list order.

On the composed registers (`AddsAt.liftC`), each addition reads its pair's input where the pair
sits (`XPos`); the additions still pending after the drops at pairs below `c` (`AddsAt.carry`)
are carried across the gates, and those dropped at pair `c` are `AddsAt.block`.

- `optIdx`, `dregLens`, `AddsOn`, `AddsOn.toStepAdds`, `AddsOn.Off`, `KindShape.AddsAt`, `KindAlg.AddsAt`.
- `wsOf`, `setWs`, `readP`, `KindShape.AddsAt.fC`, `KindShape.AddsAt.liftC`,
  `KindShape.AddsAt.liftC_conj`, `KindShape.AddsAt.liftQC`, `KindShape.AddsAt.liftC_adv`.
- `seqPerm_conj`, `seqPerm_mask_split`, `KindShape.AddsAt.carry`, `KindShape.AddsAt.block`,
  `KindShape.AddsAt.carry_succ`, `KindShape.AddsAt.carry_width`.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

/-! ### Permutations in sequence: conjugation and masks -/

section SeqMask

variable {Z : Type*}

/-- **A permutation carrying each of a list to another carries them in sequence.** -/
theorem seqPerm_conj (π : Equiv.Perm Z) :
    ∀ (n : ℕ) (f f' : Fin n → Equiv.Perm Z), (∀ i z, π (f i z) = f' i (π z)) →
      ∀ z, π (seqPerm n f z) = seqPerm n f' (π z)
  | 0, _, _, _, _ => rfl
  | n + 1, f, f', h, z => by
    change π (f (Fin.last n) (seqPerm n (fun i => f i.castSucc) z)) =
      f' (Fin.last n) (seqPerm n (fun i => f' i.castSucc) (π z))
    rw [h, seqPerm_conj π n _ _ (fun i => h i.castSucc)]

/-- **A masked list in sequence splits into two masks** when every index of the first precedes
every index of the second: the first mask's part is applied first. -/
theorem seqPerm_mask_split :
    ∀ (n : ℕ) (a : Fin n → Equiv.Perm Z) (p q : Fin n → Bool),
      (∀ i, ¬ (p i = true ∧ q i = true)) → (∀ i j, p i = true → q j = true → i < j) →
      seqPerm n (fun i => if p i || q i then a i else 1) =
        seqPerm n (fun i => if q i then a i else 1) * seqPerm n (fun i => if p i then a i else 1)
  | 0, _, _, _, _, _ => rfl
  | n + 1, a, p, q, hd, ho => by
    have ih := seqPerm_mask_split n (fun i => a i.castSucc) (fun i => p i.castSucc)
      (fun i => q i.castSucc) (fun i => hd i.castSucc)
      (fun i j hi hj => Fin.castSucc_lt_castSucc_iff.1 (ho _ _ hi hj))
    change (if p (Fin.last n) || q (Fin.last n) then a (Fin.last n) else 1) *
        seqPerm n (fun i => if p i.castSucc || q i.castSucc then a i.castSucc else 1) =
      ((if q (Fin.last n) then a (Fin.last n) else 1) *
        seqPerm n (fun i => if q i.castSucc then a i.castSucc else 1)) *
      ((if p (Fin.last n) then a (Fin.last n) else 1) *
        seqPerm n (fun i => if p i.castSucc then a i.castSucc else 1))
    rw [ih]
    by_cases hq : q (Fin.last n) = true
    · have hp : p (Fin.last n) = false := by
        cases h : p (Fin.last n)
        · rfl
        · exact absurd ⟨h, hq⟩ (hd _)
      simp only [hq, hp, Bool.or_true, Bool.false_eq_true, ↓reduceIte, one_mul, mul_assoc]
    · have hq' : q (Fin.last n) = false := by simpa using hq
      by_cases hp : p (Fin.last n) = true
      · have hnq : ∀ i : Fin n, q i.castSucc = false := fun i => by
          cases h : q i.castSucc
          · rfl
          · exact absurd (ho _ _ hp h) (not_lt.2 (Fin.le_last _))
        have h1 : seqPerm n (fun i => if q i.castSucc then a i.castSucc else 1) = 1 :=
          seqPerm_one _ _ fun i => by simp [hnq i]
        simp only [hp, hq', Bool.or_false, ↓reduceIte, Bool.false_eq_true, h1, one_mul]
      · have hp' : p (Fin.last n) = false := by simpa using hp
        simp only [hp', hq', Bool.or_false, Bool.false_eq_true, ↓reduceIte, one_mul]

/-- Permutations that keep a set keep it in sequence. -/
theorem seqPerm_mem (S : Set Z) :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm Z), (∀ i z, z ∈ S → f i z ∈ S) →
      ∀ z ∈ S, seqPerm n f z ∈ S
  | 0, _, _, _, hz => hz
  | n + 1, _, h, z, hz => h _ _ (seqPerm_mem S n _ (fun _ => h _) z hz)

/-- **`seqPerm_conj` on a set** that the permutations keep. -/
theorem seqPerm_conj_on (π : Equiv.Perm Z) (S : Set Z) :
    ∀ (n : ℕ) (f f' : Fin n → Equiv.Perm Z), (∀ i z, z ∈ S → f i z ∈ S) →
      (∀ i z, z ∈ S → π (f i z) = f' i (π z)) →
      ∀ z ∈ S, π (seqPerm n f z) = seqPerm n f' (π z)
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, f, f', hS, h, z, hz => by
    change π (f (Fin.last n) (seqPerm n (fun i => f i.castSucc) z)) =
      f' (Fin.last n) (seqPerm n (fun i => f' i.castSucc) (π z))
    rw [h _ _ (seqPerm_mem S n _ (fun i => hS _) z hz),
      seqPerm_conj_on π S n _ _ (fun i => hS _) (fun i => h _) z hz]

end SeqMask

/-! ### The lists of additions -/

/-- The index of an optional pair, `0` for none. -/
def optIdx {n : ℕ} : Option (Fin n) → ℕ
  | none => 0
  | some i => i

/-- **A part of the workspace, on the adversary's registers.** -/
def dregLens {W V : Type*} (L : RegLens W V) (n : ℕ) (X Y Req Resp : Type*) :
    RegLens (DReg W n X Y Req Resp) V where
  get d := L.get d.1.1
  set d v := ((L.set d.1.1 v, d.1.2), d.2)
  get_set _ _ := by simp
  set_get _ := by simp
  set_set _ _ _ := by simp

/-- **A sorted list of additions after the steps of an algorithm with workspace `W`, `width` query
pairs, steps `K` and kind `kind`**: after step `k`, `nb k` additions; addition `i` writes the part
`Lw k i` of the workspace on the branches `onw k i`, at the point `xr k i w u` read from the
workspace `w` and the pairs' inputs `u`, of which it reads only pair `i'`'s if
`readsAt k i = some i'` and none if `readsAt k i = none` (`xr_reads`). Neither the branches, the
point nor the kind read the part. The list is sorted by the drop point `optIdx (readsAt k i)`, and
each addition is dropped after the query of its pair (the workspace readers after pair `0`'s):
`sorted` makes the drop order the list order, without which an addition could drop before an
earlier one whose part it reads. -/
structure AddsOn (W : Type) (width : ℕ) (K : Type) (kind : W → Bool) (X Y₁ : Type) where
  /-- The number of additions after step `k`. -/
  nb : K → ℕ
  /-- The part of addition `i` after step `k`. -/
  Lw : ∀ k, Fin (nb k) → RegLens W Y₁
  /-- The branches of addition `i`. -/
  onw : ∀ k, Fin (nb k) → W → Bool
  /-- The pair whose input addition `i` reads, if any. -/
  readsAt : ∀ k, Fin (nb k) → Option (Fin width)
  /-- The point of addition `i`, from the workspace and the pairs' inputs. -/
  xr : ∀ k, Fin (nb k) → W → (Fin width → X) → X
  onw_set : ∀ k i, (Lw k i).Indep (onw k i)
  xr_set : ∀ k i u, (Lw k i).Indep fun w => xr k i w u
  xr_reads : ∀ k i w (u u' : Fin width → X),
    (∀ i', readsAt k i = some i' → u i' = u' i') → xr k i w u = xr k i w u'
  kind_set : ∀ k i, (Lw k i).Indep kind
  sorted : ∀ k (i j : Fin (nb k)), i ≤ j → optIdx (readsAt k i) ≤ optIdx (readsAt k j)

/-- **The additions on the registers with the pairs**, the point read from the pairs' inputs. -/
def AddsOn.toStepAdds {W : Type} {width : ℕ} {K : Type} {kind : W → Bool} {X Y₁ : Type}
    [AddGroup Y₁] {Y Req Resp : Type} (P : AddsOn W width K kind X Y₁) :
    StepAdds (DReg W width X Y Req Resp) K X Y₁ where
  nb := P.nb
  L k i := dregLens (P.Lw k i) width X Y Req Resp
  on k i d := P.onw k i d.1.1
  x k i d := P.xr k i d.1.1 fun i' => (d.2 i').1
  on_set k i d v := P.onw_set k i d.1.1 v
  x_set k i d v := P.xr_set k i _ d.1.1 v

/-- **No addition after step `k`** on any branch. -/
def AddsOn.Off {W : Type} {width : ℕ} {K : Type} {kind : W → Bool} {X Y₁ : Type}
    (P : AddsOn W width K kind X Y₁) (k : K) : Prop :=
  ∀ i w, P.onw k i w = false

/-- **A sorted list of additions after the Kraus maps of a shape at a kind** (`AddsOn` at the
shape's workspace, pairs and Kraus maps). -/
abbrev KindShape.AddsAt {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    (ksT : KindShape X Y Req Resp) (kind : ksT.W → Bool) (Y₁ : Type) : Type :=
  AddsOn ksT.W ksT.width (StepIdx ksT.slots ksT.post) kind X Y₁

/-- **A sorted list of additions after the Kraus maps of a kind algorithm**: those of its shape at
its kind (`KindShape.AddsAt`). -/
abbrev KindAlg.AddsAt {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
    {ksT : KindShape X Y Req Resp} (T : KindAlg ksT O) (Y₁ : Type) : Type :=
  ksT.AddsAt T.kind Y₁

section Data

variable {X Y Y₁ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y₁]
  {ksT : KindShape X Y Req Resp} {T : KindAlg ksT O} {kind : ksT.W → Bool}

omit [AddGroup Y₁] in
theorem KindShape.AddsAt.optIdx_lt (P : ksT.AddsAt kind Y₁) (k : StepIdx ksT.slots ksT.post)
    (i : Fin (P.nb k)) : optIdx (P.readsAt k i) < ksT.width := by
  rcases h : P.readsAt k i with _ | i'
  · exact ksT.width_pos
  · exact i'.isLt

end Data

/-! ### The additions on the composed registers -/

section Composed

variable {X Y Y₁ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y₁]
  {ksT : KindShape X Y Req Resp} {T : KindAlg ksT O} {kind : ksT.W → Bool} {C : Challenger X Y Req Resp}

/-- The workspace on the composed registers. -/
abbrev wsOf (p : ReprogrammedQueryReg (ksT.CW C) X Y) : ksT.W := p.1.1.adv.1.1

/-- The composed registers with the workspace replaced. -/
def setWs (p : ReprogrammedQueryReg (ksT.CW C) X Y) (w : ksT.W) :
    ReprogrammedQueryReg (ksT.CW C) X Y :=
  ((⟨((w, p.1.1.adv.1.2), p.1.1.adv.2), p.1.1.chal⟩, p.1.2), p.2)

@[simp] theorem wsOf_setWs (p : ReprogrammedQueryReg (ksT.CW C) X Y) (w : ksT.W) :
    wsOf (setWs p w) = w :=
  rfl

@[simp] theorem setWs_setWs (p : ReprogrammedQueryReg (ksT.CW C) X Y) (w w' : ksT.W) :
    setWs (setWs p w) w' = setWs p w' :=
  rfl

@[simp] theorem setWs_wsOf (p : ReprogrammedQueryReg (ksT.CW C) X Y) : setWs p (wsOf p) = p :=
  rfl

/-- The input of pair `i'` read at the position `pos i'`. -/
def readP (C : Challenger X Y Req Resp) (pos : Fin ksT.width → XPos) (i' : Fin ksT.width)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) : X :=
  (pos i').read C i' (p.2 0).1 p.1

@[simp] theorem readP_setWs (pos : Fin ksT.width → XPos) (i' : Fin ksT.width)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) (w : ksT.W) :
    readP C pos i' (setWs p w) = readP C pos i' p := by
  unfold readP setWs
  cases pos i' <;> rfl

variable (P : ksT.AddsAt kind Y₁) (ω : X → Y₁)

/-- The value added by addition `i` after Kraus map `k` on the composed registers, its pairs'
inputs read at `pos`. -/
def KindShape.AddsAt.fC (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k)) (pos : Fin ksT.width → XPos)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) : Y₁ :=
  if P.onw k i (wsOf p) then ω (P.xr k i (wsOf p) fun i' => readP C pos i' p) else 0

theorem KindShape.AddsAt.fC_setWs (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    (pos : Fin ksT.width → XPos) (p : ReprogrammedQueryReg (ksT.CW C) X Y) (v : Y₁) :
    P.fC ω k i pos (setWs p ((P.Lw k i).set (wsOf p) v)) = P.fC ω k i pos p := by
  unfold KindShape.AddsAt.fC
  simp only [wsOf_setWs, readP_setWs, P.onw_set k i _ v, P.xr_set k i _ _ v]

/-- **Addition `i` after Kraus map `k` on the composed work register with the ancilla**, at the
query input `x`, its pairs' inputs read at `pos`. -/
def KindShape.AddsAt.liftV (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    (pos : Fin ksT.width → XPos) (x : X) : Equiv.Perm (ksT.CW C × (X × Y × Bool)) where
  toFun v := (setWs (v, fun _ => (x, (v.2.2.1)))
    ((P.Lw k i).set v.1.adv.1.1 ((P.Lw k i).get v.1.adv.1.1 +
      P.fC ω k i pos (v, fun _ => (x, v.2.2.1))))).1
  invFun v := (setWs (v, fun _ => (x, (v.2.2.1)))
    ((P.Lw k i).set v.1.adv.1.1 ((P.Lw k i).get v.1.adv.1.1 -
      P.fC ω k i pos (v, fun _ => (x, v.2.2.1))))).1
  left_inv v := by
    have h := P.fC_setWs ω k i pos (v, fun _ => (x, v.2.2.1))
      ((P.Lw k i).get v.1.adv.1.1 + P.fC ω k i pos (v, fun _ => (x, v.2.2.1)))
    simp only [setWs] at h ⊢
    rw [h]
    simp only [RegLens.get_set, RegLens.set_set, add_sub_cancel_right, RegLens.set_get]
  right_inv v := by
    have h := P.fC_setWs ω k i pos (v, fun _ => (x, v.2.2.1))
      ((P.Lw k i).get v.1.adv.1.1 - P.fC ω k i pos (v, fun _ => (x, v.2.2.1)))
    simp only [setWs] at h ⊢
    rw [h]
    simp only [RegLens.get_set, RegLens.set_set, sub_add_cancel, RegLens.set_get]

/-- **Addition `i` after Kraus map `k` on the composed registers**, its pairs' inputs read at
`pos`. -/
def KindShape.AddsAt.liftC (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    (pos : Fin ksT.width → XPos) : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y) where
  toFun p := (P.liftV ω k i pos (p.2 0).1 p.1, p.2)
  invFun p := ((P.liftV ω k i pos (p.2 0).1).symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem KindShape.AddsAt.queryPairFix_liftC (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    (pos : Fin ksT.width → XPos) : QueryPairFix (P.liftC (C := C) ω k i pos) :=
  ⟨fun x => P.liftV ω k i pos x, fun _ => rfl⟩

theorem KindShape.AddsAt.liftC_apply (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    (pos : Fin ksT.width → XPos) (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    P.liftC ω k i pos p =
      setWs p ((P.Lw k i).set (wsOf p) ((P.Lw k i).get (wsOf p) + P.fC ω k i pos p)) :=
  rfl

/-- **A permutation of the composed registers carries addition `i` read at `pos` to it read at
`pos'`** when it keeps the workspace (`hw`), commutes with writing the part (`hset`) and moves the
read pair's input from `pos` to `pos'` (`hread`). -/
theorem KindShape.AddsAt.liftC_conj (g : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k)) (pos pos' : Fin ksT.width → XPos)
    (hw : ∀ p, wsOf (g p) = wsOf p)
    (hset : ∀ p v, g (setWs p ((P.Lw k i).set (wsOf p) v)) =
      setWs (g p) ((P.Lw k i).set (wsOf p) v))
    (hread : ∀ p i', P.readsAt k i = some i' → readP C pos' i' (g p) = readP C pos i' p)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    P.liftC ω k i pos' (g p) = g (P.liftC ω k i pos p) := by
  have hf : P.fC ω k i pos' (g p) = P.fC ω k i pos p := by
    unfold KindShape.AddsAt.fC
    rw [hw, P.xr_reads k i (wsOf p) _ (fun i' => readP C pos i' p) fun i' h => hread p i' h]
  rw [liftC_apply, liftC_apply, hset, hf, hw]

/-- **Additions read at positions that agree on the read pair are equal.** -/
theorem KindShape.AddsAt.liftC_congr (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    {pos pos' : Fin ksT.width → XPos} (h : ∀ i', P.readsAt k i = some i' → pos i' = pos' i') :
    P.liftC (C := C) ω k i pos = P.liftC ω k i pos' :=
  Equiv.ext fun p => (P.liftC_conj ω (Equiv.refl _) k i pos pos' (fun _ => rfl) (fun _ _ => rfl)
    (fun p i' hi => by simp only [readP, Equiv.refl_apply, h i' hi]) p).symm

/-- The value added by addition `i` read at the adversary's pairs, without the ancilla. -/
def KindShape.AddsAt.fQ (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    (q : QueryReg (ksT.CW C) 1 X Y) : Y₁ :=
  if P.onw k i q.1.adv.1.1 then ω (P.xr k i q.1.adv.1.1 fun i' => (q.1.adv.2 i').1) else 0

/-- **Addition `i` read at the adversary's pairs, without the ancilla.** -/
def KindShape.AddsAt.liftQC (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k)) :
    Equiv.Perm (QueryReg (ksT.CW C) 1 X Y) where
  toFun q := (⟨(((P.Lw k i).set q.1.adv.1.1 ((P.Lw k i).get q.1.adv.1.1 + P.fQ ω k i q),
    q.1.adv.1.2), q.1.adv.2), q.1.chal⟩, q.2)
  invFun q := (⟨(((P.Lw k i).set q.1.adv.1.1 ((P.Lw k i).get q.1.adv.1.1 - P.fQ ω k i q),
    q.1.adv.1.2), q.1.adv.2), q.1.chal⟩, q.2)
  left_inv q := by
    simp only [KindShape.AddsAt.fQ, P.onw_set k i _ _, P.xr_set k i _ _ _, RegLens.get_set,
      RegLens.set_set, add_sub_cancel_right, RegLens.set_get]
  right_inv q := by
    simp only [KindShape.AddsAt.fQ, P.onw_set k i _ _, P.xr_set k i _ _ _, RegLens.get_set,
      RegLens.set_set, sub_add_cancel, RegLens.set_get]

/-- **Read at the adversary's pairs, the addition is the identity on the ancilla.** -/
theorem KindShape.AddsAt.liftC_adv (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k)) :
    P.liftC (C := C) ω k i (fun _ => .adv) = liftQ (P.liftQC ω k i) :=
  Equiv.ext fun _ => rfl

/-! ### The pending additions -/

/-- **The additions after Kraus map `k` still pending before the drops at pair `c`**: those
whose drop point is at least `c`, in sequence, read at `pos`. -/
def KindShape.AddsAt.carry (k : StepIdx ksT.slots ksT.post) (c : ℕ) (pos : Fin ksT.width → XPos) :
    Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y) :=
  seqPerm (P.nb k) fun i =>
    if decide (c ≤ optIdx (P.readsAt k i)) then P.liftC ω k i pos else 1

/-- **The additions after Kraus map `k` dropped at pair `c`**, in sequence, read at `pos`. -/
def KindShape.AddsAt.block (k : StepIdx ksT.slots ksT.post) (c : ℕ) (pos : Fin ksT.width → XPos) :
    Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y) :=
  seqPerm (P.nb k) fun i =>
    if decide (optIdx (P.readsAt k i) = c) then P.liftC ω k i pos else 1

/-- **The pending additions are those dropped at pair `c`, then those pending after it**: the list
being sorted, the ones dropped at `c` come first. -/
theorem KindShape.AddsAt.carry_succ (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    (pos : Fin ksT.width → XPos) :
    P.carry (C := C) ω k c pos = P.carry ω k (c + 1) pos * P.block ω k c pos := by
  have h := seqPerm_mask_split (P.nb k) (fun i => P.liftC (C := C) ω k i pos)
    (fun i => decide (optIdx (P.readsAt k i) = c))
    (fun i => decide (c + 1 ≤ optIdx (P.readsAt k i)))
    (fun i h => by simp only [decide_eq_true_eq] at h; omega)
    (fun i j hi hj => by
      simp only [decide_eq_true_eq] at hi hj
      by_contra hl
      have := P.sorted k j i (not_lt.1 hl)
      omega)
  unfold KindShape.AddsAt.carry KindShape.AddsAt.block
  rw [← h]
  congr 1
  funext i
  have e : decide (c ≤ optIdx (P.readsAt k i)) = (decide (optIdx (P.readsAt k i) = c) ||
      decide (c + 1 ≤ optIdx (P.readsAt k i))) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    omega
  rw [e]

/-- **Nothing is pending after the last pair.** -/
theorem KindShape.AddsAt.carry_width (k : StepIdx ksT.slots ksT.post) {c : ℕ} (hc : ksT.width ≤ c)
    (pos : Fin ksT.width → XPos) : P.carry (C := C) ω k c pos = 1 :=
  seqPerm_one _ _ fun i => by
    have := P.optIdx_lt k i
    rw [if_neg (by simp only [decide_eq_true_eq]; omega)]

/-- **Pending additions read at positions that agree on their read pairs are equal.** -/
theorem KindShape.AddsAt.carry_congr (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    {pos pos' : Fin ksT.width → XPos}
    (h : ∀ i, c ≤ optIdx (P.readsAt k i) → ∀ i', P.readsAt k i = some i' → pos i' = pos' i') :
    P.carry (C := C) ω k c pos = P.carry ω k c pos' := by
  unfold KindShape.AddsAt.carry
  congr 1
  funext i
  by_cases hc : c ≤ optIdx (P.readsAt k i)
  · simp only [hc, decide_true, ↓reduceIte]
    exact P.liftC_congr ω k i (h i hc)
  · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- **A permutation of the composed registers carries addition `i` read at `pos` to it read at
`pos'`** when it commutes with writing the part (`hset`), keeps the part, the branches and the point
(`hget`, `hon`, `hxr`) and moves the read pair's input from `pos` to `pos'` (`hread`); it may
change the rest of the workspace. -/
theorem KindShape.AddsAt.liftC_conj' (g : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k)) (pos pos' : Fin ksT.width → XPos)
    (hset : ∀ p v, g (setWs p ((P.Lw k i).set (wsOf p) v)) =
      setWs (g p) ((P.Lw k i).set (wsOf (g p)) v))
    (hget : ∀ p, (P.Lw k i).get (wsOf (g p)) = (P.Lw k i).get (wsOf p))
    (hon : ∀ p, P.onw k i (wsOf (g p)) = P.onw k i (wsOf p))
    (hxr : ∀ p u, P.xr k i (wsOf (g p)) u = P.xr k i (wsOf p) u)
    (hread : ∀ p i', P.readsAt k i = some i' → readP C pos' i' (g p) = readP C pos i' p)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    P.liftC ω k i pos' (g p) = g (P.liftC ω k i pos p) := by
  have hf : P.fC ω k i pos' (g p) = P.fC ω k i pos p := by
    unfold KindShape.AddsAt.fC
    rw [hon, hxr, P.xr_reads k i (wsOf p) _ (fun i' => readP C pos i' p) fun i' h => hread p i' h]
  rw [liftC_apply, liftC_apply, hset, hf, hget]

/-- **The additions dropped at pair `c` carried by a permutation** as in `liftC_conj'`. -/
theorem KindShape.AddsAt.block_conj' (g : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (k : StepIdx ksT.slots ksT.post) (c : ℕ) (pos pos' : Fin ksT.width → XPos)
    (hset : ∀ i p v, g (setWs p ((P.Lw k i).set (wsOf p) v)) =
      setWs (g p) ((P.Lw k i).set (wsOf (g p)) v))
    (hget : ∀ i p, (P.Lw k i).get (wsOf (g p)) = (P.Lw k i).get (wsOf p))
    (hon : ∀ i p, P.onw k i (wsOf (g p)) = P.onw k i (wsOf p))
    (hxr : ∀ i p u, P.xr k i (wsOf (g p)) u = P.xr k i (wsOf p) u)
    (hread : ∀ i p i', P.readsAt k i = some i' → readP C pos' i' (g p) = readP C pos i' p)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    g (P.block ω k c pos p) = P.block ω k c pos' (g p) :=
  seqPerm_conj g (P.nb k)
    (fun i => if decide (optIdx (P.readsAt k i) = c) then P.liftC ω k i pos else 1)
    (fun i => if decide (optIdx (P.readsAt k i) = c) then P.liftC ω k i pos' else 1)
    (fun i q => by
      by_cases h : optIdx (P.readsAt k i) = c
      · simp only [h, decide_true, ↓reduceIte]
        exact (P.liftC_conj' ω g k i pos pos' (hset i) (hget i) (hon i) (hxr i) (hread i) q).symm
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Equiv.Perm.coe_one, id]) p

/-- **The additions dropped at pair `c` change only the parts they write**: a property of the
composed registers kept by writing every part holds after them. -/
theorem KindShape.AddsAt.block_induct (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    (pos : Fin ksT.width → XPos) (R : ReprogrammedQueryReg (ksT.CW C) X Y → Prop)
    (hR : ∀ i p v, R p → R (setWs p ((P.Lw k i).set (wsOf p) v)))
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) (hp : R p) : R (P.block ω k c pos p) :=
  seqPerm_mem {q | R q} _ _ (fun i q hq => by
    split_ifs
    · exact hR i q _ hq
    · exact hq) p hp

/-- **The pending additions carried by a permutation** that keeps the workspace (`hw`), commutes
with writing each part (`hset`) and moves each pending addition's read pair input from `pos` to
`pos'` (`hread`). -/
theorem KindShape.AddsAt.carry_conj (g : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (k : StepIdx ksT.slots ksT.post) (c : ℕ) (pos pos' : Fin ksT.width → XPos)
    (hw : ∀ p, wsOf (g p) = wsOf p)
    (hset : ∀ i p v, g (setWs p ((P.Lw k i).set (wsOf p) v)) =
      setWs (g p) ((P.Lw k i).set (wsOf p) v))
    (hread : ∀ i, c ≤ optIdx (P.readsAt k i) → ∀ p i', P.readsAt k i = some i' →
      readP C pos' i' (g p) = readP C pos i' p)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    g (P.carry ω k c pos p) = P.carry ω k c pos' (g p) :=
  seqPerm_conj g _ _ _ (fun i q => by
    by_cases hc : c ≤ optIdx (P.readsAt k i)
    · simp only [hc, decide_true, ↓reduceIte]
      exact (P.liftC_conj ω g k i pos pos' hw (hset i) (hread i hc) q).symm
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, Equiv.Perm.coe_one, id]) p

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
/-- A permutation that keeps the query pair, applied after another, keeps it. -/
theorem QueryPairFix.mul {V' : Type} {σ τ : Equiv.Perm (QueryReg V' 1 X Y)} (hσ : QueryPairFix σ)
    (hτ : QueryPairFix τ) : QueryPairFix (σ * τ) := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨b, hb⟩ := hτ
  refine ⟨fun x => a x * b x, fun p => ?_⟩
  change σ (τ p) = _
  rw [hb, ha]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem QueryPairFix.one {V' : Type} : QueryPairFix (1 : Equiv.Perm (QueryReg V' 1 X Y)) :=
  ⟨fun _ => 1, fun _ => rfl⟩

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in
theorem queryPairFix_seqPerm {V' : Type} :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm (QueryReg V' 1 X Y)), (∀ i, QueryPairFix (f i)) →
      QueryPairFix (seqPerm n f)
  | 0, _, _ => QueryPairFix.one
  | n + 1, _, h => QueryPairFix.mul (h _) (queryPairFix_seqPerm n _ fun _ => h _)

/-- **The pending additions keep the query pair.** -/
theorem KindShape.AddsAt.queryPairFix_carry (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    (pos : Fin ksT.width → XPos) : QueryPairFix (P.carry (C := C) ω k c pos) :=
  queryPairFix_seqPerm _ _ fun i => by
    split_ifs
    · exact P.queryPairFix_liftC ω k i pos
    · exact QueryPairFix.one

/-! ### The pending additions read at the adversary's pairs -/

/-- **The pending additions read at the adversary's pairs, without the ancilla.** -/
def KindShape.AddsAt.carryQ (k : StepIdx ksT.slots ksT.post) (c : ℕ) :
    Equiv.Perm (QueryReg (ksT.CW C) 1 X Y) :=
  seqPerm (P.nb k) fun i => if decide (c ≤ optIdx (P.readsAt k i)) then P.liftQC ω k i else 1

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
theorem liftQ_seqPerm {V : Type} [Fintype V] [DecidableEq V] :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm (QueryReg V 1 X Y)),
      liftQ (seqPerm n f) = seqPerm n fun i => liftQ (f i)
  | 0, _ => Equiv.ext fun _ => rfl
  | n + 1, f => by
    change liftQ (f (Fin.last n) * seqPerm n fun i => f i.castSucc) =
      liftQ (f (Fin.last n)) * seqPerm n fun i => liftQ (f i.castSucc)
    rw [← liftQ_seqPerm n]
    exact Equiv.ext fun _ => rfl

/-- **Read at the adversary's pairs, the pending additions are the identity on the ancilla.** -/
theorem KindShape.AddsAt.carry_adv (k : StepIdx ksT.slots ksT.post) (c : ℕ) :
    P.carry (C := C) ω k c (fun _ => .adv) = liftQ (P.carryQ ω k c) := by
  unfold KindShape.AddsAt.carry KindShape.AddsAt.carryQ
  rw [liftQ_seqPerm]
  congr 1
  funext i
  split_ifs
  · exact P.liftC_adv ω k i
  · exact Equiv.ext fun _ => rfl

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- A commutation of lifted permutations is a commutation of the permutations. -/
theorem comm_of_liftQ {V : Type} [Fintype V] [DecidableEq V] {g τ : Equiv.Perm (QueryReg V 1 X Y)}
    (h : ∀ p, liftQ g (liftQ τ p) = liftQ τ (liftQ g p)) (q : QueryReg V 1 X Y) :
    g (τ q) = τ (g q) := by
  have := congrArg (fun p => (ancSplit V X Y p).1)
    (h ((ancSplit V X Y).symm (q, ((q.2 0).1, (q.2 0).2, false))))
  simpa [liftQ_apply] using this

/-- **A gate without the ancilla commuting with the pending additions read at the adversary's
pairs is invariant under them.** -/
theorem KindShape.AddsAt.opInv_ofPerm_adv (g : Equiv.Perm (QueryReg (ksT.CW C) 1 X Y))
    (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    (hg : ∀ p, liftQ g (P.carry ω k c (fun _ => .adv) p) =
      P.carry ω k c (fun _ => .adv) (liftQ g p)) :
    OpInv (P.carry ω k c fun _ => .adv) (KrausMap.ofPerm g).liftAnc := by
  rw [P.carry_adv]
  rw [P.carry_adv] at hg
  exact OpInv.liftAnc (opInv_ofPerm fun q => comm_of_liftQ hg q)

/-- **The pending additions carried by a permutation on the flag down** (`carry_conj` with
`hread` on the basis states with the flag down only). -/
theorem KindShape.AddsAt.carry_conj_flagF (g : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (k : StepIdx ksT.slots ksT.post) (c : ℕ) (pos pos' : Fin ksT.width → XPos)
    (hw : ∀ p, wsOf (g p) = wsOf p)
    (hset : ∀ i p v, g (setWs p ((P.Lw k i).set (wsOf p) v)) =
      setWs (g p) ((P.Lw k i).set (wsOf p) v))
    (hread : ∀ i, c ≤ optIdx (P.readsAt k i) → ∀ p, p ∈ flagF (ksT.CW C) X Y → ∀ i',
      P.readsAt k i = some i' → readP C pos' i' (g p) = readP C pos i' p)
    (p : ReprogrammedQueryReg (ksT.CW C) X Y) (hp : p ∈ flagF (ksT.CW C) X Y) :
    g (P.carry ω k c pos p) = P.carry ω k c pos' (g p) :=
  seqPerm_conj_on g (flagF (ksT.CW C) X Y) _ _ _
    (fun i q hq => by
      split_ifs
      · exact hq
      · exact hq)
    (fun i q hq => by
      by_cases hc : c ≤ optIdx (P.readsAt k i)
      · simp only [hc, decide_true, ↓reduceIte]
        have hf : P.fC ω k i pos' (g q) = P.fC ω k i pos q := by
          unfold KindShape.AddsAt.fC
          rw [hw, P.xr_reads k i (wsOf q) _ (fun i' => readP C pos i' q)
            fun i' h => hread i hc q hq i' h]
        rw [liftC_apply, liftC_apply, hset, hf, hw]
      · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte, Equiv.Perm.coe_one, id])
    p hp

/-! ### The gates of the composition and the pending additions -/

/-- **The request measurement is invariant under the pending additions read at the adversary's
pairs.** -/
theorem KindShape.AddsAt.opInv_measReq (P : ksT.AddsAt T.kind Y₁) (ω : X → Y₁)
    (k : StepIdx ksT.slots ksT.post) (c : ℕ) (j : Fin ksT.slots) :
    OpInv (P.carry (C := C) ω k c fun _ => .adv) (T.measReq C j).liftAnc := by
  have hc : ∀ p, liftQ (T.copyReq C j) (P.carry ω k c (fun _ => .adv) p) =
      P.carry ω k c (fun _ => .adv) (liftQ (T.copyReq C j) p) :=
    P.carry_conj ω _ k c _ _
      (fun p => by
        simp only [liftQ_apply, ancSplit, KindAlg.copyReq, Function.Involutive.toPerm,
          Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
        split_ifs <;> rfl)
      (fun i p v => by
        obtain ⟨⟨⟨⟨⟨w, rq, rs⟩, prs⟩, u⟩, anc⟩, qp⟩ := p
        simp only [liftQ_apply, ancSplit, setWs, KindAlg.copyReq, Function.Involutive.toPerm,
          Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, DReg.workspace, DReg.request]
        rw [P.kind_set k i w v]
        split_ifs <;> rfl)
      (fun i _ p i' _ => by
        simp only [readP, XPos.read, liftQ_apply, ancSplit, KindAlg.copyReq,
          Function.Involutive.toPerm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
        split_ifs <;> rfl)
  rw [P.carry_adv] at hc ⊢
  refine OpInv.liftAnc (OpInv.comp (opInv_ofPerm fun q => comm_of_liftQ hc q)
    (opInv_measureFn fun q => ?_))
  refine seqPerm_comp_eq (T.reqOutcome C) _ _ (fun i q => ?_) q
  split_ifs
  · unfold KindAlg.reqOutcome
    change (if T.kind ((P.Lw k i).set q.1.adv.1.1 _) then _ else _) = _
    rw [P.kind_set k i]
    rfl
  · rfl

/-- **A gate without the ancilla that keeps the adversary's workspace and pairs commutes with the
pending additions read at them.** -/
theorem KindShape.AddsAt.opInv_of_keep (g : Equiv.Perm (QueryReg (ksT.CW C) 1 X Y))
    (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    (hw : ∀ q, (g q).1.adv.1.1 = q.1.adv.1.1) (hp : ∀ q, (g q).1.adv.2 = q.1.adv.2)
    (hset : ∀ q (w : ksT.W), g (⟨((w, q.1.adv.1.2), q.1.adv.2), q.1.chal⟩, q.2) =
      (⟨((w, (g q).1.adv.1.2), (g q).1.adv.2), (g q).1.chal⟩, (g q).2)) :
    OpInv (P.carry ω k c fun _ => .adv) (KrausMap.ofPerm g).liftAnc :=
  P.opInv_ofPerm_adv ω g k c (P.carry_conj ω _ k c _ _
    (fun p => hw _)
    (fun i p v => by
      have h := hset (p.1.1, p.2) ((P.Lw k i).set (wsOf p) v)
      simp only [liftQ_apply, ancSplit, setWs, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      rw [h])
    (fun i _ p i' _ => by
      simp only [readP, XPos.read, liftQ_apply, ancSplit, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      rw [hp]))

/-- The write of the reply is invariant under the pending additions. -/
theorem KindShape.AddsAt.opInv_writeReply (k : StepIdx ksT.slots ksT.post) (c : ℕ) (j : Fin ksT.slots) :
    OpInv (P.carry ω k c fun _ => .adv) (KrausMap.ofPerm (T.writeReply C j)).liftAnc :=
  P.opInv_of_keep ω _ k c
    (fun q => by
      simp only [KindAlg.writeReply, Function.Involutive.toPerm, Equiv.coe_fn_mk]
      split_ifs <;> rfl)
    (fun q => by
      simp only [KindAlg.writeReply, Function.Involutive.toPerm, Equiv.coe_fn_mk]
      split_ifs <;> rfl)
    (fun q w => by
      simp only [KindAlg.writeReply, Function.Involutive.toPerm, Equiv.coe_fn_mk]
      split_ifs <;> rfl)

variable [Nonempty X] [AddGroup Y]

omit [AddGroup Y] in
/-- The preparation of the challenger's query input is invariant under the pending additions. -/
theorem KindShape.AddsAt.opInv_prepChal (k : StepIdx ksT.slots ksT.post) (c : ℕ) (j : Fin ksT.slots)
    (i : Fin C.q) :
    OpInv (P.carry ω k c fun _ => .adv) (KrausMap.ofPerm (T.prepChal C j i)).liftAnc :=
  P.opInv_of_keep ω _ k c (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

omit [Nonempty X] [AddGroup Y] in
/-- The exchange of the challenger's query pair is invariant under the pending additions. -/
theorem KindShape.AddsAt.opInv_garSwap (k : StepIdx ksT.slots ksT.post) (c : ℕ) (j : Fin ksT.slots)
    (i : Fin C.q) :
    OpInv (P.carry ω k c fun _ => .adv) (KrausMap.ofPerm (T.garSwap C j i)).liftAnc :=
  P.opInv_of_keep ω _ k c (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

omit [Nonempty X] [AddGroup Y] in
/-- **The exchanges and the addition of a reprogrammed query are invariant under the pending
additions read at the adversary's pairs**, for assignments reading only the challenger's
registers. -/
theorem KindShape.AddsAt.opInv_reprogSwap (a : ksT.CW C → List (Assignment X Y))
    (hac : ∀ v v', v.chal = v'.chal → a v = a v') (k : StepIdx ksT.slots ksT.post) (c : ℕ) :
    OpInv (P.carry ω k c fun _ => .adv) (KrausMap.ofPerm (reprogSwap a)) := by
  refine opInv_ofPerm fun p => P.carry_conj ω _ k c _ _ (fun p => ?_) (fun i p v => ?_)
    (fun i _ p i' _ => ?_) p
  · rw [reprogSwap_apply]
    split_ifs <;> rfl
  · have hcnd : reprogCond a (setWs p ((P.Lw k i).set (wsOf p) v)) ↔ reprogCond a p := by
      simp only [reprogCond, setWs]
      rw [hac ⟨(((P.Lw k i).set (wsOf p) v, p.1.1.adv.1.2), p.1.1.adv.2), p.1.1.chal⟩ p.1.1 rfl]
      rfl
    rw [reprogSwap_apply, reprogSwap_apply]
    by_cases h : reprogCond a p
    · rw [if_pos (hcnd.2 h), if_pos h]
      rfl
    · rw [if_neg (fun h' => h (hcnd.1 h')), if_neg h]
  · simp only [readP, XPos.read]
    rw [reprogSwap_apply]
    split_ifs <;> rfl

omit [Nonempty X] in
/-- **The second exchange and the addition of a reprogrammed query are invariant under the
pending additions read at the adversary's pairs.** -/
theorem KindShape.AddsAt.opInv_reprogTail (a : ksT.CW C → List (Assignment X Y))
    (hac : ∀ v v', v.chal = v'.chal → a v = a v') (k : StepIdx ksT.slots ksT.post) (c : ℕ) :
    OpInv (P.carry ω k c fun _ => .adv)
      ((KrausMap.ofPerm (reprogAdd a)).comp (KrausMap.ofPerm (reprogSwap a))) := by
  refine OpInv.comp (opInv_ofPerm fun p => P.carry_conj ω _ k c _ _ (fun p => rfl)
    (fun i p v => ?_) (fun i _ p i' _ => rfl) p) (P.opInv_reprogSwap ω a hac k c)
  obtain ⟨⟨w, ax, ay, fl⟩, qp⟩ := p
  simp only [reprogAdd, queryPermOf_apply, setWs]
  rw [hac ⟨(((P.Lw k i).set (wsOf ((w, ax, ay, fl), qp)) v, w.adv.1.2), w.adv.2), w.chal⟩ w rfl]

/-- The positions with pair `i` in the query register. -/
def posQry {n : ℕ} (i : Fin n) : Fin n → XPos := fun j => if j = i then .qry else .adv

/-- The positions with pair `i`'s input read at the flagged read. -/
def posTil {n : ℕ} (i : Fin n) : Fin n → XPos := fun j => if j = i then .til else .adv

omit [Nonempty X] [AddGroup Y] in
/-- **Moving pair `i` into the query register**: the pending additions read pair `i` from it. -/
theorem KindShape.AddsAt.chRel_advSwap_in (k : StepIdx ksT.slots ksT.post) (c : ℕ) (i : Fin ksT.width)
    (S : Set (ReprogrammedQueryReg (ksT.CW C) X Y)) :
    ChRel (P.carry ω k c (posQry i)) (P.carry ω k c fun _ => .adv) S
      (KrausMap.ofPerm (T.advSwap C i)).liftAnc (KrausMap.ofPerm (T.advSwap C i)).liftAnc := by
  refine chRel_congr (liftAnc_ofPerm_apply _) (liftAnc_ofPerm_apply _)
    (chRel_ofPerm fun a _ => P.carry_conj ω _ k c _ _ (fun _ => rfl) (fun _ _ _ => rfl)
      (fun i₁ _ p i' _ => ?_) a)
  obtain ⟨⟨⟨⟨⟨w, rq, rs⟩, prs⟩, u⟩, anc⟩, qp⟩ := p
  by_cases h : i' = i
  · subst h
    simp [readP, posQry, XPos.read, liftQ_apply, ancSplit, KindAlg.advSwap, pairSwap,
      Function.Involutive.toPerm]
  · simp [readP, posQry, XPos.read, h, liftQ_apply, ancSplit, KindAlg.advSwap, pairSwap,
      Function.Involutive.toPerm]

omit [Nonempty X] [AddGroup Y] in
/-- **Moving pair `i` back out of the query register**, no pending addition reading it. -/
theorem KindShape.AddsAt.chRel_advSwap_out (k : StepIdx ksT.slots ksT.post) (i : Fin ksT.width)
    (S : Set (ReprogrammedQueryReg (ksT.CW C) X Y)) :
    ChRel (P.carry ω k (i + 1) fun _ => .adv) (P.carry ω k (i + 1) fun _ => .adv) S
      (KrausMap.ofPerm (T.advSwap C i)).liftAnc (KrausMap.ofPerm (T.advSwap C i)).liftAnc := by
  refine chRel_congr (liftAnc_ofPerm_apply _) (liftAnc_ofPerm_apply _)
    (chRel_ofPerm fun a _ => P.carry_conj ω _ k (i + 1) _ _ (fun _ => rfl) (fun _ _ _ => rfl)
      (fun i₁ hc p i' hi' => ?_) a)
  have hne : i' ≠ i := fun h => by
    rw [hi', h] at hc
    simp [optIdx] at hc
  obtain ⟨⟨⟨⟨⟨w, rq, rs⟩, prs⟩, u⟩, anc⟩, qp⟩ := p
  simp [readP, XPos.read, liftQ_apply, ancSplit, KindAlg.advSwap, pairSwap,
    Function.Involutive.toPerm, Function.update_of_ne hne]

omit [Nonempty X] [AddGroup Y] in
/-- **The first exchange of a reprogrammed query moves pair `i`'s read to the flagged read**, on
the flag down, for assignments reading only the challenger's registers. -/
theorem KindShape.AddsAt.chRel_reprogSwap (a : ksT.CW C → List (Assignment X Y))
    (hac : ∀ v v', v.chal = v'.chal → a v = a v') (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    (i : Fin ksT.width) :
    ChRel (P.carry ω k c (posTil i)) (P.carry ω k c (posQry i)) (flagF (ksT.CW C) X Y)
      (KrausMap.ofPerm (reprogSwap a)) (KrausMap.ofPerm (reprogSwap a)) := by
  refine chRel_ofPerm fun p hp => P.carry_conj_flagF ω _ k c _ _ (fun p => ?_) (fun i₁ p v => ?_)
    (fun i₁ _ p hp i' _ => ?_) p hp
  · rw [reprogSwap_apply]
    split_ifs <;> rfl
  · have hcnd : reprogCond a (setWs p ((P.Lw k i₁).set (wsOf p) v)) ↔ reprogCond a p := by
      simp only [reprogCond, setWs]
      rw [hac ⟨(((P.Lw k i₁).set (wsOf p) v, p.1.1.adv.1.2), p.1.1.adv.2), p.1.1.chal⟩ p.1.1 rfl]
      rfl
    rw [reprogSwap_apply, reprogSwap_apply]
    by_cases h : reprogCond a p
    · rw [if_pos (hcnd.2 h), if_pos h]
      rfl
    · rw [if_neg (fun h' => h (hcnd.1 h')), if_neg h]
  · obtain ⟨⟨w, ax, ay, fl⟩, qp⟩ := p
    simp only [flagF, Set.mem_setOf_eq] at hp
    subst hp
    rw [reprogSwap_apply]
    by_cases h : i' = i
    · subst h
      split_ifs <;> simp [readP, posTil, posQry, XPos.read, swapFlip]
    · split_ifs <;> simp [readP, posTil, posQry, XPos.read, swapFlip, h]

omit [Nonempty X] [AddGroup Y] in
/-- The additions keep the challenger's registers, the ancilla and the query register. -/
theorem KindShape.AddsAt.liftC_fix (k : StepIdx ksT.slots ksT.post) (i : Fin (P.nb k))
    (pos : Fin ksT.width → XPos) (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    (P.liftC ω k i pos p).1.1.chal = p.1.1.chal ∧ (P.liftC ω k i pos p).1.2 = p.1.2 ∧
      (P.liftC ω k i pos p).2 = p.2 :=
  ⟨rfl, rfl, rfl⟩

omit [Nonempty X] [AddGroup Y] in
theorem KindShape.AddsAt.block_fix (k : StepIdx ksT.slots ksT.post) (c : ℕ)
    (pos : Fin ksT.width → XPos) (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    (P.block ω k c pos p).1.1.chal = p.1.1.chal ∧ (P.block ω k c pos p).1.2 = p.1.2 ∧
      (P.block ω k c pos p).2 = p.2 := by
  refine ⟨seqPerm_comp_eq (fun q => q.1.1.chal) _ _ (fun i q => ?_) p,
    seqPerm_comp_eq (fun q => q.1.2) _ _ (fun i q => ?_) p,
    seqPerm_comp_eq (fun q => q.2) _ _ (fun i q => ?_) p⟩ <;> split_ifs <;> rfl

omit [Nonempty X] [AddGroup Y] in
/-- **Dropping the additions of pair `i` after its query**: the write `W` against the write followed
by them, for a write commuting with every addition (`hW`). -/
theorem KindShape.AddsAt.chRel_drop (W : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hW : ∀ k i pos p, W (P.liftC ω k i pos p) = P.liftC ω k i pos (W p))
    (k : StepIdx ksT.slots ksT.post) (i : Fin ksT.width) (S : Set (ReprogrammedQueryReg (ksT.CW C) X Y)) :
    ChRel (P.carry ω k (i + 1) fun _ => .adv) (P.carry ω k i (posTil i)) S (KrausMap.ofPerm W)
      (KrausMap.ofPerm (W.trans (P.block ω k i (posTil i)))) := by
  have hc : P.carry (C := C) ω k (i + 1) (posTil i) = P.carry ω k (i + 1) fun _ => .adv :=
    P.carry_congr ω k (i + 1) fun i₁ hc i' hi' => by
      have hne : i' ≠ i := fun h => by
        rw [hi', h] at hc
        simp [optIdx] at hc
      simp [posTil, hne]
  have hWs : ∀ (c : ℕ) (pos : Fin ksT.width → XPos) (m : ℕ → Bool) p,
      W (seqPerm (P.nb k) (fun i₁ => if m (optIdx (P.readsAt k i₁)) then
        P.liftC ω k i₁ pos else 1) p) =
      seqPerm (P.nb k) (fun i₁ => if m (optIdx (P.readsAt k i₁)) then
        P.liftC ω k i₁ pos else 1) (W p) := fun c pos m p =>
    seqPerm_conj W _ _ _ (fun i₁ q => by
      split_ifs
      · exact hW k i₁ pos q
      · rfl) p
  refine chRel_ofPerm₂ fun p _ => ?_
  rw [P.carry_succ, Equiv.Perm.mul_apply, Equiv.trans_apply, ← hc]
  rw [show P.carry (C := C) ω k (i + 1) (posTil i) = seqPerm (P.nb k) (fun i₁ =>
    if (fun d : ℕ => decide ((i : ℕ) + 1 ≤ d)) (optIdx (P.readsAt k i₁)) then
      P.liftC ω k i₁ (posTil i) else 1) from rfl,
    hWs ((i : ℕ) + 1) (posTil i) (fun d : ℕ => decide ((i : ℕ) + 1 ≤ d))]
  rw [show P.block (C := C) ω k i (posTil i) = seqPerm (P.nb k) (fun i₁ =>
    if (fun d : ℕ => decide (d = (i : ℕ))) (optIdx (P.readsAt k i₁)) then
      P.liftC ω k i₁ (posTil i) else 1) from rfl,
    hWs i (posTil i) (fun d : ℕ => decide (d = (i : ℕ)))]

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Nonempty X] [AddGroup Y] in
/-- **The pending additions keep the supports between the exchanges**, for assignments reading
only the challenger's registers. -/
theorem KindShape.AddsAt.mem_condSet_of_fix {V' : Type} {a : V' → List (Assignment X Y)}
    {f : Equiv.Perm (ReprogrammedQueryReg V' X Y)} (ha : ∀ p, a (f p).1.1 = a p.1.1)
    (h2 : ∀ p, (f p).1.2 = p.1.2) (h3 : ∀ p, (f p).2 = p.2)
    {p : ReprogrammedQueryReg V' X Y} (hp : p ∈ condSet a) : f p ∈ condSet a := by
  simp only [condSet, Set.mem_setOf_eq, reprogCond, h2, h3, ha] at hp ⊢
  exact hp

omit [Nonempty X] [AddGroup Y] in
theorem permCongr_prodCongr_seqPerm {A' B' Q : Type*} (e : A' × B' ≃ Q) :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm A'),
      e.permCongr ((seqPerm n f).prodCongr (Equiv.refl B')) =
        seqPerm n fun i => e.permCongr ((f i).prodCongr (Equiv.refl B'))
  | 0, _ => Equiv.ext fun _ => by simp [seqPerm]
  | n + 1, f => by
    change e.permCongr ((f (Fin.last n) * seqPerm n fun i => f i.castSucc).prodCongr
      (Equiv.refl B')) = e.permCongr ((f (Fin.last n)).prodCongr (Equiv.refl B')) *
        seqPerm n fun i => e.permCongr ((f i.castSucc).prodCongr (Equiv.refl B'))
    rw [← permCongr_prodCongr_seqPerm e n]
    exact Equiv.ext fun _ => by simp [Equiv.permCongr_apply]; rfl

omit [Nonempty X] [AddGroup Y] in
/-- **Kraus map `k` of `T.withStep st'` on the composed registers is that of `T` followed by the
additions after it, all pending**, when `st' k` is `T.step k` followed by them. -/
theorem KindShape.AddsAt.chRel_advKraus
    {st' : StepIdx ksT.slots ksT.post → KrausMap ksT.R (DReg ksT.W ksT.width X Y Req Resp)
      (DReg ksT.W ksT.width X Y Req Resp)} (k : StepIdx ksT.slots ksT.post)
    (h : KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (T.step k))
    (S : Set (ReprogrammedQueryReg (ksT.CW C) X Y)) :
    ChRel (P.carry ω k 0 fun _ => .adv) 1 S ((T.withStep st').advKraus C k).liftAnc
      ((T.advKraus C k).liftAnc) := fun ρ _ => by
  have h1 := ((h.tensorId (CRest X Y Req ksT.slots C.q C.Coins)).reindex (T.advSplit C)).liftAnc
  have e : liftQ ((T.advSplit C).permCongr
      ((P.toStepAdds.perm ω k).prodCongr (Equiv.refl _))) = P.carry ω k 0 fun _ => .adv := by
    rw [P.carry_adv]
    unfold StepAdds.perm KindShape.AddsAt.carryQ
    rw [permCongr_prodCongr_seqPerm]
    congr 2
  rw [e] at h1
  simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id]
  exact h1.apply ρ

omit [Nonempty X] [AddGroup Y] in
/-- **A permutation commuting with every addition commutes with the pending ones.** -/
theorem KindShape.AddsAt.carry_comm (W : Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    {k : StepIdx ksT.slots ksT.post} (hW : ∀ i pos p, W (P.liftC ω k i pos p) = P.liftC ω k i pos (W p))
    (c : ℕ) (pos : Fin ksT.width → XPos) (p : ReprogrammedQueryReg (ksT.CW C) X Y) :
    W (P.carry ω k c pos p) = P.carry ω k c pos (W p) :=
  seqPerm_conj W (P.nb k)
    (fun i => if decide (c ≤ optIdx (P.readsAt k i)) then P.liftC ω k i pos else 1)
    (fun i => if decide (c ≤ optIdx (P.readsAt k i)) then P.liftC ω k i pos else 1)
    (fun i q => by
      by_cases h : c ≤ optIdx (P.readsAt k i)
      · simp only [h, decide_true, ↓reduceIte]
        exact hW i pos q
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Equiv.Perm.coe_one, id]) p

/-! ### The queries of the composition -/

variable (ksT C) in
/-- **A query of the composition**, in gate order: query `i` of the challenger in slot `j`, the
query of pair `i` in slot `j`, or the query of pair `i` in post batch `b`. -/
inductive KindShape.QueryPos
  | chal (j : Fin ksT.slots) (i : Fin C.q)
  | pair (j : Fin ksT.slots) (i : Fin ksT.width)
  | post (b : Fin ksT.post) (i : Fin ksT.width)

/-- **A query of the composition of a kind algorithm**: one of its shape (`KindShape.QueryPos`). -/
abbrev KindAlg.QueryPos (T : KindAlg ksT O) (C : Challenger X Y Req Resp) : Type :=
  ksT.QueryPos C

/-- **The number of a query of the composition**, counted from `1`. -/
def KindShape.QueryPos.idx : ksT.QueryPos C → ℕ
  | .chal j i => (j : ℕ) * (C.q + ksT.width) + i + 1
  | .pair j i => (j : ℕ) * (C.q + ksT.width) + C.q + i + 1
  | .post b i => ksT.slots * (C.q + ksT.width) + (b : ℕ) * ksT.width + i + 1

/-- **The additions dropped after a query**: those of pair `i` after its query in a slot or a post
batch, none after the challenger's queries. -/
def KindShape.AddsAt.dropAt : ksT.QueryPos C → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y)
  | .chal _ _ => 1
  | .pair j i => P.block ω (slotStep j) i (posTil i)
  | .post b i => P.block ω (postStep b) i (posTil i)

/-! ### The compiled circuit with the additions dropped after their pairs' queries -/

omit [Nonempty X] in
/-- **One adversary query with the additions of its pair dropped after it**: pair `i`'s query,
from the additions pending before pair `i` to those pending after it, on the flag down; the write
`W (n₀ + 1)` against the write followed by `β (n₀ + 1)`, the additions dropped at pair `i`
(`hβ`). -/
theorem KindShape.AddsAt.twin_advPiece (a : ksT.CW C → List (Assignment X Y))
    (hac : ∀ v v', v.chal = v'.chal → a v = a v') (k : StepIdx ksT.slots ksT.post) (i : Fin ksT.width)
    (n₀ : ℕ) (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hβ : β (n₀ + 1) = P.block ω k i (posTil i))
    (hW : ∀ k i pos p, W (n₀ + 1) (P.liftC ω k i pos p) = P.liftC ω k i pos (W (n₀ + 1) p))
    (hWk : ∀ p, (W (n₀ + 1) p).1.1.chal = p.1.1.chal ∧ (W (n₀ + 1) p).1.2 = p.1.2 ∧
      (W (n₀ + 1) p).2 = p.2) :
    Circuit.Twin QueryPairFix WXDep (P.carry ω k (i + 1) fun _ => .adv) (flagF (ksT.CW C) X Y)
      ((ReprogrammedCircuit.kraus (KrausMap.ofPerm (T.advSwap C i))
        (.rquery a (.kraus (KrausMap.ofPerm (T.advSwap C i)) .nil))).toCircuit.withPerms W n₀)
      ((ReprogrammedCircuit.kraus (KrausMap.ofPerm (T.advSwap C i))
        (.rquery a (.kraus (KrausMap.ofPerm (T.advSwap C i)) .nil))).toCircuit.withPerms
          (fun n => (W n).trans (β n)) n₀)
      (P.carry ω k i fun _ => .adv) (flagF (ksT.CW C) X Y) := by
  refine .kraus (P.chRel_advSwap_in ω k i i _) (keeps_liftAnc_flagF _) ?_
  refine .kraus (P.chRel_reprogSwap ω a hac k i i) (keeps_reprogSwap_flagF a) ?_
  refine .query (P.queryPairFix_carry ω k i _) (wxDep_condSet a) ?_
  change Circuit.Twin _ _ _ _ (.kraus (KrausMap.ofPerm (W (n₀ + 1))) _)
    (.kraus (KrausMap.ofPerm ((W (n₀ + 1)).trans (β (n₀ + 1)))) _) _ _
  rw [hβ]
  refine .kraus (S' := condSet a) (P.chRel_drop ω (W (n₀ + 1)) hW k i _)
    (keeps_ofPerm_of fun p hp => ?_) ?_
  · rw [Equiv.trans_apply]
    refine mem_condSet_of_fix (f := P.block ω k i (posTil i))
      (fun q => hac _ _ (P.block_fix ω k i _ q).1) (fun q => (P.block_fix ω k i _ q).2.1)
      (fun q => (P.block_fix ω k i _ q).2.2) ?_
    exact mem_condSet_of_fix (f := W (n₀ + 1)) (fun q => hac _ _ (hWk q).1)
      (fun q => (hWk q).2.1) (fun q => (hWk q).2.2) hp
  refine .kraus ((P.opInv_reprogTail ω a hac k (i + 1)).chRel _) (keeps_reprogTail a) ?_
  refine .kraus (P.chRel_advSwap_out ω k i _) (keeps_liftAnc_flagF _) ?_
  exact .nil rfl rfl

omit [Nonempty X] in
/-- **The adversary's queries of a slot or a post batch with each pair's additions dropped after
its query**, from all the additions after Kraus map `k` pending to none; `β (n₀ + i + 1)` drops
those of pair `i`. -/
theorem KindShape.AddsAt.twin_advQueries (a : ksT.CW C → List (Assignment X Y))
    (hac : ∀ v v', v.chal = v'.chal → a v = a v') (k : StepIdx ksT.slots ksT.post) (n₀ : ℕ)
    (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hβ : ∀ i : Fin ksT.width, β (n₀ + i + 1) = P.block ω k i (posTil i))
    (hW : ∀ n k i pos p, W n (P.liftC ω k i pos p) = P.liftC ω k i pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2) :
    Circuit.Twin QueryPairFix WXDep 1 (flagF (ksT.CW C) X Y)
      ((T.advQueries C a).toCircuit.withPerms W n₀)
      ((T.advQueries C a).toCircuit.withPerms (fun n => (W n).trans (β n)) n₀)
      (P.carry ω k 0 fun _ => .adv) (flagF (ksT.CW C) X Y) := by
  have h := twin_concat_finRange (QI := QueryPairFix) (SI := WXDep) W (fun n => (W n).trans (β n))
    (L := 1) n₀
    (fun i => ReprogrammedCircuit.kraus (KrausMap.ofPerm (T.advSwap C i))
      (.rquery a (.kraus (KrausMap.ofPerm (T.advSwap C i)) .nil)))
    (fun i => ReprogrammedCircuit.kraus (KrausMap.ofPerm (T.advSwap C i))
      (.rquery a (.kraus (KrausMap.ofPerm (T.advSwap C i)) .nil))) (fun _ => rfl) (fun _ => rfl)
    (fun n => P.carry ω k n fun _ => .adv) (fun _ => flagF (ksT.CW C) X Y) fun i =>
      P.twin_advPiece ω a hac k i (n₀ + i * 1) W β (by rw [Nat.mul_one]; exact hβ i) (hW _)
        (hWk _)
  rw [P.carry_width ω k le_rfl] at h
  exact h

/-- **One query of the challenger with the pending additions carried across it**, `β` the
identity after it (`hβ`). -/
theorem KindShape.AddsAt.twin_chalPiece (k : StepIdx ksT.slots ksT.post) (c : ℕ) (j : Fin ksT.slots)
    (i : Fin C.q) (n₀ : ℕ) (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hβ : β (n₀ + 1) = 1)
    (hW : ∀ k i pos p, W (n₀ + 1) (P.liftC ω k i pos p) = P.liftC ω k i pos (W (n₀ + 1) p))
    (hWk : ∀ p, (W (n₀ + 1) p).1.1.chal = p.1.1.chal ∧ (W (n₀ + 1) p).1.2 = p.1.2 ∧
      (W (n₀ + 1) p).2 = p.2) :
    Circuit.Twin QueryPairFix WXDep (P.carry ω k c fun _ => .adv) (flagF (ksT.CW C) X Y)
      ((ReprogrammedCircuit.kraus (KrausMap.ofPerm (T.prepChal C j i))
        (.rquery (fun v => T.chalAss C j i v.chal)
          (.kraus (KrausMap.ofPerm (T.garSwap C j i)) .nil))).toCircuit.withPerms W n₀)
      ((ReprogrammedCircuit.kraus (KrausMap.ofPerm (T.prepChal C j i))
        (.rquery (fun v => T.chalAss C j i v.chal)
          (.kraus (KrausMap.ofPerm (T.garSwap C j i)) .nil))).toCircuit.withPerms
            (fun n => (W n).trans (β n)) n₀)
      (P.carry ω k c fun _ => .adv) (flagF (ksT.CW C) X Y) := by
  set a : ksT.CW C → List (Assignment X Y) := fun v => T.chalAss C j i v.chal
  have hac : ∀ v v', v.chal = v'.chal → a v = a v' := fun v v' h => by simp only [a, h]
  refine .kraus ((P.opInv_prepChal ω k c j i).chRel _) (keeps_liftAnc_flagF _) ?_
  refine .kraus ((P.opInv_reprogSwap ω a hac k c).chRel _) (keeps_reprogSwap_flagF a) ?_
  refine .query (P.queryPairFix_carry ω k c _) (wxDep_condSet a) ?_
  change Circuit.Twin _ _ _ _ (.kraus (KrausMap.ofPerm (W (n₀ + 1))) _)
    (.kraus (KrausMap.ofPerm ((W (n₀ + 1)).trans (β (n₀ + 1)))) _) _ _
  rw [hβ, Equiv.Perm.one_def, Equiv.trans_refl]
  refine .kraus (chRel_ofPerm fun p _ => P.carry_comm ω _ (hW k) c _ p)
    (keeps_ofPerm_of fun p hp => mem_condSet_of_fix (f := W (n₀ + 1))
      (fun q => hac _ _ (hWk q).1) (fun q => (hWk q).2.1) (fun q => (hWk q).2.2) hp) ?_
  refine .kraus ((P.opInv_reprogTail ω a hac k c).chRel _) (keeps_reprogTail a) ?_
  refine .kraus ((P.opInv_garSwap ω k c j i).chRel _) (keeps_liftAnc_flagF _) ?_
  exact .nil rfl rfl

/-- **The challenger's queries of slot `j` with the pending additions carried across them.** -/
theorem KindShape.AddsAt.twin_chalQueries (k : StepIdx ksT.slots ksT.post) (c : ℕ) (j : Fin ksT.slots)
    (n₀ : ℕ) (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hβ : ∀ i : Fin C.q, β (n₀ + i + 1) = 1)
    (hW : ∀ n k i pos p, W n (P.liftC ω k i pos p) = P.liftC ω k i pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2) :
    Circuit.Twin QueryPairFix WXDep (P.carry ω k c fun _ => .adv) (flagF (ksT.CW C) X Y)
      ((T.chalQueries C j).toCircuit.withPerms W n₀)
      ((T.chalQueries C j).toCircuit.withPerms (fun n => (W n).trans (β n)) n₀)
      (P.carry ω k c fun _ => .adv) (flagF (ksT.CW C) X Y) := by
  unfold KindAlg.chalQueries
  exact twin_concat_finRange (QI := QueryPairFix) (SI := WXDep) W (fun n => (W n).trans (β n))
    (L := 1) n₀ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => P.carry ω k c fun _ => .adv)
    (fun _ => flagF (ksT.CW C) X Y) fun i =>
      P.twin_chalPiece ω k c j i (n₀ + i * 1) W β (by rw [Nat.mul_one]; exact hβ i) (hW _)
        (hWk _)

/-- **Slot `j` of the composition with the additions after its Kraus map dropped after their
pairs' queries** (`hβ`), `β` the identity after the challenger's queries (`hβc`). -/
theorem KindShape.AddsAt.twin_slot (P : ksT.AddsAt T.kind Y₁) (ω : X → Y₁)
    {st' : StepIdx ksT.slots ksT.post → KrausMap ksT.R (DReg ksT.W ksT.width X Y Req Resp)
      (DReg ksT.W ksT.width X Y Req Resp)}
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (T.step k)) (j : Fin ksT.slots)
    (n₀ : ℕ) (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hβc : ∀ i : Fin C.q, β (n₀ + i + 1) = 1)
    (hβ : ∀ i : Fin ksT.width, β (n₀ + C.q + i + 1) = P.block ω (slotStep j) i (posTil i))
    (hW : ∀ n k i pos p, W n (P.liftC ω k i pos p) = P.liftC ω k i pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2) :
    Circuit.Twin QueryPairFix WXDep 1 (flagF (ksT.CW C) X Y)
      (((T.withStep st').slotCircBoth C j).toCircuit.withPerms W n₀)
      ((T.slotCircBoth C j).toCircuit.withPerms (fun n => (W n).trans (β n)) n₀)
      1 (flagF (ksT.CW C) X Y) := by
  unfold KindAlg.slotCircBoth
  refine .kraus (P.chRel_advKraus ω (slotStep j) (hst _) _) (keeps_liftAnc_flagF _) ?_
  refine .kraus ((P.opInv_measReq ω (slotStep j) 0 j).chRel _) (keeps_liftAnc_flagF _) ?_
  refine twin_rc_append (P.twin_chalQueries ω (slotStep j) 0 j n₀ W β hβc hW hWk) ?_
  rw [KindAlg.queries_chalQueries, KindAlg.queries_chalQueries]
  refine .kraus ((P.opInv_writeReply ω (slotStep j) 0 j).chRel _) (keeps_liftAnc_flagF _) ?_
  exact P.twin_advQueries ω (fun v => T.advAss C j v.chal) (fun v v' h => by simp only [h])
    (slotStep j) (n₀ + C.q) W β hβ hW hWk

omit [Nonempty X] in
/-- **Post batch `b` with the additions after its Kraus map dropped after their pairs'
queries.** -/
theorem KindShape.AddsAt.twin_post
    {st' : StepIdx ksT.slots ksT.post → KrausMap ksT.R (DReg ksT.W ksT.width X Y Req Resp)
      (DReg ksT.W ksT.width X Y Req Resp)}
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (T.step k)) (b : Fin ksT.post)
    (n₀ : ℕ) (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hβ : ∀ i : Fin ksT.width, β (n₀ + i + 1) = P.block ω (postStep b) i (posTil i))
    (hW : ∀ n k i pos p, W n (P.liftC ω k i pos p) = P.liftC ω k i pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2) :
    Circuit.Twin QueryPairFix WXDep 1 (flagF (ksT.CW C) X Y)
      (((T.withStep st').postCirc C b).toCircuit.withPerms W n₀)
      ((T.postCirc C b).toCircuit.withPerms (fun n => (W n).trans (β n)) n₀)
      1 (flagF (ksT.CW C) X Y) := by
  unfold KindAlg.postCirc
  refine .kraus (P.chRel_advKraus ω (postStep b) (hst _) _) (keeps_liftAnc_flagF _) ?_
  exact P.twin_advQueries ω (fun v => T.postAss C v.chal) (fun v v' h => by simp only [h])
    (postStep b) n₀ W β hβ hW hWk

omit [Nonempty X] [AddGroup Y] in
/-- **No addition after a Kraus map on any branch: nothing pending.** -/
theorem KindShape.AddsAt.carry_of_off (k : StepIdx ksT.slots ksT.post) (hk : P.Off k)
    (c : ℕ) (pos : Fin ksT.width → XPos) : P.carry (C := C) ω k c pos = 1 :=
  seqPerm_one _ _ fun i => by
    split_ifs
    · exact Equiv.ext fun p => by
        rw [liftC_apply]
        have h : P.fC ω k i pos p = 0 := by
          unfold KindShape.AddsAt.fC
          have h0 : P.onw k i (wsOf p) = false := hk i (wsOf p)
          rw [h0]
          rfl
        rw [h, add_zero, RegLens.set_get, setWs_wsOf]
        rfl
    · rfl

/-- **The composition's whole circuit with each addition dropped after its pair's query**: the
twin compiled circuits of `T.withStep st'` (writes `W`) and of `T` (writes then drops `β`), when the
additions follow `T`'s steps (`hst`), none follows the last one (`hlast`: no query follows it, so
no drop could make it), and `β` after each query is the additions dropped there (`hβ`). -/
theorem KindShape.AddsAt.twin_fullCircBoth (P : ksT.AddsAt T.kind Y₁) (ω : X → Y₁)
    {st' : StepIdx ksT.slots ksT.post → KrausMap ksT.R (DReg ksT.W ksT.width X Y Req Resp)
      (DReg ksT.W ksT.width X Y Req Resp)}
    (hst : ∀ k, KrausMap.LeftPerm (P.toStepAdds.perm ω k) (st' k) (T.step k))
    (hlast : P.Off lastStep)
    (W β : ℕ → Equiv.Perm (ReprogrammedQueryReg (ksT.CW C) X Y))
    (hβ : ∀ q : T.QueryPos C, β q.idx = P.dropAt ω q)
    (hW : ∀ n k i pos p, W n (P.liftC ω k i pos p) = P.liftC ω k i pos (W n p))
    (hWk : ∀ n p, (W n p).1.1.chal = p.1.1.chal ∧ (W n p).1.2 = p.1.2 ∧ (W n p).2 = p.2) :
    Circuit.Twin QueryPairFix WXDep 1 (flagF (ksT.CW C) X Y)
      (((T.withStep st').fullCircBoth C).toCircuit.withPerms W 0)
      ((T.fullCircBoth C).toCircuit.withPerms (fun n => (W n).trans (β n)) 0)
      1 (flagF (ksT.CW C) X Y) := by
  have hβc : ∀ (j : Fin ksT.slots) (i : Fin C.q), β ((j : ℕ) * (C.q + ksT.width) + i + 1) = 1 :=
    fun j i => hβ (.chal j i)
  have hβs : ∀ (j : Fin ksT.slots) (i : Fin ksT.width),
      β ((j : ℕ) * (C.q + ksT.width) + C.q + i + 1) = P.block ω (slotStep j) i (posTil i) :=
    fun j i => hβ (.pair j i)
  have hβp : ∀ (b : Fin ksT.post) (i : Fin ksT.width),
      β (ksT.slots * (C.q + ksT.width) + (b : ℕ) * ksT.width + i + 1) =
        P.block ω (postStep b) i (posTil i) := fun b i => hβ (.post b i)
  unfold KindAlg.fullCircBoth
  have h1 := twin_concat_finRange (QI := QueryPairFix) (SI := WXDep) W
    (fun n => (W n).trans (β n)) (L := C.q + ksT.width) 0 (fun j => (T.withStep st').slotCircBoth C j)
    (fun j => T.slotCircBoth C j) (fun j => (T.withStep st').queries_slotCircBoth C j)
    (fun j => T.queries_slotCircBoth C j) (fun _ => 1) (fun _ => flagF (ksT.CW C) X Y)
    fun j => P.twin_slot ω hst j _ W β (fun i => by simpa using hβc j i)
      (fun i => by simpa using hβs j i) hW hWk
  have h2 := twin_concat_finRange (QI := QueryPairFix) (SI := WXDep) W
    (fun n => (W n).trans (β n)) (L := ksT.width) (0 + ksT.slots * (C.q + ksT.width))
    (fun b => (T.withStep st').postCirc C b) (fun b => T.postCirc C b)
    (fun b => (T.withStep st').queries_postCirc C b) (fun b => T.queries_postCirc C b)
    (fun _ => 1) (fun _ => flagF (ksT.CW C) X Y)
    fun b => P.twin_post ω hst b _ W β (fun i => by simpa using hβp b i) hW hWk
  refine twin_rc_append (σm := 1) (Sm := flagF (ksT.CW C) X Y)
    (twin_rc_append (σm := 1) (Sm := flagF (ksT.CW C) X Y) h1 ?_) ?_
  · rw [queries_concat_finRange' (fun j => (T.withStep st').queries_slotCircBoth C j),
      queries_concat_finRange' (fun j => T.queries_slotCircBoth C j)]
    exact h2
  have hK := P.chRel_advKraus (C := C) ω lastStep (hst _) (flagF (ksT.CW C) X Y)
  rw [P.carry_of_off ω lastStep hlast] at hK
  exact .kraus hK (keeps_liftAnc_flagF _) (.nil rfl rfl)

/-! ### The local queries on a part of the workspace as a list of additions -/

omit [Nonempty X] [AddGroup Y] in
/-- **A single permutation in a list of identities.** -/
theorem seqPerm_single {Z : Type*} :
    ∀ (n : ℕ) (i : Fin n) (a : Equiv.Perm Z), seqPerm n (fun j => if j = i then a else 1) = a
  | 0, i, _ => i.elim0
  | n + 1, i, a => by
    change (if Fin.last n = i then a else 1) *
      seqPerm n (fun j => if j.castSucc = i then a else 1) = a
    by_cases h : i = Fin.last n
    · subst h
      rw [if_pos rfl, seqPerm_one _ _ fun j => if_neg (Fin.castSucc_lt_last j).ne, mul_one]
    · obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 h
      rw [if_neg (Fin.castSucc_lt_last i').ne', one_mul]
      simp only [Fin.castSucc_inj]
      exact seqPerm_single n i' a

variable (D : ksT.BaseQ kind Y₁)

/-- **The local queries of `D` as a list of additions**: after Kraus map `k`, one addition per
pair `i`, coordinate `i` of the part receiving the value at pair `i`'s input. -/
def KindShape.BaseQ.toAddsAt : ksT.AddsAt kind Y₁ where
  nb _ := ksT.width
  Lw _ i := D.Lw.comp (coordLens Y₁ i)
  onw k _ := D.on k
  readsAt _ i := some i
  xr _ i _ u := u i
  onw_set k _ w _ := D.on_set k w _
  xr_set _ _ _ _ _ := rfl
  xr_reads _ i _ _ _ h := h i rfl
  kind_set _ _ w _ := D.kind_set w _
  sorted _ _ _ h := by simpa [optIdx] using h

omit [Nonempty X] [AddGroup Y] in
/-- **Addition `i` of the list is the local query of pair `i` alone.** -/
theorem KindShape.BaseQ.liftC_toAddsAt (k : StepIdx ksT.slots ksT.post) (i : Fin ksT.width)
    (pos : Fin ksT.width → XPos) :
    D.toAddsAt.liftC (C := C) ω k i pos = D.carry ω k (fun j => decide (j = i)) pos := by
  refine Equiv.ext fun p => Prod.ext ?_ rfl
  change (setWs p ((D.Lw.comp (coordLens Y₁ i)).set (wsOf p)
      ((D.Lw.comp (coordLens Y₁ i)).get (wsOf p) + D.toAddsAt.fC ω k i pos p))).1 =
    D.wLens.set p.1 (D.wLens.get p.1 + (D.carryW ω k (fun j => decide (j = i)) pos (p.2 0).1).f p.1)
  simp only [setWs, RegLens.comp, coordLens, KindShape.BaseQ.wLens, KindShape.BaseQ.carryW,
    KindShape.AddsAt.fC, KindShape.BaseQ.toAddsAt, readP]
  congr 4
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
    rfl
  · simp [hj]

omit [Nonempty X] [AddGroup Y] in
/-- **The additions of the list dropped at pair `i` are the local query of pair `i`.** -/
theorem KindShape.BaseQ.block_toAddsAt (k : StepIdx ksT.slots ksT.post) (i : Fin ksT.width) :
    D.toAddsAt.block (C := C) ω k i (posTil i) =
      D.carry ω k (fun j => decide (j = i)) fun _ => .til := by
  unfold KindShape.AddsAt.block
  change seqPerm ksT.width (fun j : Fin ksT.width => if decide (optIdx (some j) = (i : ℕ)) then
    D.toAddsAt.liftC ω k j (posTil i) else 1) = _
  have e : (fun j : Fin ksT.width => if decide (optIdx (some j) = (i : ℕ)) then
      D.toAddsAt.liftC (C := C) ω k j (posTil i) else 1) =
      fun j => if j = i then D.toAddsAt.liftC ω k i (posTil i) else 1 := by
    funext j
    by_cases h : j = i
    · subst h
      simp [optIdx]
    · have : (j : ℕ) ≠ i := fun h' => h (Fin.ext h')
      simp [optIdx, h, this]
  rw [e, seqPerm_single, D.liftC_toAddsAt]
  exact D.carry_congr ω k _ fun j hj => by simp at hj; simp [posTil, hj]

omit [Nonempty X] [AddGroup Y] in
/-- **The list's additions on the adversary's registers are the local query `wsAdd`.** -/
theorem KindShape.BaseQ.toStepAdds_perm (k : StepIdx ksT.slots ksT.post) :
    (D.toAddsAt.toStepAdds (Y := Y) (Req := Req) (Resp := Resp)).perm ω k =
      (wsAdd D.Lw (D.on k) (D.on_set k) ω Req Resp).perm :=
  wsAdds_perm D.Lw D.on D.on_set ω Req Resp k

omit [Nonempty X] [AddGroup Y] in
theorem KindShape.BaseQ.toStepAdds_off (hlast : ∀ w, D.on lastStep w = false) :
    D.toAddsAt.Off lastStep :=
  fun _ w => hlast w

end Composed

end GordieHowe.Quantum
