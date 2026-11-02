-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.BaseShift
public import GordieHowe.Model.Quantum.Pure.MultiRelaySideFactor
public import GordieHowe.Model.Quantum.Pure.MultiRelayPreAdds

@[expose] public section

/-!
# The side additions of the relayed distinguisher as a list of additions

The side additions after a sub-slot (`Distinguisher.sideAddsPerm`) are the list of additions
`Distinguisher.sideAdds` (`StepAdds`) at the side function (`sideAdds_perm`). Addition `i` writes
the side store's entry at `sideAddPos i`: the slot `j` of the relayed request in progress (read from
the record and the clock) and the side reads `ns` made before it (read from the side entries
strictly below `ns`), so writing the entry changes neither its position nor its point. Its point is
the side read the program makes there, if any (`sideAddAct`).

The relayed step at the side function is the step at the zero side function followed by these
additions conjugated by the record and the set-up (`relay_step_eq_sideAdds_conj`): the side
additions occur mid-step and are moved after the step by conjugation with the rest of the step
(`Distinguisher.relay_step_eq_withSide_zero`, `StepAdds.perm_conj`).

- `Distinguisher.blockAns`, `Distinguisher.sideNb`, `Distinguisher.lt_of_sideNb`,
  `Distinguisher.setSide`, `Distinguisher.setSide_record`.
- `Distinguisher.sideAddPos`, `Distinguisher.sideAddAct`, `Distinguisher.sideAddLens`,
  `Distinguisher.sideAdds`; `pendSt_update`, `sideAddPos_set`, `sideAddAct_set` (the position and
  the point do not read the entry written).
- `Distinguisher.sideAdds_add_perm`, `Distinguisher.seqPerm_apply_eq_foldl`,
  `Distinguisher.sideAdds_perm`, `Distinguisher.sideAddPos_withSide`,
  `Distinguisher.sideAddAct_withSide`, `Distinguisher.sideAdds_perm_withSide`,
  `Distinguisher.sideAdds_perm_side` (the list does not read the side function),
  `Distinguisher.relay_step_eq_sideAdds_conj`;
  `Distinguisher.sideAdds_conj_pre_perm`, `Distinguisher.relay_step_eq_sideAdds_pre` (the
  additions conjugated before the step, `MultiRelayPreAdds`).

The boundary convention: with no slots (`m = 0`) there are no additions; when no relayed request is
in progress the fallback entry is the slot `0` entry `i`; when the program has made all `qS` side
reads the position is the last entry (`MultiRelay.pendSt_ns_eq_qS_congr`).
-/

namespace GordieHowe.Quantum

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [DecidableEq X] [DecidableEq Req]
  [DecidableEq Resp] [DecidableEq Req'] [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys]
  {n m : ℕ} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

/-- The stored answers of the block of slot `j`. -/
abbrev blockAns (z : RR) (j : ℕ) : ℕ → Option Resp' × (X × Y) := fun k =>
  MultiRelay.storeAt z.1.1.store (F.startAt n b Q (MultiRelay.recList z.1.1.record) j + k)

/-- The number of additions after each step: `qS`, none with no slots. -/
def sideNb (_k : Unit) : ℕ := if 0 < m then F.qS else 0

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited X]
  [Inhabited Req'] [AddGroup Y] [AddGroup Ys] in
theorem lt_of_sideNb {k : Unit} (i : Fin (sideNb (m := m) F k)) : 0 < m ∧ (i : ℕ) < F.qS := by
  have hi := i.isLt
  unfold sideNb at hi
  split_ifs at hi with hm
  · exact ⟨hm, hi⟩
  · exact absurd hi (Nat.not_lt_zero _)

/-- **The position of addition `i`**: the slot `j` of the relayed request in progress and the side
reads made before it, the last entry once all `qS` are made; the slot `0` entry `i` when no relayed
request is in progress. -/
def sideAddPos (i : ℕ) (hm : 0 < m) (hi : i < F.qS) (z : RR) : Fin m × Fin F.qS :=
  match F.curRel n b Q z.1.1.record z.1.1.time with
  | some (j, r, sub) =>
    if hj : j < m then
      (⟨j, hj⟩,
        ⟨min (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i).ns
          (F.qS - 1), by omega⟩)
    else (⟨0, hm⟩, ⟨i, hi⟩)
  | none => (⟨0, hm⟩, ⟨i, hi⟩)

/-- **The side read of addition `i`**: the point the program reads there, if it makes a side read
within its budget. -/
def sideAddAct (i : ℕ) (z : RR) : Option Xs :=
  match F.curRel n b Q z.1.1.record z.1.1.time with
  | some (j, r, sub) =>
    if hj : j < m then
      if (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i).ns < F.qS then
        match F.progAct r (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i)
        with
        | some (.inl (.inr x)) => some x
        | _ => none
      else none
    else none
  | none => none

/-- The side store with entry `p` set to `v`. -/
def setSide (z : RR) (p : Fin m × Fin F.qS) (v : Ys) : RR :=
  ((⟨z.1.1.inner, z.1.1.record, z.1.1.store,
    Function.update z.1.1.side p.1 (Function.update (z.1.1.side p.1) p.2 v), z.1.1.time⟩,
    z.1.2.1, z.1.2.2), z.2)

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited Req']
  [AddGroup Y] in
/-- **The state of the relayed request does not read the entry at its side reads**, below `qS`;
once all `qS` are made, the count does not read the last entry. -/
theorem pendSt_update (v : Fin F.qS → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y))
    (sub i : ℕ) (hq : 0 < F.qS) (y : Ys) :
    min (F.pendSt (F.vecSa (Function.update v
        ⟨min (F.pendSt (F.vecSa v) r g sub i).ns (F.qS - 1), by omega⟩ y)) r g sub i).ns
        (F.qS - 1) =
      min (F.pendSt (F.vecSa v) r g sub i).ns (F.qS - 1) ∧
    ((F.pendSt (F.vecSa v) r g sub i).ns < F.qS →
      F.pendSt (F.vecSa (Function.update v
        ⟨min (F.pendSt (F.vecSa v) r g sub i).ns (F.qS - 1), by omega⟩ y)) r g sub i =
      F.pendSt (F.vecSa v) r g sub i) ∧
    ((F.pendSt (F.vecSa v) r g sub i).ns < F.qS ↔
      (F.pendSt (F.vecSa (Function.update v
        ⟨min (F.pendSt (F.vecSa v) r g sub i).ns (F.qS - 1), by omega⟩ y)) r g sub i).ns <
        F.qS) := by
  set N := (F.pendSt (F.vecSa v) r g sub i).ns with hN
  have hle := F.ns_le_qS_pendSt (F.vecSa v) r g sub i
  by_cases hlt : N < F.qS
  · have hmin : min N (F.qS - 1) = N := by omega
    have heq : F.pendSt (F.vecSa (Function.update v ⟨min N (F.qS - 1), by omega⟩ y)) r g sub i =
        F.pendSt (F.vecSa v) r g sub i := by
      refine F.pendSt_congr_sa (N := N) (fun k hk x => ?_) r g sub i le_rfl
      exact F.vecSa_update_of_ne v (by omega) y (by omega) x
    rw [heq]
    exact ⟨rfl, fun _ => rfl, Iff.rfl⟩
  · have hq' : N = F.qS := by omega
    have hmin : min N (F.qS - 1) = F.qS - 1 := by omega
    have h2 :
        (F.pendSt (F.vecSa (Function.update v ⟨min N (F.qS - 1), by omega⟩ y)) r g sub i).ns =
          F.qS := by
      refine F.pendSt_ns_eq_qS_congr (fun k hk x => ?_) r g sub i hq'
      exact F.vecSa_update_of_ne v (by omega) y (by omega) x
    rw [h2]
    exact ⟨by rw [← hN, hq'], fun h => absurd h hlt, by rw [← hN, hq']⟩

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited X]
  [Inhabited Req'] [AddGroup Y] [AddGroup Ys] in
theorem setSide_record (z : RR) (p : Fin m × Fin F.qS) (v : Ys) :
    (setSide F z p v).1.1.record = z.1.1.record ∧ (setSide F z p v).1.1.time = z.1.1.time ∧
      (setSide F z p v).1.1.store = z.1.1.store :=
  ⟨rfl, rfl, rfl⟩

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited Req'] in
/-- **Writing the entry at the position keeps the position.** -/
theorem sideAddPos_set (i : ℕ) (hm : 0 < m) (hi : i < F.qS) (z : RR) (v : Ys) :
    sideAddPos F b Q i hm hi (setSide F z (sideAddPos F b Q i hm hi z) v) =
      sideAddPos F b Q i hm hi z := by
  unfold sideAddPos
  change (match F.curRel n b Q z.1.1.record z.1.1.time with
    | some (j, r, sub) => _ | none => _) = _
  rcases hc : F.curRel n b Q z.1.1.record z.1.1.time with _ | ⟨j, r, sub⟩
  · rfl
  · simp only
    split_ifs with hj
    · have h := (pendSt_update F (z.1.1.side ⟨j, hj⟩) r (blockAns F b Q z j) sub i
        (by omega) v).1
      refine Prod.ext rfl (Fin.ext ?_)
      simp only [setSide, Function.update_self]
      exact h
    · rfl

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited Req'] in
/-- **Writing the entry at the position keeps the point.** -/
theorem sideAddAct_set (i : ℕ) (hm : 0 < m) (hi : i < F.qS) (z : RR) (v : Ys) :
    sideAddAct F b Q i (setSide F z (sideAddPos F b Q i hm hi z) v) = sideAddAct F b Q i z := by
  unfold sideAddAct
  change (match F.curRel n b Q z.1.1.record z.1.1.time with
    | some (j, r, sub) => _ | none => _) = _
  rcases hc : F.curRel n b Q z.1.1.record z.1.1.time with _ | ⟨j, r, sub⟩
  · rfl
  · simp only
    by_cases hj : j < m
    · simp only [hj, ↓reduceDIte]
      obtain ⟨-, h2, h3⟩ :=
        pendSt_update F (z.1.1.side ⟨j, hj⟩) r (blockAns F b Q z j) sub i (by omega) v
      have hs : (setSide F z (sideAddPos F b Q i hm hi z) v).1.1.side ⟨j, hj⟩ =
          Function.update (z.1.1.side ⟨j, hj⟩)
            ⟨min (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i).ns
              (F.qS - 1), by omega⟩ v := by
        simp [setSide, sideAddPos, hc, hj]
      have hb : blockAns F b Q (setSide F z (sideAddPos F b Q i hm hi z) v) j =
          blockAns F b Q z j := rfl
      rw [hs, hb]
      by_cases hlt : (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i).ns <
          F.qS
      · simp only [hlt, ↓reduceIte, h2 hlt]
      · simp only [show ¬ _ < F.qS from fun h => hlt (h3.2 h), hlt, ↓reduceIte]
    · simp only [hj, ↓reduceDIte]

/-- **The part written by addition `i`**: the side store's entry at its position. -/
def sideAddLens (i : ℕ) (hm : 0 < m) (hi : i < F.qS) : RegLens RR Ys where
  get z := z.1.1.side (sideAddPos F b Q i hm hi z).1 (sideAddPos F b Q i hm hi z).2
  set z v := setSide F z (sideAddPos F b Q i hm hi z) v
  get_set z v := by
    rw [sideAddPos_set]
    simp [setSide]
  set_get z := by
    simp only [setSide, Function.update_eq_self]
  set_set z v v' := by
    rw [sideAddPos_set]
    simp [setSide]

/-- **The side additions after a sub-slot** as a list of additions: addition `i` adds the side
function's value at its side read (`sideAddAct`) to the side store's entry at its position
(`sideAddLens`). -/
def sideAdds : StepAdds RR Unit (Option Xs) Ys where
  nb := sideNb F
  L _ i := sideAddLens F b Q i (lt_of_sideNb F i).1 (lt_of_sideNb F i).2
  on _ i z := (sideAddAct F b Q i z).isSome
  x _ i z := sideAddAct F b Q i z
  on_set _ i z v := by
    change (sideAddAct F b Q i (setSide F z _ v)).isSome = _
    rw [sideAddAct_set]
  x_set _ i z v := sideAddAct_set F b Q i _ _ z v

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited Req'] in
/-- **Addition `i` at the side function is the `i`-th side addition** (`sideAddFun`). -/
theorem sideAdds_add_perm (i : Fin (sideNb F ())) (z : RR) :
    ((sideAdds F b Q).add (fun o => o.elim 0 F.side) () i).perm z = sideAddFun F b Q i true z := by
  obtain ⟨hm, hi⟩ := lt_of_sideNb F i
  rw [RegAdd.perm_apply]
  change setSide F z (sideAddPos F b Q i hm hi z)
      (z.1.1.side (sideAddPos F b Q i hm hi z).1 (sideAddPos F b Q i hm hi z).2 +
        (if (sideAddAct F b Q i z).isSome then (sideAddAct F b Q i z).elim 0 F.side else 0)) = _
  have hz : ∀ (a : Fin m) (c : Fin F.qS), setSide F z (a, c) (z.1.1.side a c) = z := fun a c => by
    simp [setSide]
  unfold sideAddFun sideAddPos sideAddAct
  rcases hc : F.curRel n b Q z.1.1.record z.1.1.time with _ | ⟨j, r, sub⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact hz _ _
  · simp only
    by_cases hj : j < m
    · simp only [hj, ↓reduceDIte]
      unfold MultiRelay.addVec
      by_cases hk : (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i).ns <
          F.qS
      · have hmin :
            min (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i).ns
              (F.qS - 1) =
            (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j) sub i).ns := by
          omega
        rcases hp : F.progAct r (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j)
            sub i) with _ | ((x | x) | r')
        · simp only [hk, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, add_zero]
          rw [hz]
          simp
        · simp only [hk, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, add_zero]
          rw [hz]
          simp
        · simp only [hk, ↓reduceIte, ↓reduceDIte, Option.isSome_some, Option.elim_some,
            setSide]
          congr 4
          ext1 ⟨k', hk'⟩
          simp only [hmin]
        · simp only [hk, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, add_zero]
          rw [hz]
          simp
      · simp only [hk, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, add_zero]
        rw [hz]
        rcases hp : F.progAct r (F.pendSt (F.vecSa (z.1.1.side ⟨j, hj⟩)) r (blockAns F b Q z j)
            sub i) with _ | ((x | x) | r') <;> simp
    · simp only [hj, ↓reduceDIte, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero]
      exact hz _ _

/-- **Permutations in sequence applied in order.** -/
theorem seqPerm_apply_eq_foldl {Z : Type*} (g : ℕ → Z → Z) :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm Z), (∀ (i : Fin n) z, f i z = g i z) →
      ∀ z, seqPerm n f z = (List.range n).foldl (fun z i => g i z) z
  | 0, _, _, _ => rfl
  | n + 1, f, hf, z => by
    change f (Fin.last n) (seqPerm n (fun i => f i.castSucc) z) = _
    rw [seqPerm_apply_eq_foldl g n _ (fun i z => hf i.castSucc z), List.range_succ,
      List.foldl_append, hf]
    rfl

/-- **The side additions at the side function are the side additions after a sub-slot.** -/
theorem sideAdds_perm :
    (sideAdds F b Q : StepAdds RR Unit (Option Xs) Ys).perm (fun o => o.elim 0 F.side) () =
      sideAddsPerm F b Q := by
  refine Equiv.ext fun z => ?_
  rw [sideAddsPerm, foldl_sideAddPerm_apply, Equiv.refl_apply]
  refine (seqPerm_apply_eq_foldl (fun i z => sideAddFun F b Q i true z)
    ((sideAdds F b Q : StepAdds RR Unit (Option Xs) Ys).nb ()) _
    (fun i z => sideAdds_add_perm F b Q i z) z).trans ?_
  change List.foldl _ z (List.range (sideNb (m := m) F ())) = _
  by_cases hm : 0 < m
  · rw [show sideNb (m := m) F () = F.qS from by simp [sideNb, hm]]
  · have hid : ∀ i (z : RR), sideAddFun F b Q i true z = z := fun i z => by
      have hc : F.curRel n b Q z.1.1.record z.1.1.time = none := by
        unfold MultiRelay.curRel
        have hl : (MultiRelay.recList z.1.1.record).length ≤ m := by
          unfold MultiRelay.recList
          rw [List.length_map]
          exact (List.takeWhile_sublist _).length_le.trans (List.length_finRange).le
        simp only [show ¬ 0 < (MultiRelay.recList z.1.1.record).length by omega, ↓reduceIte]
      simp only [sideAddFun, hc]
    have hfold :
        ∀ (L : List ℕ) (z : RR), L.foldl (fun z i => sideAddFun F b Q i true z) z = z :=
      fun L => by
        induction L with
        | nil => intro z; rfl
        | cons i L ih => intro z; rw [List.foldl_cons, hid, ih]
    rw [hfold, hfold]

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited Req'] in
/-- The position of an addition does not read the side function. -/
theorem sideAddPos_withSide (sf : Xs → Ys) (i : ℕ) (hm : 0 < m) (hi : i < F.qS) (z : RR) :
    sideAddPos (F.withSide sf) b Q i hm hi z = sideAddPos F b Q i hm hi z := by
  unfold sideAddPos
  simp only [MultiRelay.pendSt_withSide]
  rfl

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited Req'] in
/-- The point of an addition does not read the side function. -/
theorem sideAddAct_withSide (sf : Xs → Ys) (i : ℕ) (z : RR) :
    sideAddAct (F.withSide sf) b Q i z = sideAddAct F b Q i z := by
  unfold sideAddAct
  simp only [MultiRelay.pendSt_withSide]
  rfl

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Req'] [Inhabited Req'] in
/-- **The list of additions does not read the side function.** -/
theorem sideAdds_perm_withSide (sf : Xs → Ys) (ω : Option Xs → Ys) :
    ((sideAdds (F.withSide sf) b Q).perm ω () : Equiv.Perm RR) = (sideAdds F b Q).perm ω () := by
  change seqPerm _ (fun i => ((sideAdds (F.withSide sf) b Q).add ω () i).perm) =
    seqPerm _ (fun i => ((sideAdds F b Q).add ω () i).perm)
  congr 1
  funext i
  obtain ⟨hm, hi⟩ := lt_of_sideNb (k := ()) F i
  refine Equiv.ext fun (z : RR) => ?_
  change setSide (F.withSide sf) z (sideAddPos (F.withSide sf) b Q i hm hi z)
      (z.1.1.side (sideAddPos (F.withSide sf) b Q i hm hi z).1
        (sideAddPos (F.withSide sf) b Q i hm hi z).2 +
        (if (sideAddAct (F.withSide sf) b Q i z).isSome then ω (sideAddAct (F.withSide sf) b Q i z)
          else 0)) =
    setSide F z (sideAddPos F b Q i hm hi z)
      (z.1.1.side (sideAddPos F b Q i hm hi z).1 (sideAddPos F b Q i hm hi z).2 +
        (if (sideAddAct F b Q i z).isSome then ω (sideAddAct F b Q i z) else 0))
  have e1 := sideAddPos_withSide F b Q sf i hm hi z
  have e2 := sideAddAct_withSide F b Q sf i z
  simp only [e1, e2]
  rfl

/-- **The list of additions at a side function is the side additions of the relay with that side
function.** -/
theorem sideAdds_perm_side (sf : Xs → Ys) :
    (sideAdds F b Q : StepAdds RR Unit (Option Xs) Ys).perm (fun o => o.elim 0 sf) () =
      (sideAddsPerm (F.withSide sf) b Q : Equiv.Perm RR) :=
  (sideAdds_perm_withSide F b Q sf _).symm.trans (sideAdds_perm (F.withSide sf) b Q)

/-- **The side additions conjugated before the step, as a list of additions** (`preAdds`). -/
theorem sideAdds_conj_pre_perm :
    ((sideAdds F b Q : StepAdds RR Unit (Option Xs) Ys).conj (prePerm F b Q).symm).perm
      (fun o => o.elim 0 F.side) () = preAdds F b Q := by
  rw [← StepAdds.perm_conj, sideAdds_perm]
  rfl

variable [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys] [DecidableEq Ys]
  (D : Distinguisher W X Y Req Resp n m)

/-- **The relayed step is the step at the zero side function followed by the side additions
conjugated by the record and the set-up** (module docstring), for a relay without trailing side
reads, at every step `k > 0`. The side additions occur mid-step and are moved after the step by
conjugation with the rest of the step. -/
theorem relay_step_eq_sideAdds_conj (hT : F.NoTrailingSides) (k : Fin (relaySlots n m F + 1))
    (hk : (k : ℕ) ≠ 0) :
    (D.relay F b Q).step k = ((D.relay (F.withSide 0) b Q).step k).trans
      (permOp (((sideAdds F b Q : StepAdds RR Unit (Option Xs) Ys).conj
        ((recordPerm F b Q D.kind).trans (setupPerm F b Q))).perm
        (fun o => o.elim 0 F.side) ())) := by
  rw [D.relay_step_eq_withSide_zero F b Q hT k hk, ← StepAdds.perm_conj, sideAdds_perm]

/-- **The relayed step is the side additions conjugated before the step, as a list of additions,
then the step at the zero side function**, at every step `k > 0`. They keep every register but the
side store (`preAdds_keeps`) and the kind (`kind_preAdds`). -/
theorem relay_step_eq_sideAdds_pre (k : Fin (relaySlots n m F + 1)) (hk : (k : ℕ) ≠ 0) :
    (D.relay F b Q).step k = (permOp (((sideAdds F b Q : StepAdds RR Unit (Option Xs) Ys).conj
      (prePerm F b Q).symm).perm (fun o => o.elim 0 F.side) ())).trans
        ((D.relay (F.withSide 0) b Q).step k) := by
  rw [sideAdds_conj_pre_perm, D.relay_step_eq_pre_withSide_zero F b Q k hk]

end Distinguisher

end GordieHowe.Quantum
