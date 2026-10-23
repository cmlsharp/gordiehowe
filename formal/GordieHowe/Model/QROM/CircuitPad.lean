-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.CircuitCount
public import GordieHowe.Model.QROM.CoherentBridgeCore

@[expose] public section

/-!
# Padded queries of a compiled circuit act as the identity in the real run

`compiledQueryCount` (`GordieHowe/Model/QROM/CircuitCount.lean`) shows that off the records `C k` the queries
of the pure algorithm of a compiled circuit are padded *in the simulated run* (`SimFrame.pad`):
there the compiled sub-circuit queries the clean reprogramming ancilla, whose answer register is
in the uniform superposition. This file proves the same in the real run, against any oracle: the
part of the run before query `k` outside `C k` is fixed by every oracle permutation
(`compiled_realPad`). The per-branch hybrid of `GordieHowe/Model/Quantum/O2H/CountOn.lean` uses it: two oracles
act alike on the padded branches.

- `RealFrame`: the frame of a query on the real registers, a support and an invariance under the
  frame shifts (`frameShift`), as `SimFrame` on the simulated registers.
- `RealFrame.map_queryPerm`: an oracle permutation keeps the frame. On the branches with the
  reprogramming flag set the query register holds the ancilla and the frame shifts its answer, so
  the part there does not depend on the answer register and the oracle fixes it; on the others
  the ancilla is clean and the oracle does not touch it.
- `RealFrame.pad`: off the records, on the supports, the oracle fixes the part of the state.
- `compiled_realStage`: the real run before query `k` is supported in `compiledG k` and in the
  frame of query `k` (the steps carry it by `stepAt_compiled_frame`, the queries by
  `map_queryPerm`).
-/

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-! ### Oracle permutations on one query register -/

section OnePair

variable {W : Type} [Fintype W]

/-- **An oracle permutation fixes a vector that does not depend on the answer register.** -/
theorem permOp_queryPerm_eq_self_of_ansConst (H : Bits m → BitStr I J)
    {v : QState (QueryReg W 1 (Bits m) (BitStr I J))} (hv : ∀ r u, v (withAns r u) = v r) :
    permOp (queryPerm H) v = v := by
  ext r
  rw [permOp_apply]
  have : (queryPerm H).symm r = withAns r (qAns r - H (qIn r)) := by
    rw [Equiv.symm_apply_eq, queryPerm_apply]
    obtain ⟨w, q⟩ := r
    simp only [withAns, Prod.mk.injEq, true_and]
    funext j
    rw [Subsingleton.elim j 0]
    simp
  rw [this, hv]

/-- **An oracle permutation keeps a support that depends only on the work register and the query
input.** -/
theorem Supported.permOp_queryPerm (H : Bits m → BitStr I J)
    {S : Set (QueryReg W 1 (Bits m) (BitStr I J))}
    (hS : ∀ r' r : QueryReg W 1 (Bits m) (BitStr I J), r'.1 = r.1 → qIn r' = qIn r →
      (r' ∈ S ↔ r ∈ S))
    {v : QState (QueryReg W 1 (Bits m) (BitStr I J))} (hv : Supported S v) :
    Supported S (permOp (queryPerm H) v) :=
  hv.permOp fun r hr => (hS (queryPerm H r) r rfl rfl).2 hr

/-- **An oracle permutation keeps invariance under a permutation of the work register.** -/
theorem permOp_queryPerm_apply_workPerm (H : Bits m → BitStr I J) (τ : Equiv.Perm W)
    {v : QState (QueryReg W 1 (Bits m) (BitStr I J))} (hv : ∀ r, v (τ r.1, r.2) = v r)
    (r : QueryReg W 1 (Bits m) (BitStr I J)) :
    permOp (queryPerm H) v (τ r.1, r.2) = permOp (queryPerm H) v r := by
  rw [permOp_apply, permOp_apply]
  exact hv ((queryPerm H).symm r)

end OnePair

/-! ### The frame of a query in the real run -/

section RealFrame

variable {V O' O : Type} [Fintype V] [DecidableEq V]
  (c : ReprogrammedCircuit V (Bits m) (BitStr I J))
  (x₀ : Bits m) (ρ : MState (QueryReg V 1 (Bits m) (BitStr I J)))
  (out : V × (Bits m × BitStr I J × Bool) → O') (g : Option O' → O)

variable (ass : V → List (Assignment (Bits m) (BitStr I J)))

/-- **The frame of a query, on the real run**: supported on the frame's support and invariant
under the frame shifts (on the work register and query pair of the circuit, read through the
pure algorithm's registers). -/
structure RealFrame
    (v : QState (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
      (BitStr I J))) : Prop where
  supp : Supported (ι := QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
    (BitStr I J)) {r | innerOf r ∈ frameSupp ass x₀} v
  inv : ∀ cy r, v (cLift c x₀ ρ out g (frameShift ass cy) r) = v r

/-- **An oracle permutation keeps the frame of the query** (module docstring). -/
theorem RealFrame.map_queryPerm (H : Bits m → BitStr I J)
    {v : QState (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
      (BitStr I J))} (hv : RealFrame c x₀ ρ out g ass v) :
    RealFrame c x₀ ρ out g ass (permOp (queryPerm H) v) := by
  classical
  set Fs : Set (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
    (BitStr I J)) := {r | r.1.1.1.2.2.2 = true}
  set U : Set (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
    (BitStr I J)) := {r | innerOf r ∈ cleanUnassigned ass x₀}
  -- the flagged part does not depend on the answer register
  have hA : ∀ r u, mask Fs v (withAns r u) = mask Fs v r := by
    intro r u
    by_cases hr : r ∈ Fs
    · rw [mask_apply_of_mem _ hr, mask_apply_of_mem _ (show withAns r u ∈ Fs from hr)]
      by_cases ha : (lastAssign (ass r.1.1.1.1) r.1.1.1.2.1).isSome
      · have h := hv.inv (u - qAns r) r
        rw [cLift_congr c x₀ ρ out g (frameShift_of_swapped ass _ (p := innerOf r) hr ha)] at h
        rwa [cLift_qShift, add_sub_cancel] at h
      · have h1 : v r = 0 := hv.supp r fun h => ha (of_mem_frameSupp_of_flag_true ass h hr)
        have h2 : v (withAns r u) = 0 := hv.supp _ fun h =>
          ha (of_mem_frameSupp_of_flag_true ass h hr)
        rw [h1, h2]
    · rw [mask_apply_of_notMem _ hr, mask_apply_of_notMem _ (show withAns r u ∉ Fs from hr)]
  -- the unflagged part lies on `U`
  have hU : Supported U (mask Fsᶜ v) := by
    intro r hr
    by_cases hf : r ∈ Fs
    · exact mask_apply_of_notMem _ fun h => h hf
    · rw [mask_apply_of_mem _ hf]
      refine hv.supp r fun hs => hr ?_
      have hf' : (innerOf r).1.2.2.2 = false := Bool.eq_false_iff.mpr hf
      obtain ⟨h1, h2⟩ := of_mem_frameSupp_of_flag_false ass hs hf'
      exact ⟨hf', h1, h2⟩
  have hUshift : ∀ cy r, r ∈ U →
      cLift c x₀ ρ out g (frameShift ass cy) r = cLift c x₀ ρ out g (ancShift cy) r :=
    fun cy r hr => cLift_congr c x₀ ρ out g (frameShift_of_unassigned ass cy (p := innerOf r)
      hr.1 hr.2.1)
  have hUmem : ∀ cy r, (cLift c x₀ ρ out g (ancShift cy) r ∈ U ↔ r ∈ U) := fun cy r => Iff.rfl
  -- the unflagged part is invariant under the ancilla shift
  have hUinv : ∀ cy r, mask Fsᶜ v (ancShiftW c x₀ ρ out g cy r.1, r.2) = mask Fsᶜ v r := by
    intro cy r
    have hlift : ((ancShiftW c x₀ ρ out g cy r.1, r.2) :
        QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m) (BitStr I J)) =
        cLift c x₀ ρ out g (ancShift cy) r := rfl
    rw [hlift]
    by_cases hr : r ∈ U
    · have hf : r ∉ Fs := fun h => by
        have h1 : (innerOf r).1.2.2.2 = false := hr.1
        have h2 : (innerOf r).1.2.2.2 = true := h
        rw [h1] at h2
        exact Bool.false_ne_true h2
      rw [mask_apply_of_mem _ (show cLift c x₀ ρ out g (ancShift cy) r ∈ Fsᶜ from hf),
        mask_apply_of_mem _ (show r ∈ Fsᶜ from hf), ← hUshift cy r hr]
      exact hv.inv cy r
    · rw [hU r hr, hU _ fun h => hr ((hUmem cy r).1 h)]
  set y := permOp (queryPerm H) (mask Fsᶜ v)
  have hyU : Supported U y := Supported.permOp_queryPerm H (fun r' r h1 h2 => by
    simp only [U, Set.mem_ofPred_eq, innerOf, cleanUnassigned, CleanSupp]
    rw [h1, show (r'.2 0).1 = (r.2 0).1 from h2]) hU
  have hyinv : ∀ cy r, y (ancShiftW c x₀ ρ out g cy r.1, r.2) = y r :=
    fun cy r => permOp_queryPerm_apply_workPerm H (ancShiftW c x₀ ρ out g cy) (hUinv cy) r
  have hsplit : permOp (queryPerm H) v = mask Fs v + y := by
    conv_lhs => rw [← mask_add_mask_compl Fs v]
    rw [map_add, permOp_queryPerm_eq_self_of_ansConst H hA]
  rw [hsplit]
  refine ⟨fun r hr => ?_, fun cy r => ?_⟩
  · have hm : mask Fs v r = 0 := by
      by_cases hf : r ∈ Fs
      · rw [mask_apply_of_mem _ hf]
        exact hv.supp r hr
      · exact mask_apply_of_notMem _ hf
    rw [PiLp.add_apply, hm, zero_add]
    exact hyU r fun h => hr (mem_frameSupp_of_unassigned ass h.1 h.2.1 h.2.2)
  · rw [PiLp.add_apply, PiLp.add_apply]
    congr 1
    · have hflag : cLift c x₀ ρ out g (frameShift ass cy) r ∈ Fs ↔ r ∈ Fs :=
        Iff.of_eq (congrArg (· = true) (flag_frameShift ass cy (innerOf r)))
      by_cases hr : r ∈ Fs
      · rw [mask_apply_of_mem _ (hflag.2 hr), mask_apply_of_mem _ hr]
        exact hv.inv cy r
      · rw [mask_apply_of_notMem _ (fun h => hr (hflag.1 h)), mask_apply_of_notMem _ hr]
    · by_cases hr : r ∈ U
      · rw [hUshift cy r hr]
        exact hyinv cy r
      · have hr' : cLift c x₀ ρ out g (frameShift ass cy) r ∉ U :=
          fun h => hr (mem_cleanUnassigned_of_frameShift ass cy h)
        exact (hyU _ hr').trans (hyU r hr).symm

/-- **Off the records the query is padded in the real run**: on the branches whose work register
is in `G` but outside the record `C`, every input is assigned, the frame shifts the query answer,
and every oracle permutation fixes the part of the state there. -/
theorem RealFrame.pad (H : Bits m → BitStr I J)
    {v : QState (QueryReg (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).W 1 (Bits m)
      (BitStr I J))} (hv : RealFrame c x₀ ρ out g ass v) {Cs Gs : Set V}
    (hG : Supported {r | r.1.1.1.1 ∈ Gs} v)
    (hpad : ∀ w ∈ Gs, w ∉ Cs → ∀ x, (lastAssign (ass w) x).isSome) :
    permOp (queryPerm H) (mask {r | r.1.1.1.1 ∈ Cs}ᶜ v) = mask {r | r.1.1.1.1 ∈ Cs}ᶜ v := by
  refine permOp_queryPerm_eq_self_of_ansConst H fun r u => ?_
  by_cases hC : r.1.1.1.1 ∈ Cs
  · rw [mask_apply_of_notMem _ (show r ∉ {r | r.1.1.1.1 ∈ Cs}ᶜ from fun h => h hC),
      mask_apply_of_notMem _ (show withAns r u ∉ {r | r.1.1.1.1 ∈ Cs}ᶜ from fun h => h hC)]
  · rw [mask_apply_of_mem _ (show r ∈ {r | r.1.1.1.1 ∈ Cs}ᶜ from hC),
      mask_apply_of_mem _ (show withAns r u ∈ {r | r.1.1.1.1 ∈ Cs}ᶜ from hC)]
    by_cases hGr : r.1.1.1.1 ∈ Gs
    · have h := hv.inv (u - qAns r) r
      rw [cLift_congr c x₀ ρ out g (frameShift_of_padded ass _ (p := innerOf r) (hpad _ hGr hC))] at h
      rwa [cLift_qShift, add_sub_cancel] at h
    · exact (hG (withAns r u) hGr).trans (hG r hGr).symm

end RealFrame

/-! ### The real run of the pure algorithm of a compiled circuit -/

section RealRun

variable {V O' O : Type} [Fintype V] [DecidableEq V]
  {c : ReprogrammedCircuit V (Bits m) (BitStr I J)}
  {x₀ : Bits m} {ρ : MState (QueryReg V 1 (Bits m) (BitStr I J))}
  {out : V × (Bits m × BitStr I J × Bool) → O'} {g : Option O' → O}

/-- **The real run before query `k`** is supported in `compiledG k` and, before the last query,
in the frame of query `k`, against every oracle `H`. -/
theorem compiled_realStage {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries)) (hP : ∀ p, ρ.mat p p ≠ 0 → p.1 ∈ P)
    (H : Bits m → BitStr I J) :
    ∀ k < c.queries,
      Supported {r | r.1 ∈ compiledG c x₀ ρ out g G k}
        (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stage
          (queryPerm H) () k) ∧
      RealFrame c x₀ ρ out g (c.assAt k)
        (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stage
          (queryPerm H) () k) := by
  have := compiled_nonempty c x₀ ρ out
  intro k
  induction k with
  | zero =>
    intro h0
    obtain ⟨hIS, hII⟩ := compiled_init_props (g := g) hP
    refine ⟨compiled_init hv hP, ?_⟩
    have h := ReprogrammedCircuit.stepAt_compiled_frame c x₀ ρ out g hv (k := 0) h0
      (v := (ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).init)
      (hIS.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩) hII
    rw [ReprogrammedCircuit.frameSuppAt_eq x₀ c h0] at h
    refine ⟨h.1, fun cy r => ?_⟩
    have := h.2 cy r
    rwa [ReprogrammedCircuit.frameAt_eq c h0] at this
  | succ k ih =>
    intro hk1
    obtain ⟨hG, hF⟩ := ih (by omega)
    have hk : k < c.queries := by omega
    set u := permOp (queryPerm H)
      (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stage (queryPerm H) () k)
    have hGu : Supported {r | r.1 ∈ compiledG c x₀ ρ out g G k} u :=
      hG.permOp fun r hr => hr
    have hFu := hF.map_queryPerm c x₀ ρ out g (c.assAt k) H
    refine ⟨compiled_stepG hv hk hGu, ?_⟩
    have hinv' : ∀ cy r, u (liftW (V' := (ReprogrammedCircuit.compiledAlg c x₀ ρ out).V)
        (H := (ReprogrammedCircuit.compiledAlg c x₀ ρ out).HaltAnc) (c.frameIn (k + 1) cy) r) =
        u r := fun cy r => by
      change u (cLift c x₀ ρ out g (c.frameAt k cy) r) = u r
      rw [ReprogrammedCircuit.frameAt_eq c hk]
      exact hFu.inv cy r
    have h := ReprogrammedCircuit.stepAt_compiled_frame c x₀ ρ out g hv (k := k + 1) hk1
      (v := u) (fun r hr => by
        by_cases h1 : innerOf r ∈ frameSupp (c.assAt k) x₀
        · refine hGu r fun h' => hr ⟨?_, h'.2.1, h'.2.2 hk⟩
          change innerOf r ∈ ReprogrammedCircuit.frameSuppAt x₀ c k
          rw [ReprogrammedCircuit.frameSuppAt_eq x₀ c hk]
          exact h1
        · exact hFu.supp r h1) hinv'
    rw [ReprogrammedCircuit.frameSuppAt_eq x₀ c hk1] at h
    refine ⟨h.1, fun cy r => ?_⟩
    have := h.2 cy r
    rwa [ReprogrammedCircuit.frameAt_eq c hk1] at this

/-- **Padded queries act as the identity in the real run**: before query `k`, the part of the
real run against `H` outside the record `C k` is fixed by every oracle permutation. -/
theorem compiled_realPad {C G : ℕ → Set V} {P : Set V}
    (hv : ReprogrammedCircuit.Valid C G c 0 P (G c.queries)) (hP : ∀ p, ρ.mat p p ≠ 0 → p.1 ∈ P)
    (H H' : Bits m → BitStr I J) {k : ℕ}
    (hk : k < (ReprogrammedCircuit.compiledAlg c x₀ ρ out).depth) :
    permOp (queryPerm H') (mask {r | r.1 ∈ compiledC c x₀ ρ out g C k}ᶜ
        (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stage
          (queryPerm H) () k)) =
      mask {r | r.1 ∈ compiledC c x₀ ρ out g C k}ᶜ
        (((ReprogrammedCircuit.compiledQueryAlg c x₀ ρ out g).toOracleAlg ∅).stage
          (queryPerm H) () k) := by
  rw [depth_eq] at hk
  obtain ⟨hG, hF⟩ := compiled_realStage hv hP H k hk
  refine hF.pad c x₀ ρ out g (c.assAt k) H' (Cs := C k) (Gs := G k)
    (fun r hr => hG r fun h => hr h.1) fun w hw hC => ?_
  exact hv.padAt k hk w (by rwa [zero_add]) (by rwa [zero_add])

end RealRun

end GordieHowe.QROM
