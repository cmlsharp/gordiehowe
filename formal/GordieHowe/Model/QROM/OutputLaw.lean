-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.OracleSimulation

@[expose] public section

/-!
# The output of `Sim*(A)` has the law of the output of `A` against a random oracle

**Zha19 Lemma 4** (Zhandry, "How to Record Quantum Queries", ePrint 2018/276, p. 14): "CStO and
StO are perfectly indistinguishable … for any adversary A, we have Pr[A^CStO() = 1] =
Pr[A^StO() = 1]"; restated as **CMS19 Lemma 3.3** (p. 17): "Tr_D(|Sim*(A)⟩⟨Sim*(A)|) =
(1/(2^n)^(2^m)) ∑_h A_h A_h*", i.e. `|Sim*(A)⟩` purifies the state of `A` against a uniformly random
oracle. The consequence used here, for the measured output:

- `simLaw_out`: for a `t`-query algorithm `A` and a set `S` of outputs, the probability that the
  measured output of `Sim*(A)` (CMS19's simulation with the fixed-bound compressed phase oracle,
  `simLaw`) lies in `S` equals the probability that `A^h` outputs into `S` for a uniformly random
  `h` (`QueryAlg.realLaw`). Measuring the database register after the output changes nothing in
  the output's law.
- `simLaw_eq_add_diff`: `simLaw` is additive along a split of an event (it is a sum of Born weights).

The proof writes both sides in the Fourier-basis run `fourStage A t` (`GordieHowe/Model/QROM/Purified.lean`,
`GordieHowe/Model/QROM/FourierCompression.lean`): the real side is `fourier (fourStage A t)` (Zha19 Lemma 2), the
simulated side `compress (fourStage A t)`, read through the entry kernel `fk` on every input
(`dbFun`, `norm_goodSim_compress` at tuples with no queries). Both `fourier` and `dbFun` act on the
oracle register by matrices with orthonormal columns and leave the adversary's register, from
which the output is read, unchanged; so both preserve the norm of the projection onto an output
event.
-/

open GordieHowe.Quantum

namespace GordieHowe.QROM

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B : Type} [Fintype B] (e : BitStr I J ≃ B)

section OutputLaw

variable {O : Type} {t : ℕ} (A : QueryAlg (Bits m) (BitStr I J) t O)

variable (I J) in
/-- The basis states of the purified registers whose adversary register gives an output in
`S`. -/
def outIn (W : Type) (out : W → O) (L : Type) (S : Set O) :
    Set (QueryReg W 1 (Bits m) (BitStr I J) × L) :=
  {b | out b.1.1 ∈ S}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem mem_outIn {W : Type} {out : W → O} {L : Type} {S : Set O}
    {b : QueryReg W 1 (Bits m) (BitStr I J) × L} : b ∈ outIn I J W out L S ↔ out b.1.1 ∈ S :=
  Iff.rfl

variable {A}

/-- A matrix that leaves the adversary's register unchanged intertwines the projections onto an
output event. -/
theorem kernelMap_idLeft_mask_outIn {W : Type} [Fintype W] [DecidableEq W] {out : W → O}
    {L L' : Type} [Fintype L] [Fintype L'] {S : Set O}
    (K : QueryReg W 1 (Bits m) (BitStr I J) → L' → L → ℂ)
    (v : QState (QueryReg W 1 (Bits m) (BitStr I J) × L)) :
    kernelMap (idLeft K) (mask (outIn I J W out L S) v) =
      mask (outIn I J W out L' S) (kernelMap (idLeft K) v) :=
  kernelMap_mask (fun a j hK => by
    have h1 : a.1 = j.1 := by
      by_contra hne
      exact hK (by simp [idLeft, hne])
    rw [mem_outIn, mem_outIn, h1]) v

/-- `dbFun` is an isometry: the entry kernel `fk` has orthonormal columns on every input. -/
theorem norm_dbFun {W : Type} [Fintype W] [DecidableEq W] [DecidableEq B]
    (v : QState (PurReg W I J m)) : ‖dbFun e W v‖ = ‖v‖ :=
  norm_kernelMap (idLeft_orthonormal (S := fun _ => Set.univ) fun _ F _ F' _ =>
    piKernel_orthonormal (fun _ y y' => fk_orthonormal e y y') F F')
    fun _ hb => absurd (Set.mem_univ _) hb

variable (A)

variable (B) in
/-- The tuple with no queries and the output of `A` at the work register state `w`. -/
def noQueryTuple (w : A.W) : BaseGame.Tuple (Bits m) B O 0 :=
  ⟨Fin.elim0, Fin.elim0, A.out w⟩

/-- **The simulated output law is the real output law** (Zha19 Lemma 4, p. 14; CMS19 Lemma 3.3,
p. 17, after measuring the output register): for every set `S` of outputs, the probability that
the measured output of `Sim*(A)` lies in `S` is the probability that `A^h` outputs into `S` for a
uniformly random oracle `h`. -/
theorem simLaw_out [DecidableEq B] (S : Set O) :
    simLaw e A {p | p.1 ∈ S} = (A.realLaw e).toOuterMeasure {p | p.out ∈ S} := by
  have hsim : simLaw e A {p | p.1 ∈ S} =
      ‖mask (goodSim e O (noQueryTuple B A) {o | o.out ∈ S}) (simState e A)‖ₑ ^ 2 := by
    rw [simLaw, MeasureTheory.OuterMeasure.map_apply, bornWeight_apply]
    congr 3
    ext b
    simp [goodSim, noQueryTuple, BaseGame.Tuple.InDB]
  have hgood : goodD (I := I) (J := J) O (noQueryTuple B A) {o | o.out ∈ S} =
      outIn I J A.W A.out _ S := by
    ext b
    simp [goodD, noQueryTuple, outIn]
  have hreal : (A.realLaw e).toOuterMeasure {p | p.out ∈ S} =
      ‖mask (outIn I J A.W A.out _ S) (purStage A t)‖ₑ ^ 2 := by
    rw [realLaw_eq_bornWeight, bornWeight_apply]
    rfl
  rw [hsim, hreal, simState_eq_compress, ← ofReal_norm, ← ofReal_norm,
    norm_goodSim_compress e (noQueryTuple B A) _ (supported_fourStage A t), hgood, dbFun,
    ← kernelMap_idLeft_mask_outIn, ← dbFun, norm_dbFun, ← fourier_fourStage, fourier,
    ← kernelMap_idLeft_mask_outIn, ← fourier, norm_fourier]

omit [Fintype B] in
/-- **Reading the output through `g` maps the outcome of `Sim*(A)`**: the run is unchanged. -/
theorem simLaw_mapOut {O' : Type} (g : O → O') (S : Set (O' × DB (Bits m) B)) :
    simLaw e (A.mapOut g) S = simLaw e A {p | (g p.1, p.2) ∈ S} :=
  rfl

omit [Fintype B] in
/-- **`simLaw` splits along an event**: `Pr[S] = Pr[S ∩ T] + Pr[S \ T]` for the outcome of
`Sim*(A)`. -/
theorem simLaw_eq_add_diff (S T : Set (O × DB (Bits m) B)) :
    simLaw e A S = simLaw e A (S ∩ T) + simLaw e A (S \ T) := by
  simp only [simLaw, MeasureTheory.OuterMeasure.map_apply, bornWeight_apply_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : (A.out b.1.1, slotsDB e b.2) ∈ S <;> by_cases h2 : (A.out b.1.1, slotsDB e b.2) ∈ T <;>
    simp [Set.indicator, h1, h2]

end OutputLaw

end GordieHowe.QROM
