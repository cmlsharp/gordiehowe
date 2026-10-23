-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Bridge

@[expose] public section

/-!
# The coherent bridge: the purified run without the final measurement

`Alg.toQueryAlgCoh` purifies the halting completion of a core algorithm
(`GordieHowe/Model/Quantum/Pure/Bridge.lean`) without a final computational-basis measurement: the output is
read from the system register, and the other registers stay coherent. It is the run of the
paper's database extractor (`prot:bcs-db-extractor`), which measures only what it reads.

- `MixedAlg.dilateCoh`, `Alg.toQueryAlgCoh`, `Alg.haltOutCoh`: the definitions.
- `Alg.outLaw_toQueryAlgCoh`, `Alg.realLaw_toQueryAlgCoh`: the coherent form has the output law of
  the core algorithm.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

end GordieHowe.Quantum

namespace GordieHowe.Quantum

/-! ### The dilation without the final measurement -/

namespace MixedAlg

variable {Z ι R M : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] {d : ℕ}
  (G : MixedAlg Z ι d R M) [Nonempty R] [Nonempty M]

/-- **The dilation of `G` without the final measurement**: the purification of the run of `G`
(`dilStep`), whose output bit reads the measurement register, which stays in its initial basis
state. Measuring its system register gives the outcome law of `G`'s final state in the computational
basis. -/
noncomputable def dilateCoh (E : Z → Set M) : OracleAlg Z (ι × Anc ι d R M) d where
  init := G.dilInit
  norm_init := G.norm_dilInit
  step z k := G.dilStep z k
  accept z := {p | p.2.2.2 ∈ E z}

/-- The stages of the dilation without the final measurement are the run of the dilation. -/
theorem stage_dilateCoh (E : Z → Set M) (π : Equiv.Perm ι) (z : Z) {k : ℕ} (hk : k ≤ d) :
    (G.dilateCoh E).stage (liftPerm π) z k = G.dilRun π z k := by
  refine hybrid_congr_le _ _ k fun i hi => ?_
  rw [OracleAlg.stepAt_of_lt _ (by omega)]
  rfl

end MixedAlg

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (A : Alg X Y O)

/-- The output read from the system register of the halting completion: `none` on halted
states. -/
def haltOutCoh (w : (A.V × Bool) × A.HaltAnc) : Option O :=
  if w.1.2 then none else some (A.out w.1.1)

/-- **The coherent pure serial unitary algorithm of a core algorithm**: the dilation of the halting
completion without a final measurement (`MixedAlg.dilateCoh`), relabelled by `haltRelabel`. Its
output is read from the system register (`haltOutCoh`), so the run leaves the registers it does not
read unmeasured. -/
noncomputable abbrev toQueryAlgCoh : QueryAlg X Y A.depth (Option O) :=
  haveI := A.init.nonempty
  let D := (A.halting.dilateCoh fun _ => ∅).relabel (haltRelabel A.V A.HaltAnc X Y)
  { W := (A.V × Bool) × A.HaltAnc
    instDecidableEq := Classical.decEq _
    init := D.init ()
    norm_init := D.norm_init ()
    step := D.step ()
    out := A.haltOutCoh }

/-- The ancilla of the dilation is finite, assembled from its factors (the default instance
search exceeds its size limit on the products built over it). -/
instance instFintypeHaltAnc : Fintype A.HaltAnc :=
  instFintypeProd _ _

/-- The work register of `toQueryAlgCoh` is finite, assembled from its factors. -/
instance instFintypeToQueryAlgCohW : Fintype A.toQueryAlgCoh.W :=
  instFintypeProd (A.V × Bool) A.HaltAnc

/-- The run of the dilation reads, on its system register, the computational-basis law of the
final state of a mixed algorithm whose measurement is the computational basis. -/
theorem _root_.GordieHowe.Quantum.MixedAlg.born_dilRun_fst {Z ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype R] {d : ℕ} (G : MixedAlg Z ι d R ι) [Nonempty R] [Nonempty ι]
    (hmeas : ∀ z, G.meas z = KrausChannel.basis ι) (π : Equiv.Perm ι) (z : Z) :
    (born (G.dilRun π z d) (G.norm_dilRun π z d)).map Prod.fst = G.outLaw π z := by
  ext i
  rw [born_map_apply, MixedAlg.outLaw, KrausChannel.outcomeLaw_apply, hmeas,
    KrausChannel.outcomeProb_basis]
  congr 1
  have h := probIn_reduceMState (G.dilRun π z d) (G.norm_dilRun π z d) {i}
  have hm : (reduceMState (G.dilRun π z d) (G.norm_dilRun π z d)).mat = (G.final π z).mat := by
    rw [reduceMState_mat]
    exact (G.dilRun_spec π z d).2
  rw [MState.probIn, hm] at h
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  rw [h]
  rfl

/-- **The coherent pure algorithm has the output law of the core algorithm** under every oracle. -/
theorem outLaw_toQueryAlgCoh [AddGroup Y] (f : X → Y) : A.toQueryAlgCoh.outLaw f = A.outLaw f := by
  have := A.init.nonempty
  have hfin : A.toQueryAlgCoh.final f = relabel (haltRelabel A.V A.HaltAnc X Y)
      (A.halting.dilRun (MixedAlg.liftPerm (queryPerm f)) () A.depth) := by
    rw [QueryAlg.final, OracleAlg.final]
    refine (OracleAlg.stage_relabel (A.halting.dilateCoh fun _ => ∅)
      (haltRelabel A.V A.HaltAnc X Y) (π := MixedAlg.liftPerm (MixedAlg.liftPerm (queryPerm f)))
      (π' := queryPerm f) (fun _ => rfl) () A.depth).trans ?_
    congr 1
    refine hybrid_congr_le _ _ A.depth fun i hi => ?_
    rw [OracleAlg.stepAt_of_lt _ (by omega)]
    rfl
  rw [QueryAlg.outLaw]
  simp_rw [hfin]
  rw [born_relabel, PMF.map_comp, ← A.outLaw_halting, ← A.halting.born_dilRun_fst (fun _ => rfl),
    PMF.map_comp]
  rfl

/-- **The coherent pure algorithm has the random-oracle law of the core algorithm.** -/
theorem realLaw_toQueryAlgCoh [AddGroup Y] [Nonempty Y] {B : Type} (e : Y ≃ B) :
    A.toQueryAlgCoh.realLaw e = A.realLaw e := by
  simp only [QueryAlg.realLaw, Alg.realLaw, outLaw_toQueryAlgCoh]

/-- **An event of a terminating outcome bounds the coherent pure form's event**: the probability
that `A` terminates with an outcome in `S` is at most the probability of `S` for the coherent pure
form with non-termination read as `o₀`. -/
theorem toOuterMeasure_realLaw_le_coh [AddGroup Y] [Nonempty Y] {B : Type} (e : Y ≃ B) (o₀ : O)
    (S : Set (Outcome O X B)) :
    (A.realLaw e).toOuterMeasure {p | ∃ o ∈ p.out, ⟨o, p.oracle⟩ ∈ S} ≤
      ((A.toQueryAlgCoh.mapOut (·.getD o₀)).realLaw e).toOuterMeasure S := by
  rw [QueryAlg.realLaw_mapOut, PMF.toOuterMeasure_map_apply, realLaw_toQueryAlgCoh]
  refine PMF.toOuterMeasure_mono _ ?_
  rintro ⟨q, H⟩ ⟨⟨o, ho, hS⟩, -⟩
  rw [Option.mem_def] at ho
  subst ho
  exact hS

end Alg

end GordieHowe.Quantum

