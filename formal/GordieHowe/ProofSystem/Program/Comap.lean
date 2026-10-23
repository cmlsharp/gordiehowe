-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Basic

@[expose] public section

/-!
# An application phase at another statement type

An application phase reads the statement only through `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.ok`, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.pub` and
`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.event`. Composing those with a map `f : Stmt' → Stmt` gives the same phase over the
statements `Stmt'`, for the relation `{(x', w) | (f x', w) ∈ rel}` (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.comap`; with a
statement check, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.comapWith`); its honest prover and event bounds carry over
(`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.comap`, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.Honest.ErrorBound.comap`, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.EventBound.comap`). The series–parallel form of a multi-circuit IOP
(`GordieHowe/ProofSystem/Program/ForkJoinComap.lean`) uses it to state the compiled argument over the
statement's public values (a type with a codec) instead of a program valuation.
-/

namespace GordieHowe

open IOP
open scoped NNReal

namespace RealizedProgram.ProofSystem.PhaseStep

variable {Stmt Stmt' W : Type} {rel : Set (Stmt × W)} {m : ℕ} {Pub Wit : Fin m → Type}
  {holds : ∀ i, Pub i → Wit i → Prop}

/-- **An application phase at the statements `Stmt'`**, read through `f`. -/
def comap (A : PhaseStep Stmt W rel Pub Wit holds) (f : Stmt' → Stmt) :
    PhaseStep Stmt' W {p | (f p.1, p.2) ∈ rel} Pub Wit holds where
  n := A.n
  spec := A.spec
  ok x tr := A.ok (f x) tr
  pub i x tr := A.pub i (f x) tr
  extract := A.extract
  event j w x tr := A.event j w (f x) tr
  sound x w tr hok hall := by
    rcases A.sound (f x) w tr hok hall with ⟨w', hw, hrel⟩ | hev
    · exact .inl ⟨w', hw, hrel⟩
    · exact .inr hev

variable {I : Type} {relI : Set (Stmt × I)} {In : Fin m → Type} {dom : ∀ i, Pub i → In i → Prop}

/-- **The simulator of an application phase at the statements `Stmt'`**: the same coins, the
simulator read through `f`.

Running time: one evaluation of `f` and one run of `SA`. This running time is argued here, not
proved in Lean. -/
def Sim.comap {A : PhaseStep Stmt W rel Pub Wit holds} (SA : A.Sim) (f : Stmt' → Stmt) :
    (A.comap f).Sim where
  SimCoins := SA.SimCoins
  sim x ch := SA.sim (f x) ch

/-- **The honest prover of an application phase at the statements `Stmt'`**: the same pads and
honest inputs, the prover and the events read through `f`, on the honest inputs
`{(x', y) | (f x', y) ∈ relI}`, simulated by `Sim.comap`. -/
def Honest.comap {A : PhaseStep Stmt W rel Pub Wit holds} {SA : A.Sim} (Ah : A.Honest I relI In dom SA)
    (f : Stmt' → Stmt) : (A.comap f).Honest I {p | (f p.1, p.2) ∈ relI} In dom (SA.comap f) where
  Pads := Ah.Pads
  wit := Ah.wit
  prover x y π := Ah.prover (f x) y π
  bad j x y c := Ah.bad j (f x) y c
  ok_honest x y hy π ch hav := Ah.ok_honest (f x) y hy π ch hav
  dom_honest x y hy π ch hav := Ah.dom_honest (f x) y hy π ch hav
  identDistrib x y hy ch := Ah.identDistrib (f x) y hy ch

/-- **The completeness error carries over** to the honest prover at `Stmt'`. -/
theorem Honest.ErrorBound.comap {A : PhaseStep Stmt W rel Pub Wit holds}
    {SA : A.Sim} {Ah : A.Honest I relI In dom SA} {e : Stmt → ℝ≥0} (h : Ah.ErrorBound e) (f : Stmt' → Stmt) :
    (Ah.comap f).ErrorBound fun x => e (f x) :=
  fun x y hy => h (f x) y hy

/-- **The completeness error over the coins carries over** to the honest prover at `Stmt'`. -/
theorem Honest.CoinErrorBound.comap {A : PhaseStep Stmt W rel Pub Wit holds}
    {SA : A.Sim} {Ah : A.Honest I relI In dom SA} {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (Stmt × J)}
    {inp : J → Ω → I} {e : Stmt → ℝ≥0} (h : Ah.CoinErrorBound relJ inp e) (f : Stmt' → Stmt) :
    (Ah.comap f).CoinErrorBound {p | (f p.1, p.2) ∈ relJ} inp fun x => e (f x) :=
  fun x y hy => h (f x) y hy

/-- **The event bounds carry over** to the phase at `Stmt'`. -/
theorem EventBound.comap {A : PhaseStep Stmt W rel Pub Wit holds} {ε : A.spec.ChallengeIdx → NNReal}
    (h : A.EventBound ε) (f : Stmt' → Stmt) : (A.comap f).EventBound ε :=
  fun j w x tr => h j w (f x) tr


/-- **An application phase at the statements `Stmt'` with a statement check**: the verifier also
checks `chk` on the statement, read through `f`, for the relation
`{(x', w) | chk x' ∧ (f x', w) ∈ rel}`. -/
def comapWith (A : PhaseStep Stmt W rel Pub Wit holds) (f : Stmt' → Stmt) (chk : Stmt' → Bool) :
    PhaseStep Stmt' W {p | chk p.1 = true ∧ (f p.1, p.2) ∈ rel} Pub Wit holds where
  n := A.n
  spec := A.spec
  ok x tr := chk x && A.ok (f x) tr
  pub i x tr := A.pub i (f x) tr
  extract := A.extract
  event j w x tr := A.event j w (f x) tr
  sound x w tr hok hall := by
    obtain ⟨hc, hok⟩ := Bool.and_eq_true _ _ ▸ hok
    rcases A.sound (f x) w tr hok hall with ⟨w', hw, hrel⟩ | hev
    · exact .inl ⟨w', hw, hc, hrel⟩
    · exact .inr hev

/-- **The simulator of an application phase with a statement check**: as `Sim.comap`.

Running time: one evaluation of `f` and one run of `SA`. This running time is argued here, not
proved in Lean. -/
def Sim.comapWith {A : PhaseStep Stmt W rel Pub Wit holds} (SA : A.Sim) (f : Stmt' → Stmt)
    (chk : Stmt' → Bool) : (A.comapWith f chk).Sim where
  SimCoins := SA.SimCoins
  sim x ch := SA.sim (f x) ch

/-- **The honest prover of an application phase with a statement check**, on the honest inputs whose
statements pass the check, simulated by `Sim.comapWith`. -/
def Honest.comapWith {A : PhaseStep Stmt W rel Pub Wit holds} {SA : A.Sim}
    (Ah : A.Honest I relI In dom SA) (f : Stmt' → Stmt) (chk : Stmt' → Bool) :
    (A.comapWith f chk).Honest I {p | chk p.1 = true ∧ (f p.1, p.2) ∈ relI} In dom
      (SA.comapWith f chk) where
  Pads := Ah.Pads
  wit := Ah.wit
  prover x y π := Ah.prover (f x) y π
  bad j x y c := Ah.bad j (f x) y c
  ok_honest x y hy π ch hav := by
    show (chk x && A.ok (f x) _) = true
    rw [hy.1, Bool.true_and]
    exact Ah.ok_honest (f x) y hy.2 π ch hav
  dom_honest x y hy π ch hav := Ah.dom_honest (f x) y hy.2 π ch hav
  identDistrib x y hy ch := Ah.identDistrib (f x) y hy.2 ch

/-- **The completeness error carries over** to the honest prover with a statement check. -/
theorem Honest.ErrorBound.comapWith {A : PhaseStep Stmt W rel Pub Wit holds}
    {SA : A.Sim} {Ah : A.Honest I relI In dom SA} {e : Stmt → ℝ≥0} (h : Ah.ErrorBound e) (f : Stmt' → Stmt)
    (chk : Stmt' → Bool) : (Ah.comapWith f chk).ErrorBound fun x => e (f x) :=
  fun x y hy => h (f x) y hy.2

/-- **The completeness error over the coins carries over** to the honest prover with a statement
check: an input whose statement fails the check is off the relation of every coin. -/
theorem Honest.CoinErrorBound.comapWith {A : PhaseStep Stmt W rel Pub Wit holds}
    {SA : A.Sim} {Ah : A.Honest I relI In dom SA} {J Ω : Type} [Fintype Ω] [Nonempty Ω] {relJ : Set (Stmt × J)}
    {inp : J → Ω → I} {e : Stmt → ℝ≥0} (h : Ah.CoinErrorBound relJ inp e) (f : Stmt' → Stmt)
    (chk : Stmt' → Bool) :
    (Ah.comapWith f chk).CoinErrorBound {p | chk p.1 = true ∧ (f p.1, p.2) ∈ relJ} inp
      fun x => e (f x) := by
  intro x y hy
  refine le_trans (QROM.probUniform_mono fun u hu => ?_) (h (f x) y hy.2)
  rcases hu with hu | hu
  · exact .inl fun h' => hu ⟨hy.1, h'⟩
  · exact .inr hu

/-- **The event bounds carry over** to the phase with a statement check. -/
theorem EventBound.comapWith {A : PhaseStep Stmt W rel Pub Wit holds}
    {ε : A.spec.ChallengeIdx → NNReal} (h : A.EventBound ε) (f : Stmt' → Stmt)
    (chk : Stmt' → Bool) : (A.comapWith f chk).EventBound ε :=
  fun j w x tr => h j w (f x) tr

end RealizedProgram.ProofSystem.PhaseStep

end GordieHowe
