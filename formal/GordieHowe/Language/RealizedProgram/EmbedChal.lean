-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed

@[expose] public section

/-!
# GordieHowe realized programs: a challenge drawn through a renaming

An event of a program `ir` read in the environment of a program `ir'` through a renaming
(`RealizedProgram.pullEnv`) has, at a challenge of one coordinate drawn from the field, the
probability it has in `ir` (`probUniform_pullEnv_setChal`): drawing `ir'`'s renamed challenge and
reading the environment through the renaming is drawing `ir`'s challenge in the environment read
through the renaming. A frontend reading a program's events through a renaming (a ring program
holding a proof of possession's domain `H`) transports their probability bounds this way.

* `Env.updChal`: the environment with coordinate `0` of challenge `j` set to a field element and
  its other coordinates `0`; `setChal_eq_updChal`: a challenge of one coordinate drawn from the
  field sets it so; `probUniform_setChal_eq`: drawing the challenge is drawing the element.
* `pullEnv_updChal`: setting the renamed challenge and reading through the renaming is setting the
  challenge in the environment read through the renaming.
-/

namespace GordieHowe.RealizedProgram

open IOP
open scoped NNReal ENNReal

variable {ir ir' : RealizedProgram} {I : Interp}

/-- **The environment with coordinate `0` of challenge `j` set to `a`**, its other coordinates
`0`. -/
def Env.updChal (e : ir.Env I) (j : ℕ) (a : (I (ir.chalField j)).K) : ir.Env I :=
  { e with chal := Function.update e.chal j fun i => if i = 0 then a else 0 }

/-- **A challenge of one coordinate drawn from the field sets coordinate `0`.** -/
theorem setChal_eq_updChal {j : ℕ} (hsz : (ir.challenge j).size = 1) (e : ir.Env I)
    (c : ir.ChalVal I j) :
    e.setChal j c =
      e.updChal j ((I (ir.chalField j)).samplerVal _ (c ⟨0, by rw [hsz]; omega⟩)) := by
  unfold Env.setChal Env.updChal
  congr 1
  congr 1
  funext i
  by_cases hi : i = 0
  · subst hi
    rw [dif_pos (by rw [hsz]; omega), if_pos rfl]
  · rw [dif_neg (by rw [hsz]; omega), if_neg hi]

/-- **Drawing a challenge of one coordinate from the field is drawing the element**: the
probability of an event of the environment with the challenge set is that of the environment
with coordinate `0` set to a uniform element. -/
theorem probUniform_setChal_eq {j : ℕ} (hsz : (ir.challenge j).size = 1)
    (hsm : (ir.challenge j).sampler = .full) (P : ir.Env I → Prop) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I j : P (e.setChal j c)] =
      Pr[a ← (I (ir.chalField j)).K : P (e.updChal j a)] := by
  have h0 : 0 < (ir.challenge j).size := by rw [hsz]; omega
  simp only [setChal_eq_updChal hsz e]
  have key : ∀ (F : FieldInterp) (n : ℕ) (hn : n = 1) (h0 : 0 < n) (s : Sampler) (hs : s = .full)
      (Q : F.K → Prop), Pr[c ← (Fin n → F.SamplerTy s) : Q (F.samplerVal s (c ⟨0, h0⟩))] =
        Pr[a ← F.K : Q a] := by
    intro F n hn h0 s hs Q
    subst hn hs
    exact Uniform.probUniform_comp (f := fun c : Fin 1 → F.K => c ⟨0, h0⟩)
      (Uniform.of_equiv (Equiv.funUnique (Fin 1) F.K)) Q
  exact key _ _ hsz h0 _ hsm fun a => P (e.updChal j a)

/-- **Setting the renamed challenge and reading through the renaming** is setting the challenge
in the environment read through the renaming, when no other challenge is renamed to it. -/
theorem pullEnv_updChal {σ : Renaming} {V : List ℕ} {j : ℕ}
    (hinj : ∀ j', σ.chal j' = σ.chal j → j' = j) (e' : ir'.Env I)
    (a : (I (ir'.chalField (σ.chal j))).K) :
    ir.pullEnv σ V (e'.updChal (σ.chal j) a) = (ir.pullEnv σ V e').updChal j (castElt a) := by
  unfold Env.updChal pullEnv
  congr 1
  funext j' i
  by_cases hj : j' = j
  · subst hj
    simp only [Function.update_self]
    split_ifs
    · rfl
    · exact castElt_zero
  · dsimp only
    rw [Function.update_of_ne hj, Function.update_of_ne fun h => hj (hinj j' h)]

/-- **An event read through a renaming has its probability at the renamed challenge**: at a
challenge `j` of `ir` and its renamed challenge `σ.chal j` of `ir'`, each of one coordinate drawn
from the field, of the same field identifier, no other challenge renamed to `σ.chal j`, the
probability over `ir'`'s challenge of `P` of the environment read through the renaming is the
probability over `ir`'s challenge of `P` with the challenge set in the environment read through
the renaming. -/
theorem probUniform_pullEnv_setChal {σ : Renaming} {V : List ℕ} {j : ℕ}
    (hsz' : (ir'.challenge (σ.chal j)).size = 1) (hsm' : (ir'.challenge (σ.chal j)).sampler = .full)
    (hsz : (ir.challenge j).size = 1) (hsm : (ir.challenge j).sampler = .full)
    (hf : ir'.chalField (σ.chal j) = ir.chalField j)
    (hinj : ∀ j', σ.chal j' = σ.chal j → j' = j) (P : ir.Env I → Prop) (e' : ir'.Env I) :
    Pr[c ← ir'.ChalVal I (σ.chal j) : P (ir.pullEnv σ V (e'.setChal (σ.chal j) c))] =
      Pr[c ← ir.ChalVal I j : P ((ir.pullEnv σ V e').setChal j c)] := by
  rw [probUniform_setChal_eq hsz' hsm' (fun e => P (ir.pullEnv σ V e)) e',
    probUniform_setChal_eq hsz hsm P (ir.pullEnv σ V e')]
  simp only [pullEnv_updChal hinj]
  exact probUniform_castElt hf fun b => P ((ir.pullEnv σ V e').updChal j b)

end GordieHowe.RealizedProgram
