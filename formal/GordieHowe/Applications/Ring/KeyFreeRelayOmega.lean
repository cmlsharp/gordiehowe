-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeRelay
public import GordieHowe.Applications.Ring.KeyFreeSignFactors

@[expose] public section

/-!
# The key-free relay at a fixed base component

For a key-free signer that factors through the base component and a public part
(`KFSignFactors`, `GordieHowe/Applications/Ring/KeyFreeSignFactors.lean`) and a statement program
whose run reads only the base component (`stmtPω`), the signature and the statement at the base
component `ω` read through the table in force `T` (`ωT ω T`): the public part and the signature
`F.out` at `ωT ω T` computed classically, then ONE read of the oracle at the kept point `F.xk`, of
which the second component gives the assignments; the statement `stmtPω` after the signature's
assignments. They are the runs of the key-free relay in side-read mode
(`GordieHowe/Applications/Ring/KeyFreeRelayB.lean`).

- `ωT`, `base_reprogT`: the base component of the oracle read through a table.
- `sigPω`, `xPω`, `sigPω_queriesLE`: the signature and the statement at the base component.
- `run_sigPω`, `xPω_eq`: at an oracle `reprogT T H` with `base sp H = ω`, they are the key-free
  signature's run and the statement program's output.
-/

namespace GordieHowe

open Quantum Signature QROM OracleProg RingSignature.OracleSplit

namespace RingSignature.KeyFree

open RingSignature.Insider

variable {X Y Y₁ Y₂ : Type} [DecidableEq X] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : OracleSplit Y Y₁ Y₂)

/-- **The base component read through a table**: `ω` off the table, the base component of the
table's entry on it. -/
def ωT (ω : X → Y₁) (T : X → Option Y) : X → Y₁ := fun x =>
  match T x with
  | some y => (sp y).1
  | none => ω x

omit [DecidableEq X] in
/-- **The base component of the oracle read through a table** is the base component read through
the table. -/
theorem base_reprogT (H : X → Y) (T : X → Option Y) :
    base sp (reprogT T H) = ωT sp (base sp H) T :=
  funext fun x => by cases h : T x <;> simp [base, reprogT, ωT, h]

variable {N n : ℕ} {TS : Signature.SchemeTypes} {RMsg : Type} [DecidableEq TS.PK]
  (B : BaseSigner X Y N TS RMsg) {Pf PC : Type} [Fintype Pf] [DecidableEq Pf]
  [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) ⟨Pf, PC⟩}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {SC X₀ R Pb : Type}
  (pks : Fin n → B.PK)
  {ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y)))}
  (F : KFSignFactors sp Pb ksign) (stmtPω : (X → Y₁) → RingStmt B → X₀)
  (toR : X₀ → Req B PS adm n × ℕ → B.BSig → R) (dummyR : Req B PS adm n × ℕ → R) {Q : ℕ}
  (sc : Fin Q → SC)

/-- **The key-free signature at the base component `ω` and the table `T`**: for a signing request
by a member of a supported ring below `Q`, the public part and the signature `F.out` at `ωT ω T`;
on one, a read of the oracle at the kept point, the published value, the signature and the
assignments from the second component read; `none` otherwise. -/
noncomputable def sigPω (ω : X → Y₁) (T : X → Option Y) (c : ℕ) :
    Req B PS adm n → OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y)))
  | .sign s Rg m =>
    if h : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg then
      match F.out (ωT sp ω T) (pks s) Rg c m (sc ⟨c, h.1⟩) with
      | none => .pure none
      | some q => .query (F.xk (ωT sp ω T) (pks s) Rg m q.1) fun y =>
          .pure (some (F.pub (ωT sp ω T) (pks s) Rg m q.1, q.2,
            F.asg (ωT sp ω T) (pks s) Rg m q.1 (sp y).2))
    else .pure none
  | _ => .pure none

/-- **The statement of a signed request at the base component `ω` and the table `T`**:
`stmtPω` at the base component read through `T` overridden by the signature's assignments. -/
def xPω (ω : X → Y₁) (T : X → Option Y) :
    Req B PS adm n → Option (B.Pub × B.BSig × List (Assignment X Y)) → Option X₀
  | .sign _ Rg m, some p => some (stmtPω (ωT sp ω (overT T (lastAssign p.2.2))) ⟨Rg, m, p.1⟩)
  | _, _ => none

omit [DecidableEq X] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The signature at the base component reads at most once.** -/
theorem sigPω_queriesLE (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) :
    (sigPω sp B pks F sc ω T c r).QueriesLE 1 := by
  intro H
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · simp [sigPω, trace]
  · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
    · rw [sigPω, dite_eq_left_of_eq_true (eq_true hc)]
      split <;> simp [trace]
    · rw [sigPω, dite_eq_right_of_eq_false (eq_false hc)]
      simp [trace]
  · simp [sigPω, trace]

variable (h : X → Y) (m : MURequest (SignOracle.none B.core) n ⊕ R → Option (MUResponse B.core ⊕ Pf))

variable {sp B pks F stmtPω toR dummyR sc}

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The signature at the base component runs as the key-free signature** at every oracle `H'`
whose base component is `ωT ω T`. -/
theorem run_sigPω (ω : X → Y₁) (T : X → Option Y) (c : ℕ) (r : Req B PS adm n) (H' : X → Y)
    (hb : base sp H' = ωT sp ω T) :
    (sigPω sp B pks F sc ω T c r).run H' = (sigP B pks ksign sc c r).run H' := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩
  · rfl
  · by_cases hc : c < Q ∧ pks s ∈ Rg.1 ∧ adm Rg
    · rw [sigPω, sigP, dite_eq_left_of_eq_true (eq_true hc), dite_eq_left_of_eq_true (eq_true hc)]
      erw [F.run_eq, hb]
      cases F.out (ωT sp ω T) (pks s) Rg c msg (sc ⟨c, hc.1⟩) <;> rfl
    · rw [sigPω, sigP, dite_eq_right_of_eq_false (eq_false hc),
        dite_eq_right_of_eq_false (eq_false hc)]
  · rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The statement at the base component is the statement program's output**, for a statement
program reading only the base component (`hst`), at every oracle `reprogT T H` with
`base sp H = ω`. -/
theorem xPω_eq {stmtP : RingStmt B → OracleProg X Y X₀}
    (hst : ∀ x (G : X → Y), (stmtP x).run G = stmtPω (base sp G) x) (H : X → Y)
    (T : X → Option Y) (r : Req B PS adm n)
    (o : Option (B.Pub × B.BSig × List (Assignment X Y))) :
    xPω sp B stmtPω (base sp H) T r o =
      (xP B stmtP r o).run ((reprogT T H).reprogram (asgOf B o)) := by
  rcases r with i | ⟨s, Rg, msg⟩ | ⟨i, bm⟩ <;> rcases o with _ | p
  · rfl
  · rfl
  · rfl
  · simp only [xPω, xP, run_mapOutput, asgOf, Option.elim, hst, reprogram_eq_reprogT,
      ← reprogT_overT, base_reprogT]
  · rfl
  · rfl

end RingSignature.KeyFree

end GordieHowe
