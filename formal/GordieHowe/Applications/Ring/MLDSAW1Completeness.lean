-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Ring
public import GordieHowe.Model.RingSignature.BaseCompleteness

@[expose] public section

/-!
# Completeness of the ML-DSA ring signature publishing `w₁`

Completeness (BKM06 Definition 1 with errors, `RingScheme.CompleteWithin`) of the scheme constants
`w1Concrete p` and `w1Scheme44`, `w1Scheme65`, `w1Scheme87` of
`GordieHowe/Applications/Ring/MLDSAW1Ring.lean`, by `completeWithin_ofBase`: the base signer's
correctness error is `0` (`correctWithin_w1ConcreteBase`: every signature of the ring loop verifies
at its recomputed commitment), so the ring signature refuses honest rings with probability at most
the base signer's refusal rate `ρ` and is rejected with probability at most the proof system's
completeness error.

The headlines:

- `w1Concrete.completeWithin`: at the concrete primitives of an approved parameter set.
- `w1Scheme44.completeWithin`, `w1Scheme65.completeWithin`, `w1Scheme87.completeWithin`: at
  ML-DSA-44, ML-DSA-65 and ML-DSA-87.

`w1Concrete.completeWithin_satisfiable`: `w1Concrete.completeWithin` at the refusal rate `1` and
the accepting proof system with completeness error `0`.

## What is not shown

The refusal rate `ρ` is a hypothesis (`BaseSigner.RefuseWithin`). The signer refuses an honest ring
when the public check fails, when two members' `µ_j` collide, or when all `k` calls reject; the
first two are bounded in `GordieHowe/Applications/Ring/PublicW1/MLDSAPublicW1Refusal.lean` at the
game's independent oracles (`expect_not_ringCheck_honestRing_le`, in terms of an average over the
seed of a function of an honest key's check defect; `expect_not_muDistinct_le`), and the third
needs a lower bound on the keep probability of one call for honest rings, which
`MLDSAPublicW1Hedged.lean` proves only on the good event of the anonymity analysis
(`keepBound_of_keepGood`). Their transfer to the one oracle and the bounded loop is not formalized.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature _root_.MLDSA.Concrete
  GordieHowe.MLDSA.Spec
open scoped ENNReal

attribute [local instance] concreteNTTRingOps

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {p : Params} {T : ℕ}
  {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N reps : ℕ} [NeZero (bucketCount p)]
  [Nonempty (MaskBox p)] {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg]

section Generic

variable {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps}
  {M : MaskOracle X Y p T Msg}
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA ring signature publishing `w₁` at the concrete primitives**
(`completeWithin_ofBase` with correctness error `0`): for a refusal rate `ρ` of the base signer on
honest supported rings (`hρ`) and a proof system adaptively complete for the ring relation at
error `εp` (`hp`), the ring signature refuses with probability at most `ρ` and is rejected with
probability at most `0 + εp (q + qPub)`. -/
@[headline]
theorem w1Concrete.completeWithin (hp : p.isApproved) {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase p O M βmin tol k D bmsg).RefuseWithin adm ρ) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase p O M βmin tol k D bmsg) adm)
      εp) :
    (w1Concrete p O M βmin tol k D bmsg PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase p O M βmin tol k D bmsg).q +
        (w1ConcreteBase p O M βmin tol k D bmsg).qPub)) :=
  completeWithin_ofBase _ PS adm hρ (by
    simpa using correctWithin_w1ConcreteBase hp O M βmin tol k D bmsg) hPS

end Generic

omit [Nonempty Y] in
/-- **`w1Concrete.completeWithin` applies at the scheme constant**: at an approved parameter set,
with the accepting proof system (completeness error `0`, `ProofSystem.acceptAll_completeWithin`)
and the refusal rate `1` (`BaseSigner.refuseWithin_one`), `w1Concrete` is complete with errors `1`
and `0 + 0`. -/
theorem w1Concrete.completeWithin_satisfiable [Nonempty Y] (hp : p.isApproved)
    (O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps) (M : MaskOracle X Y p T Msg)
    (bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg)
    (adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop) [DecidablePred adm] :
    (w1Concrete p O M βmin tol k D bmsg (ProofSystem.acceptAll X Y _ _) adm).CompleteWithin 1
      (0 + 0) :=
  w1Concrete.completeWithin hp (BaseSigner.refuseWithin_one _ adm)
    (ProofSystem.acceptAll_completeWithin _)

section P44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-44 ring signature publishing `w₁`** (`w1Scheme44`;
`w1Concrete.completeWithin` at ML-DSA-44). -/
@[headline]
theorem w1Scheme44.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D bmsg).RefuseWithin adm ρ) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm)
      εp) :
    (w1Scheme44 O M βmin tol k D bmsg PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D bmsg).q +
        (w1ConcreteBase Pm O M βmin tol k D bmsg).qPub)) :=
  w1Concrete.completeWithin (Or.inl rfl) hρ hPS

end P44

section P65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-65 ring signature publishing `w₁`** (`w1Scheme65`;
`w1Concrete.completeWithin` at ML-DSA-65). -/
@[headline]
theorem w1Scheme65.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D bmsg).RefuseWithin adm ρ) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm)
      εp) :
    (w1Scheme65 O M βmin tol k D bmsg PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D bmsg).q +
        (w1ConcreteBase Pm O M βmin tol k D bmsg).qPub)) :=
  w1Concrete.completeWithin (Or.inr (Or.inl rfl)) hρ hPS

end P65

section P87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-87 ring signature publishing `w₁`** (`w1Scheme87`;
`w1Concrete.completeWithin` at ML-DSA-87). -/
@[headline]
theorem w1Scheme87.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D bmsg).RefuseWithin adm ρ) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm)
      εp) :
    (w1Scheme87 O M βmin tol k D bmsg PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D bmsg).q +
        (w1ConcreteBase Pm O M βmin tol k D bmsg).qPub)) :=
  w1Concrete.completeWithin (Or.inr (Or.inr rfl)) hρ hPS

end P87

/-! ### Ring-binding and converted base messages -/

section BindGeneric

variable {O : W1Oracles X Y p (concretePrimitivesKeyGen p)
    (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg) N reps}
  {M : MaskOracle X Y p T (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing
    (w1ConcreteBase p O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA ring signature publishing `w₁` with ring-binding base messages**
(`w1BindConcrete`; `w1Concrete.completeWithin` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindConcrete.completeWithin (hp : p.isApproved) {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase p O M βmin tol k D Prod.mk).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase p O M βmin tol k D Prod.mk) adm) εp) :
    (w1BindConcrete p O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase p O M βmin tol k D Prod.mk).q +
        (w1ConcreteBase p O M βmin tol k D Prod.mk).qPub)) :=
  w1Concrete.completeWithin hp hρ hPS

end BindGeneric

section Bind44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-44 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindScheme44`; `w1Scheme44.completeWithin` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindScheme44.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D Prod.mk).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk) adm) εp) :
    (w1BindScheme44 O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D Prod.mk).q +
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk).qPub)) :=
  w1Scheme44.completeWithin  hρ hPS

end Bind44

section Bind65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-65 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindScheme65`; `w1Scheme65.completeWithin` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindScheme65.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D Prod.mk).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk) adm) εp) :
    (w1BindScheme65 O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D Prod.mk).q +
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk).qPub)) :=
  w1Scheme65.completeWithin  hρ hPS

end Bind65

section Bind87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg
    (KeyRing (PubKey Pm Kg) N × RMsg) N reps}
  {M : MaskOracle X Y Pm T (KeyRing (PubKey Pm Kg) N × RMsg)}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D Prod.mk)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D Prod.mk).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-87 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindScheme87`; `w1Scheme87.completeWithin` at `bmsg := Prod.mk`). -/
@[headline]
theorem w1BindScheme87.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D Prod.mk).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk) adm) εp) :
    (w1BindScheme87 O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D Prod.mk).q +
        (w1ConcreteBase Pm O M βmin tol k D Prod.mk).qPub)) :=
  w1Scheme87.completeWithin  hρ hPS

end Bind87

section ConvGeneric

variable {O : W1Oracles X Y p (concretePrimitivesKeyGen p)
    Msg N reps}
  {M : MaskOracle X Y p T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing
    (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the converted ML-DSA ring signature publishing `w₁`** (`w1ConvConcrete`;
`w1Concrete.completeWithin` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvConcrete.completeWithin (hp : p.isApproved) {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m)).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm) εp) :
    (w1ConvConcrete p O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m)).q +
        (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) (fun _ m => m)).qPub)) :=
  w1Concrete.completeWithin hp hρ hPS

end ConvGeneric

section Conv44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

variable {O : W1Oracles X Y Pm Kg
    Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the converted ML-DSA-44 ring signature publishing `w₁`** (`w1ConvScheme44`;
`w1Scheme44.completeWithin` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvScheme44.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm) εp) :
    (w1ConvScheme44 O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).q +
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).qPub)) :=
  w1Scheme44.completeWithin  hρ hPS

end Conv44

section Conv65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

variable {O : W1Oracles X Y Pm Kg
    Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the converted ML-DSA-65 ring signature publishing `w₁`** (`w1ConvScheme65`;
`w1Scheme65.completeWithin` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvScheme65.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm) εp) :
    (w1ConvScheme65 O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).q +
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).qPub)) :=
  w1Scheme65.completeWithin  hρ hPS

end Conv65

section Conv87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

variable {O : W1Oracles X Y Pm Kg
    Msg N reps}
  {M : MaskOracle X Y Pm T Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m))) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing
    (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).PK N → Prop}
  [DecidablePred adm]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the converted ML-DSA-87 ring signature publishing `w₁`** (`w1ConvScheme87`;
`w1Scheme87.completeWithin` at `bmsg := fun _ m => m`). -/
@[headline]
theorem w1ConvScheme87.completeWithin {ρ : ℝ≥0∞}
    (hρ : (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).RefuseWithin adm ρ)
    {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin
      (RingSignature.ringRel
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)) adm) εp) :
    (w1ConvScheme87 O M βmin tol k D PS adm).CompleteWithin ρ
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).q +
        (w1ConcreteBase Pm O M βmin tol k D (RMsg := Msg) (fun _ m => m)).qPub)) :=
  w1Scheme87.completeWithin  hρ hPS

end Conv87

end GordieHowe.Ring.MLDSAW1
