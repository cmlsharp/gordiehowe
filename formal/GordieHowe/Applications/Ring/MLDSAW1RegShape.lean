-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeBase
public import GordieHowe.Applications.Ring.KeyFreeExtractBlock

@[expose] public section

/-!
# The register types of the ML-DSA ring publishing `w₁`, as shape terms

The adversary of the key-free chain at the ML-DSA ring publishing `w₁` absorbs the side-mode
key-free relay `kfRelaySide` at side coins `sc`, and the simulation-extraction adversary
`seAlgKF` wraps it. Its register types do not depend on `sc`: they are those of a shape term
(`AlgShape`, `GordieHowe/Model/Quantum/Interactive/AlgShape.lean`) at the shape of the base
adversary `A₀` and the relay's numbers (one oracle read, one pad sub-slot, `qOut + qSt` side
reads). Each equality closes by `rfl`, comparing the adversary with the shape term only.

- `absorbAssign_kfRelaySide_toShape`: the shape of the absorbed adversary is
  `AlgShape.absorbAssignS` at `A₀`'s shape, for every `sc`.
- `reg_seAlgKF_kfRelaySide`: the composed registers of `seAlgKF` (`SPBCS.Reg`) are the composed
  work register of the shape term (`KindShape.CW`), for every `sc`.
- `reg_seAlgKF_kfRelaySide_coins`: so the composed registers at two side coins `sc`, `sc'` are
  equal.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree GordieHowe.QROM
open GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N)
    kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}
  (sp : OracleSplit Y Y₁ (XOut kh e))

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "X₀f" => W1ExpStmt prims RMsg N
local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "PSh" => w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk
local notation "PSf" => (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb
  honest chk)
local notation "Rq" => W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q

attribute [local instance] admDecF

variable {Frg : Type}

section RegShape

omit [Nonempty Y₁] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The shape of the absorbed adversary at any side coins**: `AlgShape.absorbAssignS` at `A₀`'s
shape, one oracle read, one pad sub-slot and `qOut + qSt` side reads. -/
theorem absorbAssign_kfRelaySide_toShape
    [NeZero n]
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    [Inhabited Mc.NIProof] (hO : O.ReadsFst sp)
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) :
    (A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).toShape =
      A₀.toShape.absorbAssignS Y₁ Q 1 1
        ((w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO).qOut +
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp).qSt) :=
  rfl

omit [Nonempty Y₁] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The composed registers of the simulation-extraction adversary at any side coins** are the
composed work register (`KindShape.CW`) of the trace-preserving shape of `seAlgKFS` at the
restricted (`AlgShape.restrictAtS`) shape of `absorbAssign_kfRelaySide_toShape`. -/
theorem reg_seAlgKF_kfRelaySide
    [NeZero n]
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {Stmt Wit : Type} [Fintype Stmt]
    [DecidableEq Stmt] [Inhabited Stmt] {rel : Stmt → Wit → Prop} [DecidableRel rel]
    {penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → ProofQuery Stmt Wit} {dummyS : Stmt}
    [Inhabited Mc.NIProof] (hO : O.ReadsFst sp)
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    {SC' : Type} [Fintype SC'] [DecidableEq SC'] (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none (Bf).core) n ⊕ Rq))
      (Mc.Response b) SC')
    (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) :
    SPBCS.Reg (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
        (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp
          ω).mapOut Prod.fst)) Psim Q =
      (seAlgKFS (Stmt := Stmt) (M := Mc) (B := Bf)
        ((A₀.toShape.absorbAssignS Y₁ Q 1 1
        ((w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO).qOut +
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp).qSt)).restrictAtS Y₁ (XOut kh e))).tpKindS.CW
        (simExtChallenger Psim Q) :=
  rfl

omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The composed registers of the simulation-extraction adversary do not depend on the side
coins** (`reg_seAlgKF_kfRelaySide` at `sc` and `sc'`). -/
theorem reg_seAlgKF_kfRelaySide_coins
    [NeZero n]
    [Fintype (RingSignature.Insider.Req Bf PSf adm n)]
    [DecidableEq (RingSignature.Insider.Req Bf PSf adm n)]
    [Fintype (RingSignature.Insider.Resp Bf PSf adm)]
    [DecidableEq (RingSignature.Insider.Resp Bf PSf adm)]
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    {Stmt Wit : Type} [Fintype Stmt]
    [DecidableEq Stmt] [Inhabited Stmt] {rel : Stmt → Wit → Prop} [DecidableRel rel]
    {penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → ProofQuery Stmt Wit} {dummyS : Stmt}
    [Inhabited Mc.NIProof] (hO : O.ReadsFst sp)
    (ξ : Fin n → (Bf).KeyCoins) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    {SC' : Type} [Fintype SC'] [DecidableEq SC'] (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none (Bf).core) n ⊕ Rq))
      (Mc.Response b) SC')
    (sc sc' : Fin Q → KFCoins (p := p) (T := T) k D Y₁) :
    SPBCS.Reg (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
        (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp
          ω).mapOut Prod.fst)) Psim Q =
      SPBCS.Reg (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
        (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
        (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc' ω idle) Q).restrictAt sp
          ω).mapOut Prod.fst)) Psim Q :=
  (reg_seAlgKF_kfRelaySide sp hO ξ ω idle prf A₀ Psim sc).trans
    (reg_seAlgKF_kfRelaySide sp hO ξ ω idle prf A₀ Psim sc').symm

end RegShape

end GordieHowe.Ring.MLDSAW1
