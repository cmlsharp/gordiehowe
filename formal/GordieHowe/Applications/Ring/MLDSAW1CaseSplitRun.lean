-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseS
public import GordieHowe.Applications.Ring.KeyFreeCanon
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeBase

@[expose] public section

/-!
# The goal of the key-free chain for the ML-DSA ring publishing `w₁`, split per run

The goal of the key-free chain at the ML-DSA ring publishing `w₁` (`w1Goal`,
`GordieHowe/Applications/Ring/MLDSAW1CaseU.lean`), in one simulation-extraction run of
`seAlgKF` for an adversary with the side-mode key-free relay `kfRelaySide` absorbed at a base
component `ω`, split at the canonical witness (`kfCanon`) into case U, a guess of a logged
signing entry's signature, and case S with a second signature (`W1SecondSig`,
`GordieHowe/Applications/Ring/MLDSAW1CaseS.lean`): the canonical split
(`simProb_forgerWinsKF_le_canon`), the logged signing entries of the run are signed requests of
the relay (`simProb_seAlgKF_asks` with `asksIn_kfRelaySide_signed`), and case S splits
(`w1CaseS_guess_or_second`).

- **`simProb_w1Goal_le`**: the forger's win at `w1Goal` is at most the canonical witness's case
  U, plus a logged signing entry's signature equal to the canonical witness's, plus the canonical
  witness in case S with a second signature.
- `w1SlotAsks_hp`: a request whose program can ask a signing entry has number below `Q` and is
  not the blank request.
-/

open scoped ENNReal

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

omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The goal of the key-free chain splits per run into case U, a guess and a second
signature**: in the simulation-extraction run of `seAlgKF` for an adversary `A₀` with the
side-mode key-free relay `kfRelaySide` at the side coins `sc` absorbed at the base component `ω`,
for the users' seeds `ξ`, the forger's win at `w1Goal` is at most the probability of the canonical
witness in case U, plus that of a logged signing entry's signature equal to the canonical
witness's, plus that of the canonical witness in case S with a second signature
(`W1SecondSig`). The idle main request is not a signing entry. -/
theorem simProb_w1Goal_le
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
    (ξ : Fin n → (Bf).KeyCoins) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq) (hidle : w1SignEntry idle = none)
    {SC' : Type} [Fintype SC'] [DecidableEq SC'] (prf : Frg → Option Mc.NIProof)
    {shA₀ : AlgShape Xq Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)} (A₀ : AdaptiveIAlg shA₀ (Frg × X₀f))
    (Psim : NARG.Simulator Xq (XOut kh e) (Stmt × (MURequest (SignOracle.none (Bf).core) n ⊕ Rq))
      (Mc.Response b) SC')
    (Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))) (kq : ℕ) :
    simProb (outEquiv kh e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
        (forgerWinsKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
          (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst) Psim Ext
          (fun _ w => w) (w1Goal prims O Mo βmin tol enc k D bmsg adm sp
            (fun j => (Bf).pk (ξ j)) ω)) ≤
      simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf
          ξ Q (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
          (forgerCanonKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q (((A₀.absorbAssign
              (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst) Psim Ext
            (fun _ w => w) (w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)))
            (fun f _ w => w1CaseU (bmsg := bmsg) O sp ω f w)) +
        simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
            prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
          (forgerCanonKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q (((A₀.absorbAssign
              (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst) Psim Ext
            (fun _ w => w) (w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)))
            (fun _ rs w => ∃ e' ∈ rs, (w1SignEntry e').isSome = true ∧ w1EntrySig e' = some w.sig ∧
              KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
                (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
                (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω e'))
                +
        simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS)
            prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
          (forgerCanonKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q (((A₀.absorbAssign
              (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst) Psim Ext
            (fun _ w => w) (w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)))
            (fun f rs w => ∃ i σe, W1SecondSig sp hO ξ sc ω f rs w i σe)) := by
  -- TODO(unbundle-M4): the adversary and `rel`/`enc`/`dummyS` are given explicitly; unifying them
  -- against the goal times out.
  have h0 := (simProb_forgerWinsKF_le_canon (rel := rel) (enc := penc) (dummyS := dummyS) Qs prf ξ Q kq (((A₀.absorbAssign
      (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)
    Psim Ext (fun _ w => w) _ _ _
    (fun f rs w => w1CaseS (adm := adm) (fun j => (Bf).pk (ξ j)) f rs w) (fun _ _ _ h => h.1)
    fun f rs w w' hg hok => w1Goal_split sp _ ω f rs w w' hg hok)
  refine h0.trans ?_
  -- TODO(unbundle-M4): `rw [add_assoc]` times out here (presumably its closing `rfl` attempt
  -- comparing the two different `simProb` sums); rewrite by `add_assoc` as a term instead.
  refine le_of_le_of_eq ?_ (add_assoc _ _ _).symm
  refine add_le_add (le_refl _) ?_
  have hP : ∀ Tb c r, MultiRelay.AsksIn (MUResponse (Bf).core ⊕ Mc.Response b)
      (OracleProg.elimSide (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle).side
        ((kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
          (w1DummyR (PS := PSh) (Q := Q)) sc ω idle).prog Tb c r))
      fun r' => (w1SignEntry r').isSome = true →
        KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω r' := by
    intro Tb c r ans r' h hp
    rcases asksIn_kfRelaySide_signed sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO) (w1ToR (PS := PSh) (Q := Q)) sc
        (w1DummyR (PS := PSh) (Q := Q)) (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) ω idle Tb c r
        ans r' h with h' | h'
    · subst h'
      rcases r <;> simp [reqOf, w1SignEntry, w1DummyR] at hp
    · exact ⟨Tb, c, r, h'⟩
  have h1 : simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS :=
      dummyS) prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
            (forgerCanonKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q (((A₀.absorbAssign
                (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)
      Psim Ext (fun _ w => w) (w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)))
      (fun f rs w => w1CaseS (adm := adm) (fun j => (Bf).pk (ξ j)) f rs w)) ≤
      simProb (outEquiv kh e) (extAdv Qs (seAlgKF (rel := rel) (enc := penc) (dummyS := dummyS) prf
          ξ Q (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)) Psim Q kq)
            fun c Db => (forgerCanonKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
                (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)
      Psim Ext (fun _ w => w) (w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)))
      (fun f rs w => w1CaseS (adm := adm) (fun j => (Bf).pk (ξ j)) f rs w)) c Db ∧
        ∀ r' ∈ Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := penc)
          (dummyS := dummyS) prf ξ Q (((A₀.absorbAssign (Resp' := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut
            Prod.fst)).toTPKindAlg Psim Q c).1.1.logs,
          (w1SignEntry r').isSome = true → (w1SignEntry r').isSome = true →
            KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
              (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
              (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω r' :=
    (simProb_seAlgKF_asks (Qs := Qs) (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q
    A₀ (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
      (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) sp ω Psim kq
    (forgerCanonKF (rel := rel) (enc := penc) (dummyS := dummyS) prf ξ Q (((A₀.absorbAssign (Resp'
        := MUResponse (Bf).core ⊕ Mc.Response b)
      (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).restrictAt sp ω).mapOut Prod.fst)
      Psim Ext (fun _ w => w) (w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)))
      (fun f rs w => w1CaseS (adm := adm) (fun j => (Bf).pk (ξ j)) f rs w)) _ hP
    (fun r => (w1SignEntry r).isSome) rfl
    (by change (w1SignEntry idle).isSome = false; rw [hidle]; rfl)).trans
      (simProb_mono _ _ fun c D h => ⟨h.1, fun r' hr' hp => (h.2 r' hr' hp).1⟩)
  refine h1.trans ?_
  refine (simProb_mono _ _ fun c Db h => ?_).trans (simProb_or_le _ _ _ _)
  obtain ⟨⟨w, hw, hS⟩, hsig⟩ := h
  have hok := ((kfCanon_eq_some_iff _ _ _ _ _ _ _).1 hw).1
  rcases w1CaseS_guess_or_second sp hO hok hS fun r' hr' hp => hsig r' (List.mem_of_mem_take hr')
      hp hp
    with hg | hs
  · exact .inl ⟨w, hw, hg⟩
  · exact .inr ⟨w, hw, hs⟩

omit [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **Only slot requests ask signing entries** at the side-mode key-free relay: a request whose
program can ask a signing entry has number below `Q` and is not the blank request, when the
default request is no signing request (`hdef`; the corruption of user `0` by instance). -/
theorem w1SlotAsks_hp
    [Inhabited (RingSignature.Insider.Req Bf PSf adm n)]
    (hdef : ∀ s Rg m, (default : RingSignature.Insider.Req Bf PSf adm n) ≠ .sign s Rg m)
    (hO : O.ReadsFst sp) (ξ : Fin n → (Bf).KeyCoins)
    (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : Xq → Y₁)
    (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq) :
    ∀ r r', (AssignRelay.relayOf (kfRelaySide sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) (w1ToR (PS := PSh) (Q := Q))
        (w1DummyR (PS := PSh) (Q := Q)) sc ω idle) Q).CanAsk r r' →
      (w1SignEntry r').isSome = true → (r.1.2 : ℕ) < Q ∧ r ≠ default := by
  intro r r' hc hs
  have h := MultiRelay.canAsk_of_asksIn_elimSide _ (AssignRelay.asksIn_relayOf_elimSide _ Q
    (fun T' c rq => asksIn_kfRelaySide_signed sp Bf (fun j => (Bf).pk (ξ j))
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO) (w1ToR (PS := PSh) (Q := Q)) sc
      (w1DummyR (PS := PSh) (Q := Q)) (w1KFStmt prims O Mo βmin tol enc k D bmsg sp) ω idle T' c
      rq) r) hc
  rcases h with h | ⟨s, Rg, m, hcQ, q, y, hr, -, -, -, -⟩
  · subst h
    rcases r with ⟨⟨rq, c⟩, T'⟩
    rcases rq <;> simp [reqOf, w1SignEntry, w1DummyR] at hs
  · exact ⟨hcQ, fun hd => hdef s Rg m (by subst hd; exact hr)⟩

end GordieHowe.Ring.MLDSAW1
