-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Ring
public import GordieHowe.Applications.Ring.MLDSAW1Split
public import GordieHowe.Applications.Ring.RingAnonymitySplit
public import GordieHowe.Applications.Ring.PubWIEquiv
public import GordieHowe.Model.Quantum.Interactive.ClassicalRelabel
public import GordieHowe.Model.RingSignature.SaltReprogram
public import GordieHowe.Model.RingSignature.BaseCompleteness

@[expose] public section

/-!
# Anonymity of the ML-DSA ring signature publishing `w₁`

- `run_bsign_w1BaseSigner`: the base signer with the ring loop at the oracle `H` refuses unless the
  ring passes the public check against `G` and its members' `µ_j` are distinct, and otherwise is
  `loopOut` at the commitment hash read from `H` and the masks read from the randomness.
- `W1Oracles.IsPt`, `W1Oracles.split`: the points of the message-representative, commitment-hash
  and check oracles, and the split of the oracle into its values on them and off them.
  `W1Oracles.apply_eq_of_split`, `W1Oracles.muOrc_eq_of_split`, `chOrc_eq_of_split`,
  `gOrc_eq_of_split`, `hOrc_eq_of_split`: two oracles with the same first part agree at those
  points, and so do the oracles `muOrc`, `chOrc`, `gOrc` and `hOrc` read off them.
- `readsOnly_freshBase`: the base signer with fresh masks reads the oracle only through that first
  part (`BaseSigner.ReadsOnly`).
- `saltsEquiv`, `saltsEquiv_snd_apply`: the per-call nonces of `Q` requests as one vector of
  `Q · k` salts and the other coins.
- `hedgedBase`, `freshBase`, `hedgedScheme`, `freshScheme`: the base signers and schemes with
  hedged and with fresh masks, with the same proof system: the two base signers have the same
  statements and witnesses, and the two schemes the same challenges and signatures.
- `hedgedScheme.run_sign`: at the oracle `H`, hedged signing with the nonces `rv` is fresh signing
  with the mask functions `u ↦ H (M.pt (rv c, u))`. `freshScheme.run_sign_congr`: fresh signing
  agrees at two oracles with the same values at the base signer's points and the same honest
  proofs.
- `freshChallenger`, `hopAns`, `saltFreshPair`: **the hedged anonymity challenger and its fresh
  counterpart form a `Challenger.SaltFreshPair`** at the mask oracle's points, with the `Q · k`
  nonces as the hidden salts, when the base signer's oracles and the honest prover read no mask
  point.
- `W1Pts`, `sumOracles`, `sumMask`, `sumMask_pt_injective`, `sumOracles_isPt_not_mem`: the base
  signer's oracles and the mask oracle on the two sides of a sum type, a domain separation at which
  the hypotheses `hM` and `hdisj` of the headlines hold.
- `acceptAll_prove_run_eq`, `queriesOnly_view_eq`, `pubWI_acceptAll`, `card_filter_valid_le`: the
  hypotheses `hPS`, `hV`, `hwi` (at error `0`) and `hC` hold for the accepting proof system, the
  view of queries only and `C` the number of challenges.
- `idealDist`: the coupling error of the fresh-mask signer: the largest distance between the two
  users' refusal-or-public value laws over the valid challenges on supported rings, at a value of
  the oracle at the base signer's points.
- `hedgedScheme.anonAdvantage_le`: **anonymity with hedged signing** for every adversary of the
  game (`t` superposition queries, any oracle view read off the mask oracle's points) and every
  number `Q` of challenges: at most
  `𝔼 (Q · (idealDist + 2εc) + Q · wi (Q · C)) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256))`,
  through the reprogramming hop and the coupling bound for the fresh-mask signer.
- `w1Concrete.anonAdvantage_le`: the same at the concrete primitives of every approved parameter
  set (the fresh-mask signer's correctness error is `0`, `correctWithin_w1BaseSigner`).
- `MaskOracle.ans_eq_of_readsFst`, `map_uniform_fst_split`: for an oracle split
  `sp : Y ≃+ Y₁ × Y₂`, a mask decoding reading only the base component decodes `y` as
  `sp⁻¹ ((sp y).1, 0)`, and uniform mask functions read through their base components are uniform.
- `restrChallenger`, `anonChallenger_eq_restrChallenger`, `restrAns`, `restrChallenger_answersBy`:
  the hedged scheme's challenges answered by the signer on other rings `adm'`, request by request.
- The hop for the hedged challenger on other rings (`restrChallenger … adm' …`) and a split
  oracle: `freshScheme.run_sign_mask_congr` (fresh signing reads the masks through their
  decodings), `freshRestrChallenger` (the fresh scheme on the
  rings `adm'`), `restrHopAns`, `restrAns_eq_restrHopAns`, `saltFreshPairOn` (a
  `Challenger.SaltFreshPairOn` at `sp.toEquiv`, when the mask decoding reads only the base
  component and the honest prover reads the base component only off a set containing the mask
  points), and `gameAdvantage_restrChallenger_le`:
  the bound of `hedgedScheme.anonAdvantage_le` between the runs against
  `restrChallenger … adm' keys false Q` and `… true …`, with `idealDist` on the rings `adm'`.

`MLDSAW1IdealDist.lean` bounds the average of `idealDist` (`expect_idealDist_le`), and
`MLDSAW1AnonQuery.lean` states the anonymity headlines at `w1Concrete`, `w1Scheme44`, `w1Scheme65`
and `w1Scheme87`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature
open scoped ENNReal NNReal BigOperators

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The split of the oracle at the points of the base signer's oracles -/

section Split

variable {prims : Primitives p}

/-- **The points of the base signer's oracles**: the points of the message-representative, the
commitment-hash and the check oracles. -/
def W1Oracles.IsPt (O : W1Oracles X Y p prims Msg N reps) (x : X) : Prop :=
  (∃ a, O.muPt a = x) ∨ (∃ a, O.chPt a = x) ∨ (∃ a, O.gPt a = x)

open Classical in
/-- **The split of the oracle** into its values at the points of the base signer's oracles and its
values off them (`Equiv.piEquivPiSubtypeProd`). -/
noncomputable def W1Oracles.split (O : W1Oracles X Y p prims Msg N reps) :
    (X → Y) ≃ ({x // O.IsPt x} → Y) × ({x // ¬ O.IsPt x} → Y) :=
  Equiv.piEquivPiSubtypeProd O.IsPt fun _ => Y

/-- Two oracles with the same first part agree at the points of the base signer's oracles. -/
theorem W1Oracles.apply_eq_of_split {O : W1Oracles X Y p prims Msg N reps} {H H' : X → Y}
    (h : (O.split H).1 = (O.split H').1) {x : X} (hx : O.IsPt x) : H x = H' x :=
  congrFun h ⟨x, hx⟩

/-- The message-representative oracle read off two oracles with the same first part agrees. -/
theorem W1Oracles.muOrc_eq_of_split {O : W1Oracles X Y p prims Msg N reps} {H H' : X → Y}
    (h : (O.split H).1 = (O.split H').1) : O.muOrc H = O.muOrc H' :=
  funext fun a => congrArg O.muAns (O.apply_eq_of_split h (Or.inl ⟨a, rfl⟩))

/-- The commitment-hash oracle read off two oracles with the same first part agrees. -/
theorem W1Oracles.chOrc_eq_of_split {O : W1Oracles X Y p prims Msg N reps} {H H' : X → Y}
    (h : (O.split H).1 = (O.split H').1) : O.chOrc H = O.chOrc H' :=
  funext fun a => congrArg O.chAns (O.apply_eq_of_split h (Or.inr (Or.inl ⟨a, rfl⟩)))

/-- The check oracle read off two oracles with the same first part agrees. -/
theorem W1Oracles.gOrc_eq_of_split {O : W1Oracles X Y p prims Msg N reps} {H H' : X → Y}
    (h : (O.split H).1 = (O.split H').1) : O.gOrc H = O.gOrc H' :=
  funext fun a => congrArg O.gAns (O.apply_eq_of_split h (Or.inr (Or.inr ⟨a, rfl⟩)))

/-- The commitment hash read off two oracles with the same first part agrees. -/
theorem W1Oracles.hOrc_eq_of_split {O : W1Oracles X Y p prims Msg N reps} {H H' : X → Y}
    (h : (O.split H).1 = (O.split H').1) : O.hOrc H = O.hOrc H' := by
  simp only [W1Oracles.hOrc, O.muOrc_eq_of_split h, O.chOrc_eq_of_split h]

end Split

/-! ### The base signer at an oracle -/

section Run

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]

open Classical in
/-- **The base signer with the ring loop at the oracle `H`**: `none` unless the ring passes the
public check against the check oracle read from `H` and its members' message representatives are
distinct; otherwise the loop's output `loopOut` (at a position of the ring) against the commitment
hash read from `H` and the masks read from the randomness of each call. -/
theorem run_bsign_w1BaseSigner (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) (src : MaskSource X Y p T Msg) (k D : ℕ) [NeZero D]
    {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : ℕ) (m : RMsg)
    (c : (Fin k → src.Rnd) × (Fin k → Fin D)) (H : X → Y) :
    ((w1BaseSigner prims O βmin tol enc (ringLoop prims src O βmin k D) bmsg).bsign sk R i m
        c).run H =
      if RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m) then
        if hi : i < R.1.length then
          loopOut prims βmin sk R ⟨i, hi⟩ (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H))
            (fun c' t => (src.read (c.1 c') (t, (sk.key, (sk.tr, bmsg R m)))).run H) c.2
        else none
      else none := by
  have hg := run_ringCheckProg prims O βmin tol R H
  have hm := run_muDistinctProg prims O R (bmsg R m) H
  simp only [w1BaseSigner, ringLoop, OracleProg.run_bind]
  rcases hg' : (ringCheckProg prims O βmin tol R).run H <;>
    rcases hm' : (muDistinctProg prims O R (bmsg R m)).run H <;>
    simp_all [run_ringLoopProg]

/-- **The base signer with fresh masks reads the oracle only at the points of its oracles**: its
signer, its public value (no query) and its verification agree at two oracles with the same first
part of the split. -/
theorem readsOnly_freshBase [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
    [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    (w1BaseSigner prims O βmin tol enc (freshLoop prims O M βmin k D) bmsg).ReadsOnly
      fun H => (O.split H).1 where
  run_bsign H H' h sk R i m c := by
    refine (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D bmsg sk R i m c
      H).trans (Eq.trans ?_ (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D
        bmsg sk R i m c H').symm)
    rw [O.gOrc_eq_of_split h, O.muOrc_eq_of_split h, O.hOrc_eq_of_split h]
    rfl
  run_pub _ _ _ _ _ := rfl
  bverify_eq H H' h := by
    funext pk bm σ
    simp only [w1BaseSigner, O.hOrc_eq_of_split h]

end Run

/-! ### A proof system on another statement type -/

/-! ### Salts drawn per call, as one vector -/

/-- **The per-call randomness of `Q` requests as one vector of `Q · k` salts**: coins with `k`
salts and other coins `a` per request, and signing coins `b`, as the other coins of each request
and the vector of the salts, the salt of call `c` of request `j` at `finProdFinEquiv (j, c)`. -/
def saltsEquiv (Q k : ℕ) (R A B : Type) :
    (Fin Q → ((Fin k → R) × A) × B) ≃ (Fin Q → A × B) × (Fin (Q * k) → R) where
  toFun ω := (fun j => ((ω j).1.2, (ω j).2),
    fun i => (ω (finProdFinEquiv.symm i).1).1.1 (finProdFinEquiv.symm i).2)
  invFun x j := ((fun c => x.2 (finProdFinEquiv (j, c)), (x.1 j).1), (x.1 j).2)
  left_inv ω := by
    funext j
    simp only [Equiv.symm_apply_apply]
  right_inv x := by
    refine Prod.ext rfl (funext fun i => ?_)
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- The salt of call `c` of request `j`. -/
theorem saltsEquiv_snd_apply {Q k : ℕ} {R A B : Type} (ω : Fin Q → ((Fin k → R) × A) × B)
    (j : Fin Q) (c : Fin k) :
    (saltsEquiv Q k R A B ω).2 (finProdFinEquiv (j, c)) = (ω j).1.1 c := by
  change (ω (finProdFinEquiv.symm (finProdFinEquiv (j, c))).1).1.1
    (finProdFinEquiv.symm (finProdFinEquiv (j, c))).2 = _
  rw [Equiv.symm_apply_apply]

/-! ### Masks read through a split of the oracle's values -/

section MaskSplit

variable {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  {sp : RingSignature.OracleSplit Y Y₁ Y₂}

/-- A decoding reading only the first component decodes `y` as `sp⁻¹ ((sp y).1, 0)`. -/
theorem MaskOracle.ans_eq_of_readsFst {M : MaskOracle X Y p T Msg} (hMsp : M.ReadsFst sp) (y : Y) :
    M.ans y = M.ans (sp.symm ((sp y).1, 0)) :=
  hMsp _ _ (by simp)

variable (sp) in
/-- **The uniform mask functions read through their base components are uniform.** -/
theorem map_uniform_fst_split [Fintype Msg] [DecidableEq Msg] [Fintype Y] [Fintype Y₁] [Fintype Y₂]
    {I : Type} [Fintype I] [DecidableEq I] :
    (PMF.uniformOfFintype (I → MaskPt T Msg → Y)).map
        (fun g i u => (sp (g i u)).1) = PMF.uniformOfFintype (I → MaskPt T Msg → Y₁) := by
  classical
  have : Fintype (I → MaskPt T Msg → Y₂) := inferInstance
  let e : (I → MaskPt T Msg → Y) ≃ (I → MaskPt T Msg → Y₁) × (I → MaskPt T Msg → Y₂) :=
    (Equiv.arrowCongr (Equiv.refl I) ((Equiv.arrowCongr (Equiv.refl _) sp.toEquiv).trans
      (Equiv.arrowProdEquivProdArrow _ _ _))).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  have he : (fun g : I → MaskPt T Msg → Y => fun i u => (sp (g i u)).1) = Prod.fst ∘ e := rfl
  rw [he, ← PMF.map_comp, PMF.map_uniformOfFintype_equiv, PMF.map_fst_uniformOfFintype]

end MaskSplit

/-! ### The hedged and the fresh scheme -/

section Hop

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

/-- The base signer with hedged signing (`w1Base`). -/
abbrev hedgedBase : BaseSigner X Y N (w1BaseT prims Msg RMsg (ringCoins (Bytes 32) k D)) :=
  w1BaseSigner prims O βmin tol enc (hedgedLoop prims O M βmin k D) bmsg

/-- **The base signer with fresh masks**: `w1BaseSigner` with the loop of the fresh source. -/
abbrev freshBase : BaseSigner X Y N (w1BaseT prims Msg RMsg (ringCoins (MaskPt T Msg → Y) k D)) :=
  w1BaseSigner prims O βmin tol enc (freshLoop prims O M βmin k D) bmsg

variable {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]

/-- The hedged scheme (`w1Scheme`). -/
abbrev hedgedScheme : RingScheme X Y N (ofBaseT (w1BaseT prims Msg RMsg (ringCoins (Bytes 32) k D)) TPS) :=
  RingSignature.ofBase (hedgedBase prims O M βmin tol enc k D bmsg) PS adm

/-- **The scheme with fresh masks**: `ofBase` of the fresh base signer, with the proof system `PS`
on the same rings. -/
abbrev freshScheme : RingScheme X Y N (ofBaseT (w1BaseT prims Msg RMsg (ringCoins (MaskPt T Msg → Y) k D)) TPS) :=
  @RingSignature.ofBase X Y N _ _ (freshBase prims O M βmin tol enc k D bmsg)
    (PS)
    adm ‹DecidablePred adm›

variable (n : ℕ)

local notation "Bh" => hedgedBase prims O M βmin tol enc k D bmsg
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm

/-- **Hedged signing is signing with fresh masks read off the oracle**: at the oracle `H`, the
hedged scheme's signer with the nonces `rv` is the fresh scheme's signer whose mask function of
call `c` is `u ↦ H (M.pt (rv c, u))`, the values of the oracle on the slice of the nonce. -/
theorem hedgedScheme.run_sign (kp : (Bh).PK × (Bh).SK) (R : KeyRing (PubKey p prims) N) (m : (Bh).Msg)
    (rv : Fin k → Bytes 32) (uv : Fin k → Fin D) (cp : PS.Coins) (H : X → Y) :
    ((Sh).sign kp R m ((rv, uv), cp)).run H =
      ((Sf).sign kp R m (((fun c u => H (M.pt (rv c, u))), uv), cp)).run H := by
  have hb : ∀ sk i, ((Bh).bsign sk R i m (rv, uv)).run H =
      ((Bf).bsign sk R i m ((fun c u => H (M.pt (rv c, u))), uv)).run H := fun sk i =>
    (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.hedged M) k D bmsg sk R i m (rv, uv)
      H).trans (run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D bmsg sk R i m
        ((fun c u => H (M.pt (rv c, u))), uv) H).symm
  unfold hedgedScheme freshScheme RingSignature.ofBase
  dsimp only
  split_ifs
  · refine (run_signAt_eq (Bh) PS H _ _ R _ m (rv, uv) cp).trans ?_
    refine Eq.trans ?_ (run_signAt_eq (Bf) (PS) H kp.1 kp.2 R _ m
      (((fun c u => H (M.pt (rv c, u))) : Fin k → MaskPt T Msg → Y), uv) cp).symm
    rw [hb]
    rfl
  · rfl

variable (n : ℕ)

/-- **The anonymity challenger of the hedged scheme with the signer on other rings**: the
challenges and signatures of the hedged scheme on the rings `adm`, answered as the anonymity
challenger of experiment `b` does (`anonChallenger`), by the signer of the hedged scheme on the
rings `adm'`. At `adm' = adm` it is the anonymity challenger (`anonChallenger_eq_restrChallenger`).
-/
noncomputable def restrChallenger (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) :
    Quantum.Challenger X Y (RingSignature.AnonRequest (Sh) n) (Sh).Sig where
  Coins := Fin Q → (Sh).SignCoins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := (Sh).q
  respond ω hist c :=
    if h : hist.length < Q then
      if c.Valid keys then
        ((RingSignature.ofBase (Bh) PS adm').sign ((Sh).keyGen (keys (c.user b))) c.ring c.msg
          (ω ⟨hist.length, h⟩)).bind fun o => .pure ⟨o, []⟩
      else .pure ⟨none, []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist c H := by
    split_ifs
    · rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
      exact (RingSignature.ofBase (Bh) PS adm').sign_queries _ _ _ _ H
    · simp
    · simp

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **At `adm' = adm` the challenger is the anonymity challenger** of the hedged scheme. -/
theorem anonChallenger_eq_restrChallenger (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) :
    anonChallenger (Sh) n keys b Q =
      restrChallenger prims O M βmin tol enc k D bmsg PS adm n adm keys b Q :=
  rfl

/-- **The answer of `restrChallenger` to request number `j`**: for `j < Q` and a valid challenge,
the signature of user `b` by the hedged signer on the rings `adm'` with the coins `ω j`; `none`
otherwise. -/
noncomputable def restrAns (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) (ω : Fin Q → (Sh).SignCoins) (H : X → Y) (j : ℕ)
    (c : RingSignature.AnonRequest (Sh) n) : Option (Sh).Sig :=
  if h : j < Q then
    if c.Valid keys then
      ((RingSignature.ofBase (Bh) PS adm').sign ((Sh).keyGen (keys (c.user b))) c.ring c.msg
        (ω ⟨j, h⟩)).run H
    else none
  else none

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **`restrChallenger` answers request by request** by `restrAns`, and reprograms nothing. -/
theorem restrChallenger_answersBy (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) :
    (restrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys b Q).AnswersBy
      (restrAns prims O M βmin tol enc k D bmsg PS adm n adm' keys b Q) := by
  intro ω hist c H hlt
  have hlt' : hist.length < Q := hlt
  simp only [restrChallenger, restrAns, hlt', ↓reduceDIte]
  split_ifs <;> (simp only [OracleProg.run_bind, OracleProg.run_pure]; try rfl)

/-- **The fresh counterpart of the hedged anonymity challenger**: the anonymity challenger of the
fresh scheme, whose challenges and signatures are the hedged scheme's. -/
noncomputable def freshChallenger (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) :
    Quantum.Challenger X Y (RingSignature.AnonRequest (Sh) n) (Sh).Sig :=
  anonChallenger (Sf) n keys b Q

/-- **The answer to request number `j`** from the other coins `c'` and the mask functions `g` of
the `Q · k` calls: for `j < Q` and a valid challenge, the fresh scheme's signature of user `b`
whose call `c` reads the mask function `g (j, c)`; `none` otherwise. -/
noncomputable def hopAns (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ)
    (c' : Fin Q → (Fin k → Fin D) × PS.Coins) (j : ℕ)
    (req : RingSignature.AnonRequest (Sh) n) (g : Fin (Q * k) → MaskPt T Msg → Y) (H : X → Y) :
    Option (Sh).Sig :=
  if hj : j < Q then
    if req.Valid keys then
      ((Sf).sign ((Sf).keyGen (keys (req.user b))) req.ring req.msg
        (((fun c => g (finProdFinEquiv (⟨j, hj⟩, c))), (c' ⟨j, hj⟩).1), (c' ⟨j, hj⟩).2)).run H
    else none
  else none

/-- **Fresh signing reads the oracle only at the base signer's points and the prover's points**:
at two oracles with the same first part of the split at which every honest proof is the same, the
fresh scheme's signer has the same output. -/
theorem freshScheme.run_sign_congr {H H' : X → Y} (hs : (O.split H).1 = (O.split H').1)
    (hPS : ∀ x w c, (PS.prove x w c).run H = (PS.prove x w c).run H')
    (kp : (Bh).PK × (Bh).SK) (R : KeyRing (PubKey p prims) N) (m : (Bh).Msg) (c : (Sf).SignCoins) :
    ((Sf).sign kp R m c).run H = ((Sf).sign kp R m c).run H' := by
  unfold freshScheme RingSignature.ofBase
  dsimp only
  split_ifs
  · refine (run_signAt_eq (Bf) _ H kp.1 kp.2 R _ m c.1 c.2).trans
      (Eq.trans ?_ (run_signAt_eq (Bf) _ H' kp.1 kp.2 R _ m c.1 c.2).symm)
    have key : ∀ {α β : Type} {f g : α → β} {o o' : Option α}, o = o' → (∀ a, f a = g a) →
        o.map f = o'.map g := by
      intro α β f g o o' ho hfg
      subst ho
      rw [funext hfg]
    exact key ((readsOnly_freshBase prims O M βmin tol enc k D bmsg).run_bsign H H' hs _ _ _ _ _)
      fun σ => congrArg _ (hPS _ _ _)
  · rfl

/-- **The hedged anonymity challenger reads the mask oracle at hidden fresh salts**
(`Challenger.SaltFreshPair`): the salts are the `Q · k` nonces of its coins, uniform and
independent (`PMF.pi`); its answer to request `j` is `hopAns` at the mask oracle's values on the
slices of the nonces of request `j`, and it reads the oracle off the mask oracle's points when the
base signer's oracles (`hdisj`) and the honest prover (`hPS`) do; its fresh counterpart is
`freshChallenger`, which answers with uniform mask functions. -/
noncomputable def saltFreshPair (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hPS : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) :
    (anonChallenger (Sh) n keys b Q).SaltFreshPair M.pt
      (PMF.pi fun _ : Fin (Q * k) => PMF.uniformOfFintype (Bytes 32))
      (freshChallenger prims O M βmin tol enc k D bmsg PS adm n keys b Q) where
  Coins' := Fin Q → (Fin k → Fin D) × PS.Coins
  ζ := PMF.uniformOfFintype _
  ans := hopAns prims O M βmin tol enc k D bmsg PS adm n keys b Q
  readsOffRange c' j req g H H' h := by
    unfold hopAns
    split_ifs
    · exact freshScheme.run_sign_congr prims O M βmin tol enc k D bmsg PS adm
        (funext fun x => h x.1 (hdisj x.1 x.2)) (fun x w c => hPS x w c H H' h) _ _ _ _
    · rfl
    · rfl
  dec₀ c := saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins c
  map_dec₀ := by
    change (PMF.uniformOfFintype _).map (saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins) = _
    rw [PMF.map_uniformOfFintype_equiv, PMF.pi_uniformOfFintype]
    exact PMF.uniformOfFintype_prod_eq_bind
  salted c hist req H hlt := by
    have hlt' : hist.length < Q := hlt
    unfold anonChallenger hopAns
    dsimp only
    rw [dite_eq_left_of_eq_true (eq_true hlt'), dite_eq_left_of_eq_true (eq_true hlt')]
    split_ifs with hv
    · rw [OracleProg.run_bind]
      change Quantum.Reply.mk _ _ = Quantum.Reply.mk _ _
      congr 1
      refine (hedgedScheme.run_sign prims O M βmin tol enc k D bmsg PS adm _ _ _
        (c ⟨hist.length, hlt'⟩).1.1 (c ⟨hist.length, hlt'⟩).1.2 (c ⟨hist.length, hlt'⟩).2
        H).trans ?_
      have hg : (fun c₁ => Quantum.slices M.pt H
          ((saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins) c).2
            (finProdFinEquiv (⟨hist.length, hlt'⟩, c₁))) =
          fun c₁ u => H (M.pt ((c ⟨hist.length, hlt'⟩).1.1 c₁, u)) := by
        funext c₁ u
        exact congrArg (fun r => H (M.pt (r, u))) (saltsEquiv_snd_apply c _ c₁)
      rw [hg]
      rfl
    · rfl
  dec₁ c := ((saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).2,
    (saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).1)
  map_dec₁ := by
    let _ : Fintype (MaskPt T Msg → Y) := inferInstance
    let _ : Fintype (Fin (Q * k) → MaskPt T Msg → Y) := inferInstance
    let _ : Fintype (Fin Q → (Fin k → Fin D) × PS.Coins) := inferInstance
    let e : (freshChallenger prims O M βmin tol enc k D bmsg PS adm n keys b Q).Coins ≃
        (Fin (Q * k) → MaskPt T Msg → Y) × (Fin Q → (Fin k → Fin D) × PS.Coins) :=
      (saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins).trans (Equiv.prodComm _ _)
    have : Nonempty (freshChallenger prims O M βmin tol enc k D bmsg PS adm n keys b Q).Coins :=
      ⟨e.symm (Classical.arbitrary _)⟩
    exact (PMF.map_uniformOfFintype_equiv e).trans PMF.uniformOfFintype_prod_eq_bind
  fresh c hist req H hlt := by
    have hlt' : hist.length < Q := hlt
    unfold freshChallenger anonChallenger hopAns
    dsimp only
    simp only [hlt', ↓reduceDIte]
    by_cases hv : req.Valid keys
    · simp only [hv, show AnonRequest.Valid (S := Sf) keys req from hv, ↓reduceIte]
      rw [OracleProg.run_bind, OracleProg.run_pure]
      congr 1
      refine congrArg (fun z : (Sf).SignCoins => OracleProg.run H ((Sf).sign
        ((Sf).keyGen (keys (req.user b))) req.ring req.msg z)) ?_
      exact Prod.ext (Prod.ext (funext fun c₁ => (saltsEquiv_snd_apply c _ c₁).symm) rfl) rfl
    · simp only [hv, show ¬ AnonRequest.Valid (S := Sf) keys req from hv, ↓reduceIte]
      rfl
  Q_eq := rfl

variable [Fintype X] [DecidableEq X]

open Classical in
/-- **The coupling error of the fresh-mask signer** at the users' key coins `keys` and the values
`ω₂` of the oracle at the base signer's points: the largest distance, over the valid challenges on
supported rings and the other values `h₁` of the oracle, between the two users' laws of the
refusal-or-public value of the fresh-mask base signer (`BaseSigner.refusalPubLaw`). -/
noncomputable def idealDist (keys : Fin n → Bytes 32) (ω₂ : {x // O.IsPt x} → Y) : ℝ :=
  (((Finset.univ : Finset ({x // ¬ O.IsPt x} → Y)) ×ˢ
    (Finset.univ.filter fun c : RingSignature.AnonRequest (Sh) n => c.Valid keys ∧ adm c.ring)).sup
      fun q => (⟨PMF.tvDist ((Bf).refusalPubLaw (O.split.symm (ω₂, q.1)) (keys q.2.user₀) q.2.ring
          q.2.msg) ((Bf).refusalPubLaw (O.split.symm (ω₂, q.1)) (keys q.2.user₁) q.2.ring q.2.msg),
        PMF.tvDist_nonneg _ _⟩ : ℝ≥0) : ℝ≥0)

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁` with hedged signing**, for every
anonymity adversary with `t` superposition queries and any oracle view `V` read off the mask
oracle's points (`hV`), and every number `Q` of challenges: the advantage is at most
`𝔼_{keys, ω₂} (Q · (idealDist + 2εc) + Q · wi (Q · C)) + 2 (C(Q k, 2) / 2^256 +
2 t √(Q k / 2^256))`.
The last term is the reprogramming of the mask oracle at the `Q · k` hidden nonces
(`anonAdvantage_le_of_saltFresh_of_pi` with `saltFreshPair`); the first is the coupling bound for
the fresh-mask signer (`abs_detAnonWin_split_sub_le_expect`, through deterministic classical
strategies, `gameAdvantage_runLaw_le_of_det`), with `idealDist` the distance of the two users' laws of the
fresh-mask signer's public value, `wi` the witness-indistinguishability error of the proof system
for the ring relation (`hwi`), `C` a bound on the valid challenges (`hC`) and `εc` the fresh-mask
signer's correctness error (`hcorr`). The hypotheses `hM`, `hdisj` and `hPS` are the domain
separation of the mask oracle from the base signer's oracles and from the honest prover. -/
theorem hedgedScheme.anonAdvantage_le [Nonempty X] [AddGroup Y] (hM : Function.Injective M.pt)
    (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hPS : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    {V : OracleView X Y} (hV : ∀ H H', Quantum.AgreeOffRange M.pt H H' → V.view H = V.view H')
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h))) RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (Bh) adm (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32,
      (Finset.univ.filter fun c : RingSignature.AnonRequest (Sh) n => c.Valid keys).card ≤ C)
    {εc : ℝ≥0} (hcorr : (Bf).CorrectWithin εc) {t : ℕ} (A : AnonAdversary (Sh) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      (𝔼 keys : (Fin n → (Sh).KeyCoins), 𝔼 ω₂ : ({x // O.IsPt x} → Y),
        ((Q : ℝ) * (idealDist prims O M βmin tol enc k D bmsg PS adm n keys ω₂ + 2 * εc) +
          Q * wi (Q * C))) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) := by
  classical
  have hδ : ∀ (_ : Fin (Q * k)) (s : Bytes 32),
      ((PMF.uniformOfFintype (Bytes 32)) s).toReal ≤ (2 ^ 256 : ℝ)⁻¹ := fun _ s => by
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, card_bytes32]
  have hop := anonAdvantage_le_of_saltFresh_of_pi hV A Q
    (fun b keys => saltFreshPair prims O M βmin tol enc k D bmsg PS adm n hdisj hPS keys b Q) hM hδ
  refine hop.trans (add_le_add ?_ le_rfl)
  let inst' : @DecidablePred (KeyRing (PubKey p prims) N) adm := ‹DecidablePred adm›
  have hrel : ∀ H, RingSignature.ringRel (Bf) adm H = RingSignature.ringRel (Bh) adm H :=
    fun H =>
    Set.ext fun _ => ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩
  have hwi' : ∀ ω₂ h₁, PubWI (fun h => (PS).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (Bf) adm (O.split.symm (ω₂, h₁))) wi := fun ω₂ h₁ => by
    rw [hrel]
    exact hwi ω₂ h₁
  have hC' : ∀ keys : Fin n → Bytes 32,
      (Finset.univ.filter fun c : RingSignature.AnonRequest (Sf) n => c.Valid keys).card ≤ C :=
    fun keys => hC keys
  refine (gameAdvantage_runLaw_le_of_det A _ _ (ε := fun keys => 𝔼 ω₂ : ({x // O.IsPt x} → Y),
    ((Q : ℝ) * (idealDist prims O M βmin tol enc k D bmsg PS adm n keys ω₂ + 2 * εc) +
      Q * wi (Q * C) + if True then 0 else 1)) fun keys m s => ?_).trans (le_of_eq ?_)
  · have hw : ∀ b', (𝔼 H, Interaction.winProb (s H).toStrategy ((freshChallenger prims O M βmin
        tol enc k D bmsg PS adm n keys b' Q).classicalAt H) (m H) {p | p.2 = some true}) =
        detAnonWin (S := Sf) keys b' Q m s := fun _ => rfl
    rw [hw, hw]
    refine abs_detAnonWin_split_sub_le_expect (B := Bf) keys Q m _ O.split
      (readsOnly_freshBase prims O M βmin tol enc k D bmsg) hwi' (hC' keys) (fun _ => True)
      (idealDist prims O M βmin tol enc k D bmsg PS adm n keys) (fun _ => NNReal.coe_nonneg _)
      ?_ hcorr
    intro ω₂ _ h₁ c hv ha
    have hmem : (h₁, c) ∈
        ((Finset.univ : Finset ({x // ¬ O.IsPt x} → Y)) ×ˢ
          (Finset.univ.filter fun c : RingSignature.AnonRequest (Sh) n =>
            c.Valid keys ∧ adm c.ring)) :=
      Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv, ha⟩⟩
    let F : ({x // ¬ O.IsPt x} → Y) × RingSignature.AnonRequest (Sh) n → ℝ≥0 := fun q =>
      ⟨PMF.tvDist ((Bf).refusalPubLaw (O.split.symm (ω₂, q.1)) (keys q.2.user₀) q.2.ring q.2.msg)
        ((Bf).refusalPubLaw (O.split.symm (ω₂, q.1)) (keys q.2.user₁) q.2.ring q.2.msg),
        PMF.tvDist_nonneg _ _⟩
    have h := NNReal.coe_le_coe.2 (Finset.le_sup (f := F) hmem)
    exact h
  · simp only [ite_true, add_zero]

/-! ### The reprogramming hop for the signer on other rings and a split oracle -/

section Restr

omit [Fintype X] [DecidableEq X] in
/-- **Fresh signing reads the masks only through their decodings**: the fresh scheme's signer
with mask functions `g` and `g'` whose decoded masks agree has the same output. -/
theorem freshScheme.run_sign_mask_congr (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    {g g' : Fin k → MaskPt T Msg → Y}
    (hg : ∀ c u, M.ans (g c u) = M.ans (g' c u)) (kp : (Bh).PK × (Bh).SK) (R : KeyRing (PubKey p prims) N)
    (m : (Bh).Msg) (uv : Fin k → Fin D) (cp : PS.Coins) (H : X → Y) :
    ((freshScheme prims O M βmin tol enc k D bmsg PS adm').sign kp R m ((g, uv), cp)).run H =
      ((freshScheme prims O M βmin tol enc k D bmsg PS adm').sign kp R m ((g', uv), cp)).run H := by
  have hb : ∀ sk i, ((Bf).bsign sk R i m (g, uv)).run H = ((Bf).bsign sk R i m (g', uv)).run H :=
    fun sk i => by
      erw [run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D bmsg sk R i m (g, uv)
        H, run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D bmsg sk R i m
        (g', uv) H]
      simp only [MaskSource.fresh, OracleProg.run_pure, hg]
  unfold freshScheme RingSignature.ofBase
  dsimp only
  split_ifs
  · refine (run_signAt_eq (Bf) (PS) H kp.1 kp.2 R _ m (g, uv) cp).trans
      (Eq.trans ?_ (run_signAt_eq (Bf) (PS) H kp.1 kp.2 R _ m (g', uv) cp).symm)
    exact congrArg (Option.map _) (hb _ _)
  · rfl

/-- **The fresh counterpart of `restrChallenger`**: the anonymity challenger of the fresh scheme
on the rings `adm'`, whose challenges and signatures are the hedged scheme's. -/
noncomputable def freshRestrChallenger (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) :
    Quantum.Challenger X Y (RingSignature.AnonRequest (Sh) n) (Sh).Sig :=
  anonChallenger (freshScheme prims O M βmin tol enc k D bmsg PS adm') n keys b Q

variable {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [Fintype Y₂]
  (sp : RingSignature.OracleSplit Y Y₁ Y₂)

/-- **The answer to request number `j` from base components of masks**: `hopAns` for the fresh
scheme on the rings `adm'`, whose call `c` reads the mask function `u ↦ sp⁻¹ (g (j, c) u, 0)`. -/
noncomputable def restrHopAns (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ)
    (c' : Fin Q → (Fin k → Fin D) × PS.Coins) (j : ℕ)
    (req : RingSignature.AnonRequest (Sh) n) (g : Fin (Q * k) → MaskPt T Msg → Y₁) (H : X → Y) :
    Option (Sh).Sig :=
  if hj : j < Q then
    if req.Valid keys then
      ((freshScheme prims O M βmin tol enc k D bmsg PS adm').sign
        ((freshScheme prims O M βmin tol enc k D bmsg PS adm').keyGen (keys (req.user b)))
        req.ring req.msg
        (((fun c u => sp.symm (g (finProdFinEquiv (⟨j, hj⟩, c)) u, 0)), (c' ⟨j, hj⟩).1),
          (c' ⟨j, hj⟩).2)).run H
    else none
  else none

omit [Fintype X] [DecidableEq X] [Fintype Y₁] [Fintype Y₂] in
/-- **`restrAns` is `restrHopAns` at the base components of the oracle on the slices** of the
nonces, for a mask decoding reading only the first component. -/
theorem restrAns_eq_restrHopAns (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    (hMsp : M.ReadsFst sp) (keys : Fin n → Bytes 32) (b : Bool)
    (Q : ℕ) (c : Fin Q → (Sh).SignCoins) (H : X → Y) (j : ℕ)
    (req : RingSignature.AnonRequest (Sh) n) :
    restrAns prims O M βmin tol enc k D bmsg PS adm n adm' keys b Q c H j req =
      restrHopAns prims O M βmin tol enc k D bmsg PS adm n sp adm' keys b Q
        (saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins c).1 j req
        (Quantum.slicesOn M.pt sp.toEquiv H
          (saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins c).2)
        H := by
  unfold restrAns restrHopAns
  split_ifs with hj hv
  · refine (hedgedScheme.run_sign prims O M βmin tol enc k D bmsg PS adm' _ _ _
      (c ⟨j, hj⟩).1.1 (c ⟨j, hj⟩).1.2 (c ⟨j, hj⟩).2 H).trans ?_
    refine freshScheme.run_sign_mask_congr prims O M βmin tol enc k D bmsg PS adm' (fun c₁ u => ?_)
      _ _ _ _ _ H
    simp only [Quantum.slicesOn]
    erw [saltsEquiv_snd_apply]
    exact MaskOracle.ans_eq_of_readsFst hMsp _
  · rfl
  · rfl


/-- **The hedged challenger on the rings `adm'` reads the base components of the mask oracle at
hidden fresh salts** (`Challenger.SaltFreshPairOn` at `sp`): the salts are the `Q · k` nonces of
its coins; its answer to request `j` is `restrHopAns` at the base components of the mask oracle on
the slices of the nonces of request `j`, for a mask decoding reading only the base component
(`hMsp`); it reads the base components only off the mask oracle's points when the base signer's
oracles do (`hdisj`) and the honest prover reads the oracle off a set `B` containing them
(`hB`, `hPS`); its fresh counterpart is `freshRestrChallenger`, whose mask functions read through
their base components are uniform. -/
noncomputable def saltFreshPairOn (adm' : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm']
    (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hMsp : M.ReadsFst sp) {Bs : Set X} (hB : Set.range M.pt ⊆ Bs) (hPS : PS.ReadsOff sp Bs)
    (keys : Fin n → Bytes 32) (b : Bool) (Q : ℕ) :
    (restrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys b Q).SaltFreshPairOn M.pt
      sp.toEquiv (PMF.pi fun _ : Fin (Q * k) => PMF.uniformOfFintype (Bytes 32))
      (freshRestrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys b Q) where
  Coins' := Fin Q → (Fin k → Fin D) × PS.Coins
  ζ := PMF.uniformOfFintype _
  ans := restrHopAns prims O M βmin tol enc k D bmsg PS adm n sp adm' keys b Q
  readsOffRange c' j req g H H' h := by
    unfold restrHopAns
    split_ifs
    · exact freshScheme.run_sign_congr prims O M βmin tol enc k D bmsg PS adm'
        (funext fun x => h.1 x.1 (hdisj x.1 x.2))
        (fun x w c => hPS x w c H H' (fun z => h.2 z) fun z hz => h.1 z fun hr => hz (hB hr))
        _ _ _ _
    · rfl
    · rfl
  dec₀ c := saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins c
  map_dec₀ := by
    change (PMF.uniformOfFintype _).map (saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins) = _
    rw [PMF.map_uniformOfFintype_equiv, PMF.pi_uniformOfFintype]
    exact PMF.uniformOfFintype_prod_eq_bind
  salted c hist req H hlt :=
    ((restrChallenger_answersBy prims O M βmin tol enc k D bmsg PS adm n adm' keys b Q) c hist req H
      hlt).trans (congrArg (fun r => Quantum.Reply.mk r [])
        (restrAns_eq_restrHopAns prims O M βmin tol enc k D bmsg PS adm n sp
          adm' hMsp keys b Q c H _ req))
  dec₁ c := ((fun i u => (sp ((saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).2 i
      u)).1), (saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).1)
  map_dec₁ := by
    let _ : Fintype (Fin Q → (Fin k → Fin D) × PS.Coins) := inferInstance
    let e : (freshRestrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys b Q).Coins ≃
        (Fin (Q * k) → MaskPt T Msg → Y) × (Fin Q → (Fin k → Fin D) × PS.Coins) :=
      (saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins).trans (Equiv.prodComm _ _)
    have : Nonempty (freshRestrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys b
        Q).Coins := ⟨e.symm (Classical.arbitrary _)⟩
    change PMF.map ((Prod.map (fun g i u => (sp (g i u)).1) id) ∘ e) (PMF.uniformOfFintype _) = _
    rw [← PMF.map_comp, PMF.map_uniformOfFintype_equiv, PMF.uniformOfFintype_prod_eq_bind,
      PMF.map_bind, ← map_uniform_fst_split sp, Quantum.prodLaw, PMF.bind_map]
    simp only [PMF.map_comp]
    rfl
  fresh c hist req H hlt := by
    have hlt' : hist.length < Q := hlt
    unfold freshRestrChallenger anonChallenger restrHopAns
    dsimp only
    simp only [hlt', ↓reduceDIte]
    by_cases hv : req.Valid keys
    · simp only [hv, show AnonRequest.Valid (S := freshScheme prims O M βmin tol enc k D bmsg PS adm') keys req from hv, ↓reduceIte]
      rw [OracleProg.run_bind, OracleProg.run_pure]
      congr 1
      refine freshScheme.run_sign_mask_congr prims O M βmin tol enc k D bmsg PS adm'
        (fun c₁ u => ?_) _ _ _ _ _ H
      erw [saltsEquiv_snd_apply]
      exact MaskOracle.ans_eq_of_readsFst hMsp _
    · simp only [hv, show ¬ AnonRequest.Valid (S := freshScheme prims O M βmin tol enc k D bmsg PS adm') keys req from hv, ↓reduceIte]
      rfl
  Q_eq := rfl

open Classical in
/-- **The hedged challenger on the rings `adm'` against an anonymity adversary of the hedged
scheme on the rings `adm`**, for an oracle split `sp : Y ≃+ Y₁ × Y₂` with the mask decoding reading
only the base component (`hMsp`), and the honest prover and the oracle view reading the base
component only off a set `B` containing the mask oracle's points (`hB`, `hPS`, `hV`): for every
adversary with `t` superposition queries and every number `Q` of challenges, the advantage
between the runs against `restrChallenger … adm' keys false Q` and `… true …` is at most
`𝔼_{keys, ω₂} (Q · (idealDist + 2εc) + Q · wi (Q · C)) + 2 (C(Q k, 2) / 2^256 +
2 t √(Q k / 2^256))`, with `idealDist` of the scheme on the rings `adm'`, `wi` the
witness-indistinguishability error of the proof system for the ring relation on `adm'` (`hwi`),
`C` a bound on the valid challenges (`hC`) and `εc` the fresh-mask signer's correctness error
(`hcorr`). The last term is the reprogramming of the base components of the mask oracle at the
`Q · k` hidden nonces (`gameAdvantage_runLaw_le_of_saltFreshOn` with `saltFreshPairOn`); the
first is the coupling bound for the fresh-mask signer on `adm'`, as in
`hedgedScheme.anonAdvantage_le`. -/
theorem gameAdvantage_restrChallenger_le [Nonempty X] (adm' : KeyRing (PubKey p prims) N → Prop)
    [DecidablePred adm'] (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hMsp : M.ReadsFst sp) {B : Set X} (hB : Set.range M.pt ⊆ B) (hPS : PS.ReadsOff sp B)
    {V : OracleView X Y} (hV : V.ReadsOff sp B) {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h))) RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (Bh) adm' (O.split.symm (ω₂, h₁))) wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS adm') n =>
        c.Valid keys).card ≤ C)
    {εc : ℝ≥0} (hcorr : (Bf).CorrectWithin εc) {t : ℕ} (A : AnonAdversary (Sh) n V t) (Q : ℕ) :
    gameAdvantage (runLaw (fun keys H => A (keys, V.view H))
        (fun keys => restrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys false Q))
      (runLaw (fun keys H => A (keys, V.view H))
        (fun keys => restrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys true Q))
      anonAccepts ≤
      (𝔼 keys : (Fin n → (Sh).KeyCoins), 𝔼 ω₂ : ({x // O.IsPt x} → Y),
        ((Q : ℝ) * (idealDist prims O M βmin tol enc k D bmsg PS adm' n keys ω₂ + 2 * εc) +
          Q * wi (Q * C))) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) := by
  classical
  have hδ : ∀ (_ : Fin (Q * k)) (s : Bytes 32),
      ((PMF.uniformOfFintype (Bytes 32)) s).toReal ≤ (2 ^ 256 : ℝ)⁻¹ := fun _ s => by
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, card_bytes32]
  have hacc : (anonAccepts : Set ((Fin n → (Sh).KeyCoins) × (X → Y) ×
      Option (Bool × List (Quantum.HistoryEntry (AnonRequest (Sh) n) (Sh).Sig)))) =
        RunOutIn {true} := by
    ext x
    simp [anonAccepts, RunOutIn]
  have hop := gameAdvantage_runLaw_le_of_saltFreshOn (fun keys H => A (keys, V.view H))
    (fun keys H H' h => by rw [hV H H' (fun z => h.2 z) fun z hz => h.1 z fun hr => hz (hB hr)])
    (fun keys => saltFreshPairOn prims O M βmin tol enc k D bmsg PS adm n sp adm' hdisj hMsp hB hPS
      keys false Q)
    (fun keys => saltFreshPairOn prims O M βmin tol enc k D bmsg PS adm n sp adm' hdisj hMsp hB hPS
      keys true Q) hM (Quantum.toReal_pi_exists_eq_le _ hδ) {true}
  rw [← hacc] at hop
  have hcoll := Quantum.toReal_pi_not_injective_le _ hδ
  refine hop.trans ?_
  suffices hdet : gameAdvantage (runLaw (fun keys H => A (keys, V.view H))
        (fun keys => freshRestrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys false
          Q))
      (runLaw (fun keys H => A (keys, V.view H))
        (fun keys => freshRestrChallenger prims O M βmin tol enc k D bmsg PS adm n adm' keys true
          Q))
      anonAccepts ≤
      (𝔼 keys : (Fin n → (Sh).KeyCoins), 𝔼 ω₂ : ({x // O.IsPt x} → Y),
        ((Q : ℝ) * (idealDist prims O M βmin tol enc k D bmsg PS adm' n keys ω₂ + 2 * εc) +
          Q * wi (Q * C))) by
    have h2 : 0 ≤ (2 : ℝ) * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹) := by positivity
    nlinarith
  let inst' : @DecidablePred (KeyRing (PubKey p prims) N) adm' := ‹DecidablePred adm'›
  have hrel : ∀ H, RingSignature.ringRel (Bf) adm' H = RingSignature.ringRel (Bh) adm' H :=
    fun H =>
    Set.ext fun _ => ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩
  have hwi' : ∀ ω₂ h₁, PubWI (fun h => (PS).proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (Bf) adm' (O.split.symm (ω₂, h₁))) wi := fun ω₂ h₁ => by
    rw [hrel]
    exact hwi ω₂ h₁
  have hC' : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (freshScheme prims O M βmin tol enc k D bmsg PS adm') n =>
        c.Valid keys).card ≤ C :=
    fun keys => hC keys
  refine (gameAdvantage_runLaw_le_of_det A _ _ (ε := fun keys => 𝔼 ω₂ : ({x // O.IsPt x} → Y),
    ((Q : ℝ) * (idealDist prims O M βmin tol enc k D bmsg PS adm' n keys ω₂ + 2 * εc) +
      Q * wi (Q * C) + if True then 0 else 1)) fun keys m s => ?_).trans (le_of_eq ?_)
  · have hw : ∀ b', (𝔼 H, Interaction.winProb (s H).toStrategy ((freshRestrChallenger prims O M
        βmin tol enc k D bmsg PS adm n adm' keys b' Q).classicalAt H) (m H)
          {p | p.2 = some true}) =
        detAnonWin (S := freshScheme prims O M βmin tol enc k D bmsg PS adm') keys b' Q m
          s := fun _ => rfl
    rw [hw, hw]
    refine abs_detAnonWin_split_sub_le_expect (B := Bf) keys Q m _ O.split
      (readsOnly_freshBase prims O M βmin tol enc k D bmsg) hwi' (hC' keys) (fun _ => True)
      (idealDist prims O M βmin tol enc k D bmsg PS adm' n keys) (fun _ => NNReal.coe_nonneg _)
      ?_ hcorr
    intro ω₂ _ h₁ c hv ha
    have hmem : (h₁, c) ∈
        ((Finset.univ : Finset ({x // ¬ O.IsPt x} → Y)) ×ˢ
          (Finset.univ.filter fun c : RingSignature.AnonRequest
            (hedgedScheme prims O M βmin tol enc k D bmsg PS adm') n =>
            AnonRequest.Valid (S := hedgedScheme prims O M βmin tol enc k D bmsg PS adm') keys c ∧
              adm' c.ring)) :=
      Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv, ha⟩⟩
    let F : ({x // ¬ O.IsPt x} → Y) ×
        RingSignature.AnonRequest (hedgedScheme prims O M βmin tol enc k D bmsg PS adm') n → ℝ≥0 :=
      fun q =>
      ⟨PMF.tvDist ((Bf).refusalPubLaw (O.split.symm (ω₂, q.1)) (keys q.2.user₀) q.2.ring q.2.msg)
        ((Bf).refusalPubLaw (O.split.symm (ω₂, q.1)) (keys q.2.user₁) q.2.ring q.2.msg),
        PMF.tvDist_nonneg _ _⟩
    refine le_of_le_of_eq (NNReal.coe_le_coe.2 (Finset.le_sup (f := F) hmem)) ?_
    unfold idealDist
    congr
  · simp only [ite_true, add_zero]

end Restr

end Hop

/-! ### Domain separation by a sum type -/

section Sum

variable {prims : Primitives p}

/-- **The points of the base signer's oracles**: message points, commitment-hash points and
check-oracle points, as one sum type. -/
abbrev W1Pts (p : Params) (prims : Primitives p) (Msg : Type) (N reps : ℕ) : Type :=
  (Bytes 64 × Msg) ⊕ ((Bytes 64 × BucketVec p) ⊕ (KeyRing (PubKey p prims) N × Fin N × Fin reps))

/-- The points of the base signer's oracles are finite, as one registered instance, so that
instance search for functions on them stays within its size bound. -/
instance instFintypeW1Pts [Fintype Msg] [Fintype prims.Power2High] [DecidableEq prims.Power2High] :
    Fintype (W1Pts p prims Msg N reps) :=
  inferInstanceAs (Fintype ((Bytes 64 × Msg) ⊕
    ((Bytes 64 × BucketVec p) ⊕ (KeyRing (PubKey p prims) N × Fin N × Fin reps))))

/-- The points of the base signer's oracles have decidable equality (`instFintypeW1Pts`). -/
instance instDecidableEqW1Pts [DecidableEq Msg] [DecidableEq prims.Power2High] :
    DecidableEq (W1Pts p prims Msg N reps) :=
  inferInstanceAs (DecidableEq ((Bytes 64 × Msg) ⊕
    ((Bytes 64 × BucketVec p) ⊕ (KeyRing (PubKey p prims) N × Fin N × Fin reps))))

/-- **The base signer's oracles on the left of a sum type** `W1Pts ⊕ (Bytes 32 × MaskPt T Msg)`,
with the given decodings of the values. -/
def sumOracles (muAns : Y → Bytes 64) (chAns gAns : Y → CommitHashBytes p) :
    W1Oracles (W1Pts p prims Msg N reps ⊕ (Bytes 32 × MaskPt T Msg)) Y p prims Msg N reps where
  muPt a := .inl (.inl a)
  muAns := muAns
  chPt a := .inl (.inr (.inl a))
  chAns := chAns
  gPt a := .inl (.inr (.inr a))
  gAns := gAns

/-- **The mask oracle on the right of the sum type**, with the given decoding of the values. -/
def sumMask (ans : Y → MaskBox p) :
    MaskOracle (W1Pts p prims Msg N reps ⊕ (Bytes 32 × MaskPt T Msg)) Y p T Msg :=
  ⟨Sum.inr, ans⟩

/-- **The mask oracle on the sum type is injective**: the hypothesis `hM` of the anonymity
headlines holds. -/
theorem sumMask_pt_injective (ans : Y → MaskBox p) :
    Function.Injective (sumMask (prims := prims) (N := N) (reps := reps) (T := T) (Msg := Msg)
      ans).pt :=
  Sum.inr_injective

/-- **The base signer's oracles on the sum type read no mask point**: the hypothesis `hdisj` of the
anonymity headlines holds. -/
theorem sumOracles_isPt_not_mem (muAns : Y → Bytes 64) (chAns gAns : Y → CommitHashBytes p)
    (ans : Y → MaskBox p) :
    ∀ x, (sumOracles (prims := prims) (N := N) (reps := reps) (T := T) muAns chAns gAns).IsPt x →
      x ∉ Set.range (sumMask (prims := prims) (N := N) (reps := reps) (T := T) (Msg := Msg)
        ans).pt := by
  rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩) ⟨b, hb⟩ <;> simp [sumMask, sumOracles] at hb

end Sum

/-! ### Satisfiability of the remaining hypotheses -/

section Satisfiable

/-- **A proof system reading no oracle satisfies `hPS`**: the accepting proof system's proofs agree
at any two oracles. -/
theorem acceptAll_prove_run_eq {S U Stmt Wit : Type} (emb : S × U → X) :
    ∀ x w c (H H' : X → Y), Quantum.AgreeOffRange emb H H' →
      ((ProofSystem.acceptAll X Y Stmt Wit).prove x w c).run H =
        ((ProofSystem.acceptAll X Y Stmt Wit).prove x w c).run H' :=
  fun _ _ _ _ _ _ => rfl

/-- **The view of queries only satisfies `hV`**: it hands out nothing. -/
theorem queriesOnly_view_eq {S U : Type} (emb : S × U → X) :
    ∀ H H' : X → Y, Quantum.AgreeOffRange emb H H' →
      (OracleView.queriesOnly X Y).view H = (OracleView.queriesOnly X Y).view H' :=
  fun _ _ _ => rfl

/-- **Witness indistinguishability of the accepting proof system** at error `0`
(`PubWI.of_witness_indep`): the hypothesis `hwi` holds for it at every oracle law and relation. -/
theorem pubWI_acceptAll [Fintype X] [Fintype Y] [Nonempty Y] {Stmt Wit Pub Ω : Type} [Fintype Ω]
    [Nonempty Ω] (ψ : Ω → X → Y) (pubOf : Stmt → Pub) (rel : Set (Stmt × Wit)) :
    PubWI (fun h => (ProofSystem.acceptAll X Y Stmt Wit).proofLaw (ψ h)) pubOf rel fun _ => 0 :=
  PubWI.of_witness_indep pubOf rel fun _ _ _ _ => rfl

/-- **Every scheme has at most `card` valid challenges**: the hypothesis `hC` holds at `C` the
number of challenges. -/
theorem card_filter_valid_le {TS : RingTypes} {S : RingScheme X Y N TS} {n : ℕ} (keys : Fin n → S.KeyCoins) :
    (Finset.univ.filter fun c : RingSignature.AnonRequest S n => c.Valid keys).card ≤
      Fintype.card (RingSignature.AnonRequest S n) :=
  Finset.card_filter_le _ _

end Satisfiable

/-! ### The headlines at the concrete primitives -/

section Concrete

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps} {M : MaskOracle X Y p T Msg}
  {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm] {n : ℕ}

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁` at the concrete primitives** of an
approved parameter set (`hedgedScheme.anonAdvantage_le` with the fresh-mask signer's correctness
error `0`, `correctWithin_w1BaseSigner`): for every anonymity adversary with `t` superposition
queries, any oracle view read off the mask oracle's points, and every number `Q` of challenges,
the advantage is at most
`𝔼_{keys, ω₂} (Q · idealDist + Q · wi (Q · C)) + 2 (C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256))`.
`expect_idealDist_le` (`MLDSAW1IdealDist.lean`) bounds the average of `idealDist`. -/
theorem w1Concrete.anonAdvantage_le (hp : p.isApproved) (hM : Function.Injective M.pt)
    (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hPS : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    {V : OracleView X Y} (hV : ∀ H H', Quantum.AgreeOffRange M.pt H H' → V.view H = V.view H')
    {wi : ℕ → ℝ}
    (hwi : ∀ ω₂ h₁, PubWI (fun h => PS.proofLaw (O.split.symm (ω₂, h)))
      RingSignature.RingStmtOf.pub
      (RingSignature.ringRel (w1ConcreteBase p O M βmin tol k D bmsg) adm (O.split.symm (ω₂, h₁)))
      wi)
    {C : ℕ} (hC : ∀ keys : Fin n → Bytes 32, (Finset.univ.filter fun c :
      RingSignature.AnonRequest (w1Concrete p O M βmin tol k D bmsg PS adm) n =>
        c.Valid keys).card ≤ C)
    {t : ℕ} (A : AnonAdversary (w1Concrete p O M βmin tol k D bmsg PS adm) n V t) (Q : ℕ) :
    anonAdvantage A Q ≤
      (𝔼 keys : (Fin n → (w1Concrete p O M βmin tol k D bmsg PS adm).KeyCoins),
        𝔼 ω₂ : ({x // O.IsPt x} → Y),
        ((Q : ℝ) * idealDist (concretePrimitivesKeyGen p) O M βmin tol (concreteEnc p) k D bmsg
          PS adm n keys ω₂ + Q * wi (Q * C))) +
        2 * ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) := by
  have h := hedgedScheme.anonAdvantage_le (concretePrimitivesKeyGen p) O M βmin tol
    (concreteEnc p) k D bmsg PS adm n hM hdisj hPS hV hwi hC
    (correctWithin_w1BaseSigner _ (signingLaws_concreteKeyGen p hp) (verifyLaws_concreteKeyGen hp)
      (concreteEnc_highBitsVec_keyGen hp) (fun seed => keyGenFromSeed_s2_bounded hp seed)
      (MaskSource.fresh M) O βmin tol k D bmsg) A Q
  simpa only [NNReal.coe_zero, mul_zero, add_zero] using h

end Concrete

end GordieHowe.Ring.MLDSAW1
