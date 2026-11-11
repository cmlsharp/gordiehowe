-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.StrongForger
public import GordieHowe.Model.Signature.MultiUser

@[expose] public section

/-!
# The signature assumptions of the earlier interface in the new one

How the base-scheme definitions of the earlier ring interface (`Ring.SigScheme`,
`GordieHowe/Applications/Ring/Scheme.lean`, with the forgers of `RelayForger.lean` and
`StrongForger.lean`) relate to the assumption library of `GordieHowe/Model/Signature/`.

- `SigScheme.toBaseSigner Sch bind`: the base signer of an earlier scheme with the base-message
  map `bind`: `bsign` signs `bind R m` with `signWith` (it reads the ring only through `bind` and
  never refuses), `ssign` signs a base message, verification and public values are the scheme's and
  read no oracle.
- Each earlier property gives the new one: `correctWithin_toBaseSigner`,
  `stdCorrectWithin_toBaseSigner` (from `SigScheme.CorrectWithin`), `stdRefuseWithin_toBaseSigner`,
  `refuseWithin_toBaseSigner` (refusal `0`), `pubOfCoins_toBaseSigner` (from
  `SigScheme.PubOfCoins`), `sigGivenPubLe_toBaseSigner` (from `SigScheme.SigGivenPubLe`; the two
  events are equal).
- The winning conditions are the same: `forges_iff_baseForgery` (`Signature.Forges` at a history is
  `Ring.BaseForgery`, `GordieHowe/Applications/Ring/Games.lean`, at the history's corruptions and
  signing requests) and `sigStrongForges_iff_strongForgery` (`Signature.SigStrongForges` is
  `Ring.StrongForgery` at the history's corruptions and returned signatures). The success of a
  forger of `RelayForger.lean` or `StrongForger.lean` (`RelayForger.success`,
  `SignRelayForger.success`) is the probability of these conditions for a forger of another form:
  a classical relay over the base oracles (`BaseRequest`, which `muRequestEquiv` identifies with the
  requests of `Signature.SignOracle.std`) followed by a compressed-oracle extraction, not an
  adversary of the interactive model. The strong game of the new library with pair freshness
  (`Signature.muSufProb`) bounds the one with stream A's freshness (`muSufSigProb_le_muSufProb`).
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature GordieHowe.Signature
open scoped ENNReal

variable (X Y : Type) (N : ℕ) (Sch : SigScheme) {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

/-- The types of `Sch.toBaseSigner`: the keys, messages, signatures, public values and signing coins
of `Sch`, with the ring messages `RMsg`. -/
abbrev SigScheme.baseT (RMsg : Type) : BaseTypes where
  PK := Sch.PK
  SK := Sch.SK
  KeyCoins := Sch.KeyCoins
  Msg := RMsg
  BMsg := Sch.Msg
  BSig := Sch.Sig
  Pub := Sch.Pub
  Coins := Sch.SignCoins

/-- **The base signer of an earlier scheme** with the base-message map `bind`: `bsign` signs
`bind R m` with `signWith` at the drawn coins (never refusing; the ring read only through `bind`),
`ssign` signs a base message, verification and the public value are the scheme's. No oracle is
read. -/
def SigScheme.toBaseSigner (bind : List Sch.PK → RMsg → Sch.Msg) : BaseSigner X Y N (Sch.baseT RMsg) where
  keyGen := Sch.keyGen
  bmsg R m := bind R.1 m
  q := 0
  bsign sk R _ m c := .pure (some (Sch.signWith sk (bind R.1 m) c))
  bsign_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign sk bm c := .pure (some (Sch.signWith sk bm c))
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ := Sch.verify
  qPub := 0
  pub _ σ := .pure (Sch.pub σ)
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

variable [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [Nonempty Sch.SignCoins]

variable {X Y N Sch} {bind : List Sch.PK → RMsg → Sch.Msg}

omit [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] in
/-- **The earlier correctness error is the new one** of the ring-aware signer. -/
theorem correctWithin_toBaseSigner {ε : ℝ≥0∞} (h : Sch.CorrectWithin ε) :
    (Sch.toBaseSigner X Y N bind).CorrectWithin ε := by
  intro H kc R i _ m
  refine (PMF.toOuterMeasure_mono _ fun c hc => ?_).trans (h kc (bind R.1 m))
  obtain ⟨⟨σ, hσ, hv⟩, -⟩ := hc
  have hσ' : Sch.signWith (Sch.sk kc) (bind R.1 m) c = σ := Option.some.inj hσ
  change Sch.verify (Sch.pk kc) (bind R.1 m) σ = false at hv
  change Sch.verify (Sch.pk kc) (bind R.1 m) (Sch.signWith (Sch.sk kc) (bind R.1 m) c) ≠ true
  rw [hσ', hv]
  exact Bool.false_ne_true

omit [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] in
/-- **The earlier correctness error is the new one** of the ordinary signer. -/
theorem stdCorrectWithin_toBaseSigner {ε : ℝ≥0∞} (h : Sch.CorrectWithin ε) :
    (Sch.toBaseSigner X Y N bind).StdCorrectWithin ε := by
  intro H kc bm
  refine (PMF.toOuterMeasure_mono _ fun c hc => ?_).trans (h kc bm)
  obtain ⟨⟨σ, hσ, hv⟩, -⟩ := hc
  have hσ' : Sch.signWith (Sch.sk kc) bm c = σ := Option.some.inj hσ
  change Sch.verify (Sch.pk kc) bm σ = false at hv
  change Sch.verify (Sch.pk kc) bm (Sch.signWith (Sch.sk kc) bm c) ≠ true
  rw [hσ', hv]
  exact Bool.false_ne_true

omit [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] in
/-- The ordinary signer of an earlier scheme never refuses. -/
theorem stdRefuseWithin_toBaseSigner : (Sch.toBaseSigner X Y N bind).StdRefuseWithin 0 := by
  intro H kc bm
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  have h : (some (Sch.signWith (Sch.sk kc) bm c) : Option Sch.Sig) = none := hc
  exact Option.some_ne_none _ h

/-- The ring-aware signer of an earlier scheme never refuses. -/
theorem refuseWithin_toBaseSigner [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (adm : KeyRing Sch.PK N → Prop) : (Sch.toBaseSigner X Y N bind).RefuseWithin adm 0 := by
  intro r hr s m
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun d _ hd => ?_
  exact Option.some_ne_none _ hd.2

omit [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [Nonempty Sch.SignCoins] in
/-- **Public values from coins in the earlier sense give them in the new one.** -/
theorem pubOfCoins_toBaseSigner {pubOf : Sch.SignCoins → Sch.Pub} (h : Sch.PubOfCoins pubOf) :
    (Sch.toBaseSigner X Y N bind).PubOfCoins pubOf := by
  intro H kc R i _ m c σ hσ
  have hσ' : Sch.signWith (Sch.sk kc) (bind R.1 m) c = σ := Option.some.inj hσ
  change Sch.pub σ = pubOf c
  rw [← hσ']
  exact h kc (bind R.1 m) c

omit [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] in
/-- **The earlier min-entropy bound is the new one**: the events of the two definitions are
equal. -/
theorem sigGivenPubLe_toBaseSigner {γ : ℝ≥0∞} (h : Sch.SigGivenPubLe γ) :
    (Sch.toBaseSigner X Y N bind).SigGivenPubLe γ := by
  intro H kc R i _ m y σ
  have h1 : (Set.ofPred fun c : Sch.SignCoins =>
      (some (Sch.signWith (Sch.sk kc) (bind R.1 m) c) : Option Sch.Sig) = some σ ∧
        Sch.pub σ = y) =
      {c | Sch.signWith (Sch.sk kc) (bind R.1 m) c = σ ∧
        Sch.pub (Sch.signWith (Sch.sk kc) (bind R.1 m) c) = y} := by
    ext c
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hc, hy⟩
      have hc' := Option.some.inj hc
      exact ⟨hc', hc' ▸ hy⟩
    · rintro ⟨hc, hy⟩
      exact ⟨congrArg some hc, hc ▸ hy⟩
  have h2 : (Set.ofPred fun c : Sch.SignCoins =>
      ∃ σ', (some (Sch.signWith (Sch.sk kc) (bind R.1 m) c) : Option Sch.Sig) = some σ' ∧
        Sch.pub σ' = y) =
      {c | Sch.pub (Sch.signWith (Sch.sk kc) (bind R.1 m) c) = y} := by
    ext c
    simp
  change (PMF.uniformOfFintype Sch.SignCoins).toOuterMeasure (Set.ofPred fun c : Sch.SignCoins =>
      (some (Sch.signWith (Sch.sk kc) (bind R.1 m) c) : Option Sch.Sig) = some σ ∧
        Sch.pub σ = y) ≤
    γ * (PMF.uniformOfFintype Sch.SignCoins).toOuterMeasure (Set.ofPred fun c : Sch.SignCoins =>
      ∃ σ', (some (Sch.signWith (Sch.sk kc) (bind R.1 m) c) : Option Sch.Sig) = some σ' ∧
        Sch.pub σ' = y)
  rw [h1, h2]
  exact h kc (bind R.1 m) y σ

/-! ### The winning conditions -/

variable {n : ℕ} {O : SignOracle (Sch.toBaseSigner X Y N bind).core}

omit [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [Nonempty Sch.SignCoins] in
/-- **`Signature.Forges` is `Ring.BaseForgery`** at the history's corruptions and signing
requests. -/
theorem forges_iff_baseForgery {keys : Fin n → Sch.KeyCoins} {H : X → Y}
    {f : Sch.PK × Sch.Msg × Sch.Sig} {hist : MUHist O n} :
    Forges (B := (Sch.toBaseSigner X Y N bind).core) keys H f hist ↔
      BaseForgery keys (Corrupted hist) (Signed hist) f :=
  ⟨fun h => ⟨h.verify_eq, h.exists_user⟩, fun h => ⟨h.verify_eq, h.exists_user⟩⟩

omit [DecidableEq Sch.PK] [Fintype Sch.KeyCoins] [Nonempty Sch.KeyCoins] [Fintype Sch.SignCoins]
  [Nonempty Sch.SignCoins] in
/-- **`Signature.SigStrongForges` is `Ring.StrongForgery`** at the history's corruptions and
returned signatures. -/
theorem sigStrongForges_iff_strongForgery {keys : Fin n → Sch.KeyCoins} {H : X → Y}
    {f : Sch.PK × Sch.Msg × Sch.Sig} {hist : MUHist O n} :
    SigStrongForges (B := (Sch.toBaseSigner X Y N bind).core) keys H f hist ↔
      StrongForgery keys (Corrupted hist) (ReturnedSig hist) f :=
  ⟨fun h => ⟨h.verify_eq, h.exists_user⟩, fun h => ⟨h.verify_eq, h.exists_user⟩⟩

variable (X Y N bind n) in
/-- **The requests of the ordinary signing oracle's game are the earlier base requests**
(`BaseRequest`: public key, signature on a message, corruption). -/
def muRequestEquiv :
    MURequest (SignOracle.std (Sch.toBaseSigner X Y N bind).core) n ≃ BaseRequest Sch n where
  toFun
    | .publicKey i => .publicKey i
    | .sign i bm => .sign i bm
    | .corrupt i => .corrupt i
  invFun
    | .publicKey i => .publicKey i
    | .sign i bm => .sign i bm
    | .corrupt i => .corrupt i
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

variable (X Y N bind) in
/-- **The replies of the multi-user game are the earlier base replies.** -/
def muResponseEquiv : MUResponse (Sch.toBaseSigner X Y N bind).core ≃ BaseResponse Sch where
  toFun
    | .publicKey pk => .publicKey pk
    | .signature σ => .signature σ
    | .keyCoins kc => .keyCoins kc
  invFun
    | .publicKey pk => .publicKey pk
    | .signature σ => .signature σ
    | .keyCoins kc => .keyCoins kc
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

end GordieHowe.Ring
