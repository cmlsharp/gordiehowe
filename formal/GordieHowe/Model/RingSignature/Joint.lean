-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Base
public import GordieHowe.Model.RingSignature.Unforgeability

@[expose] public section

/-!
# Joint-security unforgeability

A named strengthening of BKM06 Definition 7 for the ring signatures `ofBase B PS adm` whose users
also use their keys in the base scheme: the unforgeability game of `Unforgeability.lean` with the
base scheme's ordinary signer as its side oracle (`baseSide`). A request `sideSign i bm` is
answered by `B.ssign` of user `i` on the base message `bm`; a forgery on `(R*, m*)` is not fresh if
a member of `R*` signed `bmsg R* m*` ordinarily.

- `baseSide B PS adm`: the side oracle: base messages, base signatures, `ssign` with the base part
  of the signing coins, and `Covers bm R m := bm = bmsg R m`; `baseSide_sign`: its signer.
- `JointAdversary`, `jointForgeProb`: the adversaries and the forgery probability.
- Sanity: `sideCovered_baseSide_iff` (freshness excludes exactly the members' ordinary signatures on
  the forgery's base message), `covers_unique` (for a base message that binds the ring, an ordinary
  signature covers at most one ring and message), `jointForgeProb_le_one`.

## Source and scope

This is the joint-security setting of Haber–Pinkas ("Securely Combining Public-Key
Cryptosystems", CCS 2001, `CCS:HabPin01`) and Paterson–Schuldt–Stam–Thomson ("On the Joint Security
of Encryption and Signature, Revisited", ASIACRYPT 2011, `AC:PSST11`): one key pair used by two
schemes, here the ring signature and its base signature scheme.

There is no such game in BKM06. It is BKM06 Definition 7 (ePrint 2005/304, p. 7) plus the signing
oracle of the base scheme's own unforgeability game (EUF-CMA, Goldwasser–Micali–Rivest, SIAM J.
Comput. 17(2), 1988) on the same keys, the setting of a user who signs with one key both in rings
and in the base scheme. A ring-binding base message (`bmsg R m = m ‖ encode R`, BKM06 section 5)
keeps the two uses apart; for converted signatures (`bmsg R m = m`) an ordinary signature by a
member on `m` gives a ring signature on `(R, m)` for every ring holding the member, and
`Covers` then excludes exactly those forgeries.
-/

namespace GordieHowe.RingSignature

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  (B : BaseSigner X Y N T RMsg) {TPS : PSTypes} (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS)
  (adm : KeyRing B.PK N → Prop) [DecidablePred adm]

variable [DecidableEq T.PK]

/-- **The base scheme's ordinary signer as the side oracle of `ofBase`**: user `i`'s base signature
`ssign` on a base message, with the base part of the request's signing coins; a member's ordinary
signature on `bm` covers the rings and messages whose base message is `bm`. -/
@[reducible] def baseSide : SideOracle (ofBase B PS adm) where
  BMsg := B.BMsg
  BSig := B.BSig
  q := B.q
  sign kp bm c := B.ssign kp.sk bm c.base
  sign_queries kp bm c := B.ssign_queries kp.sk bm c.base
  Covers bm R m := bm = B.bmsg R m

/-- The side signer of `baseSide` is the base signer's ordinary signer at the base part of the
coins. -/
theorem baseSide_sign (kp : Signature.KeyPair (ofBase B PS adm).PK (ofBase B PS adm).SK)
    (bm : (baseSide B PS adm).BMsg) (c : (ofBase B PS adm).SignCoins) :
    (baseSide B PS adm).sign kp bm c = B.ssign kp.sk bm c.base :=
  rfl

/-- **A member's ordinary signature covers exactly the forgery's base message**: in the joint-security
game, a side request covers `(R, m)` when a member of `R` was asked to sign `bmsg R m`. -/
theorem sideCovered_baseSide_iff {n : ℕ} {keys : Fin n → B.KeyCoins}
    {hist : UnforgeHist n (baseSide B PS adm)} {R : KeyRing B.PK N} {m : B.Msg} :
    SideCovered keys hist R m ↔
      ∃ e ∈ hist, ∃ i, e.request = .sideSign i (B.bmsg R m) ∧ (ofBase B PS adm).pk (keys i) ∈ R.1 := by
  constructor
  · rintro ⟨e, he, i, bm, hr, hmem, hc⟩
    exact ⟨e, he, i, hc ▸ hr, hmem⟩
  · rintro ⟨e, he, i, hr, hmem⟩
    exact ⟨e, he, i, B.bmsg R m, hr, hmem, rfl⟩

/-- **A ring-binding base message makes each ordinary signature cover at most one ring and
message.** -/
theorem covers_unique (hbind : B.BindsRing) {bm : B.BMsg} {R R' : KeyRing B.PK N}
    {m m' : B.Msg} (h : (baseSide B PS adm).Covers bm R m)
    (h' : (baseSide B PS adm).Covers bm R' m') : R = R' ∧ m = m' :=
  hbind R R' m m' (h.symm.trans h')

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof]

variable [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BMsg]
  [DecidableEq T.BMsg] [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub]
  [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]

/-- **An adversary of the joint-security game** with `n` honest users: an adversary of the
unforgeability game of `ofBase B PS adm` with the base scheme's ordinary signer as side oracle. -/
abbrev JointAdversary (n : ℕ) (V : OracleView X Y) (t : ℕ) : Type 1 :=
  UnforgeAdversary (ofBase B PS adm) n (baseSide B PS adm) V t

variable {B PS adm} {n : ℕ} {V : OracleView X Y} {t : ℕ} [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins]

variable [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins]

/-- **The probability of a forgery in the joint-security game** with `Q` requests. -/
noncomputable def jointForgeProb (A : JointAdversary B PS adm n V t) (Q : ℕ) : ℝ≥0∞ :=
  forgeProb A Q

/-- The joint-security forgery probability is at most `1`. -/
theorem jointForgeProb_le_one (A : JointAdversary B PS adm n V t) (Q : ℕ) :
    jointForgeProb A Q ≤ 1 :=
  forgeProb_le_one A Q

end GordieHowe.RingSignature
