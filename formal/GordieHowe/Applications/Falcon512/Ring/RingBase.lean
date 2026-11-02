-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Honest
public import GordieHowe.Applications.Ring.BaseSignerFacts
public import GordieHowe.Applications.Ring.StmtBase
public import GordieHowe.Applications.Ring.SchemeView

@[expose] public section

/-!
# The native Falcon rings' statements verify Falcon-512 base signatures

The ring statements of the Falcon-512 base signer `falconBaseSigner G bmsg`
(`GordieHowe/Applications/Ring/BaseSigners.lean`) with rings of at most `64` keys, read as the
statements of the native Falcon rings' BCS transformation (`GordieHowe.Falcon512.Ring.RStmt G`, the
statements the configurations' transcripts write): `(R, m, y)` is read as `(R, bmsg R m, y)`, the
base message in the statement's message slot. The program statement
(`GordieHowe.Falcon512.Ring.stmtOf`) holds the message only through the coefficients of
`HashToPoint(r ‖ bmsg R m)`, and `ringVerifies` is defined at one realized program `program` for
every `bmsg` whose values have the signer's message length.

- `adm64`: the supported rings, exactly `64` keys.
- `schemeView G bmsg`: the base signer read as the scheme `scheme G` (`GordieHowe.Ring.SchemeView`,
  `GordieHowe/Applications/Ring/SchemeView.lean`); `toRStmt`, `toRWit`, `ofRWit`: its statement
  and witness maps; `mem_ringRel64_iff`: the ring relation of the base signer at any oracle is
  `ringRel64 G` at the read pair; `mem_ringRel_of_mem_ringRel64`: its direction from `ringRel64 G`.
- `ringStmtRelOf`, `ringHonestRelOf`: the relation and the honest relation of the configurations'
  IOP read at `RStmt G` (`ringOk` and the realized program's relation, or the honest relation
  `relH`, at `stmtOf`).
- `schemeVerifies G`: `RStmt G` verifies `scheme G` signatures for the ring relation on rings of
  `64` keys (`GordieHowe.Ring.SchemeVerifies`): soundness by `ringRel_of_rel`, the honest input the
  pair (`RingIn`). `ringVerifies G bmsg`: hence `RStmt G` verifies the base signatures of
  `falconBaseSigner G bmsg` for the ring relation on `adm64` (`Ring.StmtVerifiesRing`,
  `SchemeView.stmtVerifiesRing`).
- The facts of the zero-knowledge route (`RingSignature.Insider.ZKRingHyps`) at `ringVerifies`:
  `toRStmt_injective`, `ringVerifies_stmt_injective` (the statement map is injective when `bmsg R`
  is, for every ring `R`; `bmsg R m = m` and `encodeRingMsg`), `not_mem_ringHonestRelOf_nil` (no
  statement of the empty ring is an honest statement: the check needs `64` keys), and the
  inhabited types `nonempty_msg`, `nonempty_pub`, `nonempty_bsig` of the base signer;
  `RingIn.idx_lt_64`, `RingIn.finite`: the honest inputs are finite.
-/

namespace GordieHowe.Falcon512.Ring

open GordieHowe.Ring GordieHowe.RingSignature _root_.GordieHowe.Falcon512.Ring.Native
  RealizedProgram.ProofSystem

variable {msgLen : ℕ} (G : Signer msgLen) {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  (bmsg : KeyRing PublicKey 64 → RMsg → (Fin msgLen → UInt8)) {Xo Yo : Type}

/-- **The rings the native Falcon rings' realized programs support**: exactly `64` keys. -/
abbrev adm64 : KeyRing PublicKey 64 → Prop := fun R => R.1.length = 64

variable (Xo Yo) in
/-- **The Falcon-512 base signer read as the scheme `scheme G`** (`GordieHowe.Ring.SchemeView`):
keys, base messages, signatures and salts are the scheme's, with the same verification and
salt. -/
def schemeView : SchemeView (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg) (scheme G) where
  pk := id
  pk_injective := Function.injective_id
  bm := id
  sig := Equiv.refl _
  pub := id
  pub_injective := Function.injective_id
  verify_eq _ _ _ _ := rfl
  pub_eq _ _ _ := rfl

/-- **The statement of the native Falcon rings of a ring statement** `(R, m, y)` of the base
signer: `(R, bmsg R m, y)` (`SchemeView.toStmt`). -/
abbrev toRStmt (x : RingSignature.RingStmt (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg)) : RStmt G :=
  (schemeView G bmsg Xo Yo).toStmt x

/-- **The witness of the native Falcon rings of a ring witness**: the same position and
signature. -/
abbrev toRWit (w : RingSignature.RingWit (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg)) :
    GordieHowe.Ring.RingWit (scheme G) :=
  (schemeView G bmsg Xo Yo).toWit w

/-- **The ring witness of a witness of the native Falcon rings**: the same position and
signature. -/
abbrev ofRWit (w : GordieHowe.Ring.RingWit (scheme G)) :
    RingSignature.RingWit (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg) :=
  (schemeView G bmsg Xo Yo).ofWit w

variable {G bmsg}

/-- **The supported rings of the base signer are those whose read ring has `64` keys.** -/
theorem adm64_iff (R : KeyRing PublicKey 64) :
    adm64 R ↔ ringAdm64 ((schemeView G bmsg Xo Yo).ringOf R).1 := by
  show R.1.length = 64 ↔ (R.1.map id).length = 64
  rw [List.length_map]

/-- **The ring relation of the base signer is the native Falcon rings' at the read pair**, at
every oracle (`SchemeView.mem_ringRel_iff`). -/
theorem mem_ringRel64_iff (H : Xo → Yo)
    (x : RingSignature.RingStmt (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg))
    (w : RingSignature.RingWit (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg)) :
    (toRStmt G bmsg x, toRWit G bmsg w) ∈ ringRel64 G ↔
      (x, w) ∈ RingSignature.ringRel (falconBaseSigner G bmsg) adm64 H :=
  (schemeView G bmsg Xo Yo).mem_ringRel_iff adm64_iff H x w

/-- **A ring witness of the native Falcon rings at the read statement is a ring witness of the
base signer**, at every oracle (`SchemeView.mem_ringRel_of`). -/
theorem mem_ringRel_of_mem_ringRel64 (H : Xo → Yo)
    (x : RingSignature.RingStmt (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg))
    {w : GordieHowe.Ring.RingWit (scheme G)} (h : (toRStmt G bmsg x, w) ∈ ringRel64 G) :
    (x, ofRWit G bmsg w) ∈ RingSignature.ringRel (falconBaseSigner G bmsg) adm64 H :=
  (schemeView G bmsg Xo Yo).mem_ringRel_of adm64_iff H x h

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp} [AReading (I 0)]

variable (G program I) in
/-- **The relation of the native Falcon rings' IOP**: the statement passes the check (`ringOk`)
and the realized program's relation holds at its program statement, on the witness read from that
statement. -/
abbrev ringStmtRelOf : Set (RStmt G × (program.Valuation I → CoreWit)) :=
  {p | ringOk p.1 = true ∧ (stmtOf p.1, p.2) ∈ relOf Ring.rel}

variable (G program I) in
/-- **The honest relation of the native Falcon rings' IOP**: the statement passes the check and
its program statement is the honest input's (`relH`). -/
abbrev ringHonestRelOf [FalconRingRoles program] [FalconRingRoleFacts program]
    [FalconRingSource program] : Set (RStmt G × RingIn G) :=
  {p | ringOk p.1 = true ∧ (stmtOf p.1, p.2) ∈ relH G program I}

variable [FalconRingRoles program] [FalconRingRoleFacts program] [FalconRingSource program]

variable (G program I) in
/-- **The native Falcon rings' statements verify Falcon-512 signatures** for the ring relation on
rings of `64` keys (`GordieHowe.Ring.SchemeVerifies`): statements checked by `ringOk`; a witness
`f` of the IOP's relation gives the ring witness of the signature encoded from the extracted `s2`
with the statement's salt (`CoreWit.withSalt`, `ringRel_of_rel`); the honest input of a pair of
the ring relation is the pair (`RingIn`). -/
def schemeVerifies :
    SchemeVerifies (scheme G) 64 (ringStmtRelOf G program I) (ringHonestRelOf G program I)
      ringAdm64 where
  check := ringOk
  wit x f := (f (stmtOf (program := program) (I := I) x)).withSalt (G := G) x.pub
  sound _ _ _ hf := ringRel_of_rel hf.1 hf.2
  input x w h := ⟨x, w, h⟩
  check_eq_true x w h := RingIn.ringOk_x (G := G) ⟨x, w, h⟩
  input_mem x w h := ⟨RingIn.ringOk_x (G := G) ⟨x, w, h⟩, rfl⟩

variable (G bmsg program I Xo Yo) in
/-- **The native Falcon rings' statements verify the base signatures of `falconBaseSigner G
bmsg`** for the ring relation on rings of `64` keys (`Ring.StmtVerifiesRing`,
`SchemeView.stmtVerifiesRing` at `schemeVerifies`): statements read by `toRStmt` and checked by
`ringOk`; a witness `f` of the IOP's relation gives the ring witness of the signature encoded from
the extracted `s2` with the statement's salt; the honest input of a pair of the ring relation is
the honest pair `(toRStmt x, toRWit w)` (`RingIn`), none off the ring relation. -/
noncomputable def ringVerifies :
    StmtVerifiesRing (ringStmtRelOf G program I) (ringHonestRelOf G program I)
      (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg) adm64 :=
  (schemeView G bmsg Xo Yo).stmtVerifiesRing (schemeVerifies G program I) adm64_iff

variable (G bmsg program I Xo Yo) in
/-- **The statements of the empty ring are tested by the emptiness of the statement's ring**
(`RingSignature.EmptyRingTest`, `SchemeView.stmtVerifiesRing_emptyRingTest`). -/
instance ringVerifies_emptyRingTest :
    RingSignature.EmptyRingTest (ringVerifies G bmsg Xo Yo program I).stmt :=
  (schemeView G bmsg Xo Yo).stmtVerifiesRing_emptyRingTest (schemeVerifies G program I) adm64_iff

/-! ### The facts of the zero-knowledge route -/

variable (G bmsg) in
/-- **The statement map is injective** when `bmsg R` is injective for every ring `R` (`hbm`):
`(R, bmsg R m, y)` determines `R`, then `m`, and `y`. -/
theorem toRStmt_injective (hbm : ∀ R, Function.Injective (bmsg R)) :
    Function.Injective (toRStmt (Xo := Xo) (Yo := Yo) G bmsg) :=
  (schemeView G bmsg Xo Yo).toStmt_injective hbm Function.injective_id

variable (G bmsg program I Xo Yo) in
/-- **The statement map of `ringVerifies` is injective** when `bmsg R` is, for every ring `R`. -/
theorem ringVerifies_stmt_injective (hbm : ∀ R, Function.Injective (bmsg R)) :
    Function.Injective (ringVerifies G bmsg Xo Yo program I).stmt :=
  toRStmt_injective G bmsg hbm

omit [AReading (I 0)] in
variable (G bmsg program I) in
/-- **No statement of the empty ring is an honest statement**: the check `ringOk` needs `64`
keys. -/
theorem not_mem_ringHonestRelOf_nil
    (x : RingSignature.RingStmt (falconBaseSigner («X» := Xo) («Y» := Yo) G bmsg))
    (hx : x.ring.1 = []) (y : RingIn G) :
    (toRStmt G bmsg x, y) ∉ ringHonestRelOf G program I :=
  (schemeView G bmsg Xo Yo).not_mem_of_nil (fun x' _ h hnil => by
    have hlen := (ringOk_iff.1 h.1).1
    rw [hnil] at hlen
    exact absurd hlen (by simp)) x hx y

variable (G bmsg) in
/-- The base signer's ring messages are inhabited when `RMsg` is. -/
theorem nonempty_msg [Nonempty RMsg] :
    Nonempty (falconBaseSigner («X» := Xo) («Y» := Yo) (N := 64) G bmsg).Msg :=
  inferInstanceAs (Nonempty RMsg)

variable (G bmsg) in
/-- The base signer's public values (salts) are inhabited. -/
theorem nonempty_pub : Nonempty (falconBaseSigner («X» := Xo) («Y» := Yo) (N := 64) G bmsg).Pub :=
  inferInstanceAs (Nonempty Salt)

variable (G bmsg) in
/-- The base signer's signatures are inhabited. -/
theorem nonempty_bsig :
    Nonempty (falconBaseSigner («X» := Xo) («Y» := Yo) (N := 64) G bmsg).BSig :=
  inferInstanceAs (Nonempty Sig)

/-- **The signer's position of an honest input is below `64`**: it is in a ring of `64` keys. -/
theorem RingIn.idx_lt_64 (y : RingIn G) : y.w.idx < 64 :=
  lt_of_lt_of_eq y.mem.2.idx_lt y.mem.1

/-- **The honest inputs are finite**: an honest input is determined by its statement, its signer's
position (below `64`) and its signature. -/
instance RingIn.finite : Finite (RingIn G) :=
  Finite.of_injective (fun y : RingIn G =>
      ((y.x.ring, y.x.msg, y.x.pub), (⟨y.w.idx, y.idx_lt_64⟩ : Fin 64), y.w.sig)) (by
    rintro ⟨⟨R, m, p⟩, ⟨i, s⟩, h⟩ ⟨⟨R', m', p'⟩, ⟨i', s'⟩, h'⟩ he
    simp only [Prod.mk.injEq, Fin.mk.injEq] at he
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := he
    rfl)

/-- The honest inputs as a finite type (`RingIn.finite`). -/
noncomputable instance RingIn.instFintype : Fintype (RingIn G) :=
  Fintype.ofFinite _

/-- Decidable equality of the honest inputs (classical). -/
noncomputable instance RingIn.instDecidableEq : DecidableEq (RingIn G) :=
  Classical.decEq _

end GordieHowe.Falcon512.Ring
