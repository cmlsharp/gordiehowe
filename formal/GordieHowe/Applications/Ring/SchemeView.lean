-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.StmtBase

@[expose] public section

/-!
# Base signers read as signature schemes: the ring statements of a compiled ring program

A compiled ring program (the Falcon rings, the ML-DSA rings) proves the ring relation of a
signature scheme `Sch` over statements that carry the base message itself
(`GordieHowe.Ring.RingStmt Sch Sch.Msg N`, the relation `GordieHowe.Ring.ringRel admS bindSelf`):
its configuration, transcript and honest prover do not depend on the base message map `bmsg` of
a ring signature, nor on the random oracle. This file reads the ring statements of a base signer
`B` (`GordieHowe/Model/RingSignature/Base.lean`) as such statements and builds the base signer's
`StmtVerifiesRing` from the program's soundness and honest direction, for every `bmsg`.

- `SchemeView B Sch`: the base signer's keys, base messages, signatures and public values read as
  the scheme's (`pk`, `bm`, the equivalence `sig`, `pub`), with the same verification and public
  value at every oracle (`verify_eq`, `pub_eq`). `SchemeView.ringOf`, `toStmt`, `toWit`, `ofWit`:
  the maps of rings, statements `(R, m, y) ↦ (R, bm (bmsg R m), pub y)` and witnesses.
- `SchemeView.mem_ringRel_iff`: the scheme's ring relation (`GordieHowe.Ring.ringRel admS
  bindSelf`) at the read pair is the base signer's (`RingSignature.ringRel B admB H`) at every
  oracle, when `admB R` is `admS` of the read ring (`hadm`).
- `SchemeVerifies Sch N rel relH admS`: the program's statements `GordieHowe.Ring.RingStmt Sch
  Sch.Msg N` with the relation `rel` verify `Sch` signatures for the ring relation on `admS`: a
  statement check, soundness through a witness map, and an honest input of every pair of the ring
  relation. `SchemeView.stmtVerifiesRing`: the base signer's `StmtVerifiesRing` (statements read
  by `toStmt`).
- `SigScheme.ofVerifier`: the statement scheme of a verifier (constant key generation and
  signing), for a base signer whose own signing is not a `SigScheme`'s (the ML-DSA signer
  refuses).
- The facts of the zero-knowledge route: `SchemeView.toStmt_injective` (when `bmsg R`, `bm`, `pk`
  and `pub` are injective), `SchemeView.not_mem_of_nil` (when the check rejects the empty ring).
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature

variable {Xo Yo : Type} {N : ℕ}

/-- **The base message slot of a program statement holds the base message itself.** -/
abbrev bindSelf {PK M : Type} : List PK → M → M := fun _ m => m

/-- **A base signer read as a signature scheme**: its keys, base messages and public values mapped
into the scheme's (`pk`, `bm`, `pub`, the first and the last injective), its signatures the
scheme's (`sig`), with the scheme's verification (`verify_eq`) and public value (`pub_eq`) at
every oracle. -/
structure SchemeView {T : Signature.SchemeTypes} {RMsg : Type}
    (B : BaseSigner Xo Yo N T RMsg) (Sch : SigScheme) where
  /-- The keys. -/
  pk : B.PK → Sch.PK
  /-- The key map is injective. -/
  pk_injective : Function.Injective pk
  /-- The base messages. -/
  bm : B.BMsg → Sch.Msg
  /-- The signatures. -/
  sig : B.BSig ≃ Sch.Sig
  /-- The public values. -/
  pub : B.Pub → Sch.Pub
  /-- The public-value map is injective. -/
  pub_injective : Function.Injective pub
  /-- Verification is the scheme's. -/
  verify_eq : ∀ (H : Xo → Yo) k m σ, B.bverify H k m σ = Sch.verify (pk k) (bm m) (sig σ)
  /-- The public value is the scheme's. -/
  pub_eq : ∀ (H : Xo → Yo) k σ, pub ((B.pub k σ).run H) = Sch.pub (sig σ)

/-- **The statement scheme of a verifier**: the signature scheme with keys `PK`, messages `Msg`,
signatures `Sig`, public values `Pub`, verification `verify` and public value `pub`, whose key
generation and signing are constant (secret keys, key-generation and signing coins are `Unit`). A
compiled ring program proves the ring relation of this scheme (`GordieHowe.Ring.ringRel`), which
reads only `verify` and `pub`; the ring signature's own key generation and signing are its base
signer's. -/
abbrev _root_.GordieHowe.Ring.SigScheme.ofVerifier (PK Msg Sig Pub : Type) [Inhabited Sig]
    [Inhabited PK] (verify : PK → Msg → Sig → Bool)
    (pub : Sig → Pub) : SigScheme where
  PK := PK
  SK := Unit
  Msg := Msg
  Sig := Sig
  Pub := Pub
  KeyCoins := Unit
  SignCoins := Unit
  keyGen _ := (default, ())
  pub := pub
  signWith _ _ _ := default
  verify := verify

namespace SchemeView

variable {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner Xo Yo N T RMsg}
  {Sch : SigScheme} (V : SchemeView B Sch)

/-- **The ring read as the scheme's**: the keys mapped by `pk`. -/
def ringOf (R : KeyRing B.PK N) : RingOf Sch.PK N :=
  ⟨R.1.map V.pk, by simpa using R.2⟩

@[simp] theorem length_ringOf (R : KeyRing B.PK N) : (V.ringOf R).1.length = R.1.length :=
  List.length_map _

/-- **The program statement of a ring statement** `(R, m, y)`: the read ring, the base message
`bmsg R m` read by `bm`, and the read public value. -/
def toStmt (x : RingSignature.RingStmt B) : GordieHowe.Ring.RingStmt Sch Sch.Msg N :=
  ⟨V.ringOf x.ring, V.bm (B.bmsg x.ring x.msg), V.pub x.pub⟩

/-- **The program witness of a ring witness**: the same position, the signature read by `sig`. -/
def toWit (w : RingSignature.RingWit B) : GordieHowe.Ring.RingWit Sch :=
  ⟨w.idx, V.sig w.sig⟩

/-- **The ring witness of a program witness**: the same position, the signature read back. -/
def ofWit (w : GordieHowe.Ring.RingWit Sch) : RingSignature.RingWit B :=
  ⟨w.idx, V.sig.symm w.sig⟩

theorem toWit_ofWit (w : GordieHowe.Ring.RingWit Sch) : V.toWit (V.ofWit w) = w := by
  simp [toWit, ofWit]

/-- **The scheme's ring relation at the read pair is the base signer's**, at every oracle `H`,
when the supported rings of the base signer are those whose read ring the scheme supports
(`hadm`). -/
theorem mem_ringRel_iff {admS : List Sch.PK → Prop} {admB : KeyRing B.PK N → Prop}
    (hadm : ∀ R, admB R ↔ admS (V.ringOf R).1) (H : Xo → Yo) (x : RingSignature.RingStmt B)
    (w : RingSignature.RingWit B) :
    (V.toStmt x, V.toWit w) ∈ GordieHowe.Ring.ringRel admS bindSelf ↔
      (x, w) ∈ RingSignature.ringRel B admB H := by
  constructor
  · rintro ⟨hadmS, ⟨hidx, hpub, hver⟩⟩
    have hidx' : w.idx < x.ring.1.length := by simpa [toStmt, toWit] using hidx
    refine ⟨(hadm _).2 hadmS, hidx', ?_, ?_⟩
    · rw [V.verify_eq]
      simpa [toStmt, toWit, ringOf] using hver
    · apply V.pub_injective
      rw [V.pub_eq]
      simpa [toStmt, toWit] using hpub
  · rintro ⟨hadmB, hidx, hver, hpub⟩
    refine ⟨(hadm _).1 hadmB, ⟨by simpa [toStmt, toWit] using hidx, ?_, ?_⟩⟩
    · simp only [toStmt, toWit]
      rw [← V.pub_eq H, hpub]
    · rw [V.verify_eq] at hver
      simpa [toStmt, toWit, ringOf] using hver

/-- **A program witness at the read statement gives a ring witness of the base signer**, at every
oracle. -/
theorem mem_ringRel_of {admS : List Sch.PK → Prop} {admB : KeyRing B.PK N → Prop}
    (hadm : ∀ R, admB R ↔ admS (V.ringOf R).1) (H : Xo → Yo) (x : RingSignature.RingStmt B)
    {w : GordieHowe.Ring.RingWit Sch} (h : (V.toStmt x, w) ∈ GordieHowe.Ring.ringRel admS bindSelf) :
    (x, V.ofWit w) ∈ RingSignature.ringRel B admB H :=
  (V.mem_ringRel_iff hadm H x (V.ofWit w)).1 (by rwa [toWit_ofWit])

end SchemeView

/-- **The program's statements verify `Sch` signatures for the ring relation** on the rings
`admS` (statements `GordieHowe.Ring.RingStmt Sch Sch.Msg N`, which carry the base message): a
statement check `check`; soundness, a witness of `rel` at a checked statement giving a ring witness
(`wit`); and the honest direction, every pair of the ring relation passing the check and having an
honest input (`input`) of `relH`. -/
structure SchemeVerifies (Sch : SigScheme) (N : ℕ) {W Inp : Type}
    (rel : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × W))
    (relH : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × Inp)) (admS : List Sch.PK → Prop) where
  /-- The statement check. -/
  check : GordieHowe.Ring.RingStmt Sch Sch.Msg N → Bool
  /-- The ring witness of a witness of `rel`. -/
  wit : GordieHowe.Ring.RingStmt Sch Sch.Msg N → W → GordieHowe.Ring.RingWit Sch
  /-- Soundness at a checked statement. -/
  sound : ∀ x w, check x = true → (x, w) ∈ rel → (x, wit x w) ∈ GordieHowe.Ring.ringRel admS bindSelf
  /-- The honest input of a pair of the ring relation. -/
  input : ∀ x w, (x, w) ∈ GordieHowe.Ring.ringRel admS bindSelf → Inp
  /-- The statements of the ring relation pass the check. -/
  check_eq_true : ∀ x w, (x, w) ∈ GordieHowe.Ring.ringRel admS bindSelf → check x = true
  /-- The honest input is one. -/
  input_mem : ∀ x w (h : (x, w) ∈ GordieHowe.Ring.ringRel admS bindSelf), (x, input x w h) ∈ relH

namespace SchemeView

variable {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner Xo Yo N T RMsg}
  {Sch : SigScheme} (V : SchemeView B Sch)

/-- **The base signer's statements verify its signatures** (`StmtVerifiesRing`) for the ring
relation on `admB`: statements read by `toStmt` and checked by the program's check, the ring
witness of a program witness read back (`ofWit`), the honest input of a pair of the ring relation
the program's at the read pair. Membership in the ring relation is decided by
`GordieHowe.Ring.ringRelDecidable` (for a decidable `admS` and public values with decidable
equality), so the definition is computable. -/
def stmtVerifiesRing {W Inp : Type}
    {rel : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × W)}
    {relH : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × Inp)} {admS : List Sch.PK → Prop}
    [DecidablePred admS] [DecidableEq Sch.Pub] (S : SchemeVerifies Sch N rel relH admS)
    {admB : KeyRing B.PK N → Prop}
    (hadm : ∀ R, admB R ↔ admS (V.ringOf R).1) : StmtVerifiesRing rel relH B admB where
  stmt := V.toStmt
  check x := S.check (V.toStmt x)
  wit x w := V.ofWit (S.wit (V.toStmt x) w)
  sound H x w hx hw := V.mem_ringRel_of hadm H x (S.sound _ _ hx hw)
  input x w :=
    haveI := GordieHowe.Ring.ringRelDecidable (N := N) admS bindSelf
    if h : (V.toStmt x, V.toWit w) ∈ GordieHowe.Ring.ringRel admS bindSelf then
      some (S.input _ _ h) else none
  check_eq_true H x w h := S.check_eq_true _ _ ((V.mem_ringRel_iff hadm H x w).2 h)
  input_mem H x w h := by
    have h' := (V.mem_ringRel_iff hadm H x w).2 h
    exact ⟨_, by simp [h'], S.input_mem _ _ h'⟩

/-- **The statement map is injective** when `bmsg R` is injective for every ring `R` (`hbm`) and
the base-message map `bm` is: `(R, bm (bmsg R m), pub y)` determines `R`, then `m`, and `y`. -/
theorem toStmt_injective (hbm : ∀ R, Function.Injective (B.bmsg R))
    (hb : Function.Injective V.bm) : Function.Injective V.toStmt := by
  rintro ⟨R, m, y⟩ ⟨R', m', y'⟩ h
  simp only [toStmt, GordieHowe.Ring.RingStmt.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hR : R = R' := by
    apply Subtype.ext
    exact List.map_injective_iff.2 V.pk_injective (congrArg Subtype.val h1)
  subst hR
  rw [hbm R (hb h2), V.pub_injective h3]

/-- **The statement map of `stmtVerifiesRing` is injective** under the conditions of
`toStmt_injective`. -/
theorem stmtVerifiesRing_stmt_injective {W Inp : Type}
    {rel : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × W)}
    {relH : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × Inp)} {admS : List Sch.PK → Prop}
    [DecidablePred admS] [DecidableEq Sch.Pub] (S : SchemeVerifies Sch N rel relH admS)
    {admB : KeyRing B.PK N → Prop}
    (hadm : ∀ R, admB R ↔ admS (V.ringOf R).1) (hbm : ∀ R, Function.Injective (B.bmsg R))
    (hb : Function.Injective V.bm) : Function.Injective (V.stmtVerifiesRing S hadm).stmt :=
  V.toStmt_injective hbm hb

/-- **No read statement of the empty ring is in a relation whose statements have nonempty rings**
(`hne`: for the Falcon and ML-DSA rings, the check needs the compiled ring size). -/
theorem not_mem_of_nil {Inp : Type} {relH : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × Inp)}
    (hne : ∀ x y, (x, y) ∈ relH → x.ring.1 ≠ []) (x : RingSignature.RingStmt B)
    (hx : x.ring.1 = []) (y : Inp) : (V.toStmt x, y) ∉ relH := fun h =>
  hne _ _ h (by simp [toStmt, ringOf, hx])

/-- **The statement map of `stmtVerifiesRing` keeps the ring's length** (`length_ringOf`), so the
statements of the empty ring are tested by the emptiness of the statement's ring
(`RingSignature.EmptyRingTest`). -/
def stmtVerifiesRing_emptyRingTest {W Inp : Type}
    {rel : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × W)}
    {relH : Set (GordieHowe.Ring.RingStmt Sch Sch.Msg N × Inp)} {admS : List Sch.PK → Prop}
    [DecidablePred admS] [DecidableEq Sch.Pub] (S : SchemeVerifies Sch N rel relH admS)
    {admB : KeyRing B.PK N → Prop}
    (hadm : ∀ R, admB R ↔ admS (V.ringOf R).1) :
    RingSignature.EmptyRingTest (V.stmtVerifiesRing S hadm).stmt where
  isNil r := r.ring.1.isEmpty
  isNil_stmt_iff y := by
    show (V.ringOf y.ring).1.isEmpty = true ↔ y.ring.1 = []
    rw [List.isEmpty_iff, ← List.length_eq_zero_iff, V.length_ringOf, List.length_eq_zero_iff]

end SchemeView

end GordieHowe.Ring
