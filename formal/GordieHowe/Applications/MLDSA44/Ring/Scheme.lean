-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SchemeView
public import GordieHowe.Applications.Ring.StmtCodec
public import GordieHowe.Applications.Ring.BaseSignerFacts
public import GordieHowe.Applications.MLDSA44.Spec.Basic
public import GordieHowe.Applications.MLDSA.Spec.ExpandMask

@[expose] public section

/-!
# The ML-DSA-44 rings: the statement scheme, the supported rings and the base signer

The ring relation the compiled ML-DSA-44 ring programs prove
(`lib/gordiehowe/examples/rings/mldsa_ring.h`: the ring statement is `64` public keys, a message
and a context; the prover holds a signature under one member's key), read as the ring relation of a
statement scheme (`GordieHowe/Applications/Ring/SchemeView.lean`), and the ML-DSA base signer of
the ring signature read as that scheme.

- `PublicKey`, `Sig`: the vendored FIPS 204 public keys `(ρ, t₁)` and signatures `(c̃, z, h)` at
  ML-DSA-44 and the concrete primitives.
- `scheme msgLen`: the statement scheme (`GordieHowe.Ring.SigScheme.ofVerifier`) of FIPS 204
  verification (`MLDSA.Concrete.verify`: Algorithm 8 with the bounded `ExpandA` and `SampleInBall`
  of Appendix C) on `msgLen`-byte message representatives `M′`, public value `Unit`.
- `ringAdm`: the supported rings, exactly `64` keys whose `ExpandA` finishes within `1008` SHAKE128
  bytes per `RejNTTPoly` call (`MLDSA44.ExpandAWithin`; the C++
  refuses a ring with any other key: `ring_host::decode` throws `StatementRefused`); `ringOk`: its
  check. `RStmt msgLen`, `ringRel64`, `RingIn`: the statements, the ring relation and its pairs.
- `prims eS eM`: the concrete primitives with the signing-only `ExpandS` and `ExpandMask`
  (Algorithms 33, 34) given (the vendored bundle's are placeholders), so that verification is the
  concrete one at every choice; `baseSigner eS eM maxAttempts bmsg`: the ML-DSA base signer
  `mldsaBaseSigner` at those primitives.
- `prims_fips`: at FIPS 204's `ExpandS` and `ExpandMask` (`GordieHowe.MLDSA.Spec.expandS`,
  `GordieHowe.MLDSA.Spec.expandMask`), `prims` is `concretePrimitivesFIPS`, the real signer.
- `schemeView`: the base signer read as `scheme`, its keys and signatures copied field by field
  (`verify_eq`: its verification is `MLDSA.Concrete.verify`); `adm`: the base signer's supported
  rings; `mem_ringRel64_iff`: the base signer's ring relation at every oracle is `ringRel64` at the
  read pair.
-/

namespace GordieHowe.MLDSA44.Ring

open GordieHowe.Ring GordieHowe.RingSignature _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA

attribute [local instance] concreteNTTRingOps

/-- The concrete primitives at ML-DSA-44. -/
abbrev cprims : Primitives _root_.MLDSA.mldsa44 := concretePrimitives _root_.MLDSA.mldsa44

instance : Fintype cprims.Power2High := inferInstanceAs (Fintype Rq)
instance : DecidableEq cprims.Power2High := inferInstanceAs (DecidableEq Rq)
instance : Fintype cprims.Hint := inferInstanceAs (Fintype (Vector Bool ringDegree))
instance : DecidableEq cprims.Hint := inferInstanceAs (DecidableEq (Vector Bool ringDegree))
instance : Inhabited cprims.Hint := inferInstanceAs (Inhabited (Vector Bool ringDegree))

/-- **An ML-DSA-44 public key** `(ρ, t₁)` (the vendored `MLDSA.PublicKey`). -/
abbrev PublicKey : Type := _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 cprims

/-- **An ML-DSA-44 signature** `(c̃, z, h)` (the vendored `MLDSA.FIPSSignature`). -/
abbrev Sig : Type := FIPSSignature _root_.MLDSA.mldsa44 cprims

instance : Inhabited PublicKey := ⟨⟨Vector.replicate _ 0, Vector.replicate _ (show cprims.Power2High from (0 : Rq))⟩⟩

variable (msgLen : ℕ)

/-- **The statement scheme of the ML-DSA-44 rings** at `msgLen`-byte message representatives
`M′` (FIPS 204 Algorithm 2, line 10: `M′ = 0 ‖ |ctx| ‖ ctx ‖ M`): FIPS 204 verification with the
bounded samplers (`MLDSA.Concrete.verify`), public value `Unit`. -/
abbrev scheme : SigScheme :=
  SigScheme.ofVerifier PublicKey (Bytes msgLen) Sig Unit
    (fun pk m σ => Concrete.verify _root_.MLDSA.mldsa44 pk m.toList σ) fun _ => ()

/-- **The rings the ML-DSA-44 ring programs support**: exactly `64` keys, each with an
`ExpandA(ρ)` that finishes within `1008` SHAKE128 bytes per `RejNTTPoly` call
(`MLDSA44.ExpandAWithin`, the C++'s six SHAKE128 blocks, `expand_a_fast`). -/
def ringAdm (l : List PublicKey) : Prop :=
  l.length = 64 ∧ ∀ pk ∈ l, MLDSA44.ExpandAWithin _root_.MLDSA.mldsa44 pk.rho

instance : DecidablePred ringAdm := fun l => by unfold ringAdm; infer_instance

/-- **The statements of the ML-DSA-44 ring programs**: a ring of at most `64` keys, the message
representative and the public value `()`. -/
abbrev RStmt : Type := GordieHowe.Ring.RingStmt (scheme msgLen) (Bytes msgLen) 64

/-- **A statement of the ML-DSA-44 ring programs**, an explicit computable value: the empty ring,
the all-zero message representative and the public value `()`. -/
instance RStmt.instInhabited : Inhabited (RStmt msgLen) :=
  ⟨⟨⟨[], Nat.zero_le _⟩, Vector.replicate msgLen 0, ()⟩⟩

/-- **The ring relation of the ML-DSA-44 ring programs**: supported rings (`ringAdm`) and a
signature at a position of the ring that verifies on the statement's message representative. -/
abbrev ringRel64 : Set (RStmt msgLen × GordieHowe.Ring.RingWit (scheme msgLen)) :=
  GordieHowe.Ring.ringRel ringAdm bindSelf

variable {msgLen}

/-- **The statement check**: the ring is supported. -/
def ringOk (x : RStmt msgLen) : Bool := decide (ringAdm x.ring.1)

theorem ringOk_iff {x : RStmt msgLen} : ringOk x = true ↔ ringAdm x.ring.1 := by
  simp [ringOk]

variable (msgLen) in
/-- **An honest input of an ML-DSA-44 ring**: a ring statement and a witness of the ring
relation. -/
structure RingIn where
  /-- The statement. -/
  x : RStmt msgLen
  /-- The witness: the signer's position and signature. -/
  w : GordieHowe.Ring.RingWit (scheme msgLen)
  /-- The pair is in the ring relation. -/
  mem : (x, w) ∈ ringRel64 msgLen

/-- **An honest input's statement passes the check.** -/
theorem RingIn.ringOk_x (y : RingIn msgLen) : ringOk y.x = true :=
  ringOk_iff.2 y.mem.1

/-- **The signer's position of an honest input is below `64`**. -/
theorem RingIn.idx_lt_64 (y : RingIn msgLen) : y.w.idx < 64 :=
  lt_of_lt_of_eq y.mem.2.idx_lt y.mem.1.1

/-- **The honest inputs are finite**: an honest input is determined by its statement, its
signer's position (below `64`) and its signature. -/
instance RingIn.finite : Finite (RingIn msgLen) :=
  Finite.of_injective (fun y : RingIn msgLen =>
      ((y.x.ring, y.x.msg), (⟨y.w.idx, y.idx_lt_64⟩ : Fin 64), y.w.sig)) (by
    rintro ⟨⟨R, m, ⟨⟩⟩, ⟨i, s⟩, h⟩ ⟨⟨R', m', ⟨⟩⟩, ⟨i', s'⟩, h'⟩ he
    simp only [Prod.mk.injEq, Fin.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := he
    rfl)

/-- The honest inputs as a finite type (`RingIn.finite`). -/
noncomputable instance RingIn.instFintype : Fintype (RingIn msgLen) :=
  Fintype.ofFinite _

/-- Decidable equality of the honest inputs (classical). -/
noncomputable instance RingIn.instDecidableEq : DecidableEq (RingIn msgLen) :=
  Classical.decEq _

/-! ### The base signer -/

/-- **The concrete primitives with the signing-only expansions given**: `ExpandS` (`eS`,
Algorithm 33) and `ExpandMask` (`eM`, Algorithm 34) in place of the vendored placeholders; every
field verification reads is the concrete one. -/
abbrev prims (eS : Bytes 64 → RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k)
    (eM : Bytes 64 → ℕ → RqVec _root_.MLDSA.mldsa44.l) : Primitives _root_.MLDSA.mldsa44 :=
  { cprims with expandS := eS, expandMask := eM }

/-- Updating `expandS` and `expandMask` at once is updating them one after the other (stated for
an abstract bundle `P`, so that no concrete primitive is unfolded). -/
theorem with_expandS_expandMask {p : _root_.MLDSA.Params} (P : Primitives p)
    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l) :
    ({ P with expandS := eS, expandMask := eM } : Primitives p) =
      { ({ P with expandS := eS } : Primitives p) with expandMask := eM } :=
  rfl

/-- **At FIPS 204's `ExpandS` and `ExpandMask` the primitives are the FIPS bundle**
`concretePrimitivesFIPS` (Algorithms 33 and 34). -/
theorem prims_fips :
    prims (GordieHowe.MLDSA.Spec.expandS _root_.MLDSA.mldsa44)
        (GordieHowe.MLDSA.Spec.expandMask _root_.MLDSA.mldsa44) =
      GordieHowe.MLDSA.Spec.concretePrimitivesFIPS _root_.MLDSA.mldsa44 := by
  unfold GordieHowe.MLDSA.Spec.concretePrimitivesFIPS GordieHowe.MLDSA.Spec.withExpandMask
    GordieHowe.MLDSA.Spec.concretePrimitivesKeyGen
  exact with_expandS_expandMask cprims _ _

variable (eS : Bytes 64 → RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k) (eM : Bytes 64 → ℕ → RqVec _root_.MLDSA.mldsa44.l)

instance : Fintype (prims eS eM).Power2High := inferInstanceAs (Fintype Rq)
instance : DecidableEq (prims eS eM).Power2High := inferInstanceAs (DecidableEq Rq)
instance : Fintype (prims eS eM).Hint := inferInstanceAs (Fintype (Vector Bool ringDegree))
instance : DecidableEq (prims eS eM).Hint := inferInstanceAs (DecidableEq (Vector Bool ringDegree))

variable {Xo Yo : Type} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {len : ℕ}

variable (Xo Yo) in
/-- **The ML-DSA-44 base signer** at the primitives `prims eS eM`: `mldsaBaseSigner` (FIPS 204
hedged signing with at most `maxAttempts` attempts on the base message `bmsg R m`, FIPS 204
verification with the bounded samplers, public value `Unit`). -/
abbrev baseSigner (maxAttempts : ℕ)
    (bmsg : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64 → RMsg → Bytes len) :
    BaseSigner Xo Yo 64 (mldsaSchemeT _root_.MLDSA.mldsa44 (prims eS eM) len) RMsg :=
  mldsaBaseSigner _root_.MLDSA.mldsa44 (prims eS eM) maxAttempts bmsg

/-- A key of the primitives `prims eS eM` as a concrete key (the same `ρ` and `t₁`). -/
def toKey (k : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) : PublicKey := ⟨k.rho, k.t1⟩

theorem toKey_injective : Function.Injective (toKey eS eM) := by
  rintro ⟨r, t⟩ ⟨r', t'⟩ h
  simp only [toKey, _root_.MLDSA.PublicKey.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- A signature of the primitives `prims eS eM` as a concrete signature (the same `c̃`, `z`,
`h`). -/
def sigEquiv : FIPSSignature _root_.MLDSA.mldsa44 (prims eS eM) ≃ Sig where
  toFun σ := ⟨σ.cTilde, σ.z, σ.h⟩
  invFun σ := ⟨σ.cTilde, σ.z, σ.h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Verification reads only the fields of a primitives bundle that signing-only updates keep**:
at `{P with expandS := eS, expandMask := eM}` it is verification at `P` of the same key and
signature, for every bundle `P` (stated for an abstract `P`, so that no concrete primitive is
unfolded). -/
theorem fipsVerify_with {p : _root_.MLDSA.Params} (P : Primitives p) [NTTRingOps]
    (eS : Bytes 64 → RqVec p.l × RqVec p.k) (eM : Bytes 64 → ℕ → RqVec p.l)
    (k : _root_.MLDSA.PublicKey p { P with expandS := eS, expandMask := eM }) (m : List Byte)
    (σ : FIPSSignature p { P with expandS := eS, expandMask := eM }) :
    fipsVerify p { P with expandS := eS, expandMask := eM } k m σ =
      fipsVerify p P ⟨k.rho, k.t1⟩ m ⟨σ.cTilde, σ.z, σ.h⟩ :=
  rfl

/-- **Verification at `prims eS eM` is verification at the concrete primitives.** -/
theorem fipsVerify_prims (k : _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM))
    (m : List Byte) (σ : FIPSSignature _root_.MLDSA.mldsa44 (prims eS eM)) :
    fipsVerify _root_.MLDSA.mldsa44 (prims eS eM) k m σ =
      fipsVerify _root_.MLDSA.mldsa44 cprims (toKey eS eM k) m (sigEquiv eS eM σ) :=
  fipsVerify_with cprims eS eM k m σ

variable (maxAttempts : ℕ)
  (bmsg : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64 → RMsg → Bytes len)

variable (Xo Yo) in
/-- **The ML-DSA-44 base signer read as `scheme len`** (`GordieHowe.Ring.SchemeView`): keys and
signatures copied field by field, base messages and public values unchanged; its verification
(`boundedOk && fipsVerify` at `prims eS eM`) is `MLDSA.Concrete.verify`. -/
def schemeView : SchemeView (baseSigner eS eM Xo Yo maxAttempts bmsg) (scheme len) where
  pk := toKey eS eM
  pk_injective := toKey_injective eS eM
  bm := id
  sig := sigEquiv eS eM
  pub := id
  pub_injective := Function.injective_id
  verify_eq _ k m σ := by
    change (boundedOk _ k.rho σ.cTilde && fipsVerify _ (prims eS eM) k m.toList σ) =
      Concrete.verify _ (toKey eS eM k) m.toList (sigEquiv eS eM σ)
    have h := fipsVerify_prims eS eM k m.toList σ
    unfold Concrete.verify boundedOk
    exact congrArg _ h
  pub_eq _ _ _ := rfl

/-- **The rings the base signer supports**: those whose read ring is supported (`ringAdm`). -/
def adm (R : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64) : Prop :=
  ringAdm (R.1.map (toKey eS eM))

instance : DecidablePred (adm eS eM) := fun R => by unfold adm; infer_instance

theorem adm_iff (R : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64) :
    adm eS eM R ↔ ringAdm ((schemeView eS eM Xo Yo maxAttempts bmsg).ringOf R).1 :=
  Iff.rfl

/-- **The ring relation of the base signer is `ringRel64` at the read pair**, at every oracle
(`SchemeView.mem_ringRel_iff`). -/
theorem mem_ringRel64_iff (H : Xo → Yo)
    (x : RingSignature.RingStmt (baseSigner eS eM Xo Yo maxAttempts bmsg))
    (w : RingSignature.RingWit (baseSigner eS eM Xo Yo maxAttempts bmsg)) :
    ((schemeView eS eM Xo Yo maxAttempts bmsg).toStmt x,
        (schemeView eS eM Xo Yo maxAttempts bmsg).toWit w) ∈ ringRel64 len ↔
      (x, w) ∈ RingSignature.ringRel (baseSigner eS eM Xo Yo maxAttempts bmsg) (adm eS eM) H :=
  (schemeView eS eM Xo Yo maxAttempts bmsg).mem_ringRel_iff (adm_iff eS eM maxAttempts bmsg) H x w

end GordieHowe.MLDSA44.Ring
