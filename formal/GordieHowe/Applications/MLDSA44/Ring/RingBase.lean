-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.RingEncoding

@[expose] public section

/-!
# The ML-DSA-44 rings' statements verify ML-DSA-44 base signatures

The ring statements of the ML-DSA-44 base signer `baseSigner eS eM maxAttempts bmsg` read as the
statements `RStmt len` of the compiled ML-DSA-44 ring programs (`schemeView`): `(R, m, ())` is
read as `(R, bmsg R m, ())`, the base message in the statement's message slot. The program
statement holds the base message only through every member's `µ = H(tr ‖ M′)`, so a configuration
proves the ring relation at every `len` and `ringVerifies` holds for every `bmsg`.

- `ringVerifies S`: for program statements verifying `scheme len` signatures on the supported rings
  (`S : SchemeVerifies (scheme len) 64 rel relH ringAdm`, a configuration's frontend), the base
  signer's statements verify its signatures on the supported rings `adm eS eM`
  (`Ring.StmtVerifiesRing`, `SchemeView.stmtVerifiesRing`).
- The base signer's facts: `baseSigner_oracleFree` (no oracle query, verification reads no
  oracle), `baseSigner_pubOfCoins` (`Pub = Unit`), `baseSigner_refusal_le_one`,
  `baseSigner_boundedOk` (its signatures pass the bounded-sampling check).
- The facts of the zero-knowledge route at `ringVerifies`: `ringVerifies_stmt_injective` (when
  `bmsg R` is injective for every ring `R`: `convertedMsg_injective`, `bindingMsg_injective`),
  `not_mem_of_nil` (no statement of the empty ring is an honest statement when honest statements
  pass `ringOk`), and the inhabited types `nonempty_msg`, `nonempty_pub`, `nonempty_bsig`.
-/

namespace GordieHowe.MLDSA44.Ring

open GordieHowe.Ring GordieHowe.RingSignature _root_.MLDSA GordieHowe.MLDSA

attribute [local instance] _root_.MLDSA.Concrete.concreteNTTRingOps

variable (eS : Bytes 64 → RqVec _root_.MLDSA.mldsa44.l × RqVec _root_.MLDSA.mldsa44.k)
  (eM : Bytes 64 → ℕ → RqVec _root_.MLDSA.mldsa44.l) {Xo Yo : Type} {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {len : ℕ} (maxAttempts : ℕ)
  (bmsg : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64 → RMsg → Bytes len)
  {W Inp : Type} {rel : Set (RStmt len × W)} {relH : Set (RStmt len × Inp)}

variable (Xo Yo) in
/-- **The ML-DSA-44 rings' statements verify the base signatures of `baseSigner eS eM maxAttempts
bmsg`** on the supported rings `adm eS eM`, for program statements verifying `scheme len`
signatures (`S`): statements read by `schemeView` and checked by the program's check, the ring
witness of a program witness read back, the honest input of a pair of the ring relation the
program's at the read pair (`SchemeView.stmtVerifiesRing`). -/
noncomputable def ringVerifies (S : SchemeVerifies (scheme len) 64 rel relH ringAdm) :
    StmtVerifiesRing rel relH (baseSigner eS eM Xo Yo maxAttempts bmsg) (adm eS eM) :=
  (schemeView eS eM Xo Yo maxAttempts bmsg).stmtVerifiesRing S (adm_iff eS eM maxAttempts bmsg)

/-- **The statement map of `ringVerifies` is injective** when `bmsg R` is, for every ring `R`. -/
theorem ringVerifies_stmt_injective (S : SchemeVerifies (scheme len) 64 rel relH ringAdm)
    (hbm : ∀ R, Function.Injective (bmsg R)) :
    Function.Injective (ringVerifies eS eM Xo Yo maxAttempts bmsg S).stmt :=
  (schemeView eS eM Xo Yo maxAttempts bmsg).toStmt_injective hbm Function.injective_id

/-- **No statement of the empty ring is an honest statement** when every honest statement passes
the check `ringOk` (which needs `64` keys). -/
theorem not_mem_of_nil (S : SchemeVerifies (scheme len) 64 rel relH ringAdm) (hok : ∀ x y, (x, y) ∈ relH → ringOk x = true)
    (x : RingSignature.RingStmt (baseSigner eS eM Xo Yo maxAttempts bmsg)) (hx : x.ring.1 = [])
    (y : Inp) : ((ringVerifies eS eM Xo Yo maxAttempts bmsg S).stmt x, y) ∉ relH :=
  (schemeView eS eM Xo Yo maxAttempts bmsg).not_mem_of_nil (fun x' y' h hnil => by
    have hlen := (ringOk_iff.1 (hok x' y' h)).1
    rw [hnil] at hlen
    exact absurd hlen (by simp)) x hx y

/-- **The statements of the empty ring are tested by the emptiness of the statement's ring**
(`SchemeView.stmtVerifiesRing_emptyRingTest`). -/
instance ringVerifies_emptyRingTest (S : SchemeVerifies (scheme len) 64 rel relH ringAdm) :
    RingSignature.EmptyRingTest (ringVerifies eS eM Xo Yo maxAttempts bmsg S).stmt :=
  (schemeView eS eM Xo Yo maxAttempts bmsg).stmtVerifiesRing_emptyRingTest S
    (adm_iff eS eM maxAttempts bmsg)

/-- The base signer's ring messages are inhabited when `RMsg` is. -/
theorem nonempty_msg [Nonempty RMsg] :
    Nonempty (baseSigner eS eM Xo Yo maxAttempts bmsg).Msg :=
  inferInstanceAs (Nonempty RMsg)

/-- The base signer's public values are inhabited. -/
theorem nonempty_pub : Nonempty (baseSigner eS eM Xo Yo maxAttempts bmsg).Pub :=
  inferInstanceAs (Nonempty Unit)

/-- The base signer's signatures are inhabited. -/
theorem nonempty_bsig : Nonempty (baseSigner eS eM Xo Yo maxAttempts bmsg).BSig :=
  ⟨(sigEquiv eS eM).symm default⟩

/-! ### The base signer's facts -/

/-- **The ML-DSA-44 base signer is oracle-free** (`mldsaBaseSigner_oracleFree`): its signers and
public value make no queries and its verification reads no oracle. -/
theorem baseSigner_oracleFree : (baseSigner eS eM Xo Yo maxAttempts bmsg).OracleFree :=
  mldsaBaseSigner_oracleFree _root_.MLDSA.mldsa44 (prims eS eM) maxAttempts bmsg

/-- **The public value of the ML-DSA-44 base signer is read off the coins** (`Pub = Unit`,
`BaseSigner.pubOfCoins_unique`). -/
theorem baseSigner_pubOfCoins :
    (baseSigner eS eM Xo Yo maxAttempts bmsg).PubOfCoins fun _ => () :=
  haveI : Unique (baseSigner eS eM Xo Yo maxAttempts bmsg).Pub := inferInstanceAs (Unique Unit)
  BaseSigner.pubOfCoins_unique _

/-- **The ML-DSA-44 base signer refuses with probability at most `1` at every input**
(`mldsaBaseSigner_refusal_le_one`). -/
theorem baseSigner_refusal_le_one (H : Xo → Yo) (kc : Bytes 32)
    (R : KeyRing (_root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 (prims eS eM)) 64) (i : ℕ)
    (m : RMsg) :
    Pr[cb ~ PMF.uniformOfFintype (baseSigner eS eM Xo Yo maxAttempts bmsg).Coins :
      ((baseSigner eS eM Xo Yo maxAttempts bmsg).bsign
        ((baseSigner eS eM Xo Yo maxAttempts bmsg).sk kc) R i m cb).run H = none] ≤
      ((1 : NNReal) : ENNReal) :=
  mldsaBaseSigner_refusal_le_one _root_.MLDSA.mldsa44 (prims eS eM) maxAttempts bmsg H kc R i m

/-- **A signature of the ML-DSA-44 base signer passes the bounded-sampling check** at the signer's
`ρ` (`boundedOk_of_fipsSignWith`): its `SampleInBall(c̃)` and the key's `ExpandA(ρ)` finish within
their bounds. -/
theorem baseSigner_boundedOk {sk : SecretKey _root_.MLDSA.mldsa44} {msg : List Byte}
    {rnd : Bytes 32} {σ : FIPSSignature _root_.MLDSA.mldsa44 (prims eS eM)}
    (h : fipsSignWith _root_.MLDSA.mldsa44 (prims eS eM) maxAttempts sk msg rnd = some σ) :
    boundedOk _root_.MLDSA.mldsa44 sk.rho σ.cTilde = true :=
  boundedOk_of_fipsSignWith _root_.MLDSA.mldsa44 (prims eS eM) h

end GordieHowe.MLDSA44.Ring
