-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Frontend.Basic

@[expose] public section

/-!
# GordieHowe frontend: the native Falcon ring's statement and the ring relation

The statement of the native Falcon rings' BCS transformation, generic in the program and its
interpretation (`GordieHowe.Falcon512.Ring.FalconRingBase`): a ring signature statement `(R, m, r)` of rings of at
most `64` keys (`RStmt`), as the hand-built native ring's (`GordieHowe/Applications/Falcon512/Ring/Native/System/Composite.lean`):

* **The program's statement** (`stmtOf`): the ring's keys' coefficients at `statement.ring`
  (value `4`, key `j` at `512 j … 512 j + 511`) and the coefficients of `HashToPoint(r ‖ m)`
  (`GordieHowe.Falcon512.Ring.Native.stmtChallenge`, the keyless primitive the verifier computes) at `statement.c`
  (value `5`). The challenge is never read from the prover: the verifier computes it from the
  message and the salt.
* **The statement check** (`ringOk`): the ring has `64` keys (the compiled ring size) and the
  hash-to-point succeeds; the BCS verifier rejects every other statement
  (`GordieHowe.RealizedProgram.ProofSystem.IOP.comapWith`).
* **The ring relation** (`ringRel64`): rings of `64` keys and the ring relation
  (`GordieHowe.Ring.ringRel`) at the base message `m` (converted signatures). `ringRel_of_rel`: at a
  statement that passes the check, the realized program's relation at `stmtOf` (`GordieHowe.Falcon512.Ring.rel`) gives the
  ring relation at the signature encoded from the extracted `s2` with the statement's salt
  (`GordieHowe.Falcon512.Ring.Native.CoreWit.withSalt`).
-/

namespace GordieHowe.Falcon512.Ring

open GordieHowe.Ring Native

variable {msgLen : ℕ} (G : Signer msgLen)

/-- **The statement of a native Falcon ring of `64` keys**: a ring of at most `64` keys, an
`msgLen`-byte message and the salt. -/
abbrev RStmt : Type := RingStmt (scheme G) (Fin msgLen → UInt8) 64

/-- **The rings the native Falcon rings' realized programs support**: exactly `64` keys. -/
abbrev ringAdm64 : List PublicKey → Prop := fun R => R.length = 64

/-- **The ring relation of the native Falcon rings' realized programs**: rings of `64` keys and the ring
relation at the base message `m` (`GordieHowe.Ring.ringRel`). -/
abbrev ringRel64 : Set (RStmt G × RingWit (scheme G)) := GordieHowe.Ring.ringRel ringAdm64 bindMsg

variable {G}

/-- **The statement check**: the ring has `64` keys and the hash-to-point succeeds. -/
def ringOk (x : RStmt G) : Bool := x.ring.1.length == 64 && (ringChallenge x.pub x.msg).isSome

theorem ringOk_iff {x : RStmt G} :
    ringOk x = true ↔ x.ring.1.length = 64 ∧ (ringChallenge x.pub x.msg).isSome = true := by
  simp [ringOk]

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp} [AReading (I 0)]

/-- **Coefficient `c` of key `j`** of a statement's ring, as a natural below `q`. -/
def keyEntry (x : RStmt G) (s : ℕ) : ℕ :=
  if h : s % 512 < falcon512.n then EmulatedAlgebraCircuit.keyCoeffs (Native.ringKey x (s / 512)).h ⟨s % 512, h⟩
  else 0

/-- **The program's statement of a ring statement**: the keys' coefficients at `statement.ring`,
the coefficients of `HashToPoint(r ‖ m)` at `statement.c`, every other coordinate `0`. -/
def stmtOf (x : RStmt G) : program.Valuation I := fun v i =>
  if v = FalconRingMember.ring program then RealizedProgram.castElt (a := 0) ((keyEntry x i : ℕ) : (I 0).K)
  else if h : v = FalconRingMember.chal program ∧ i < falcon512.n then
    RealizedProgram.castElt (a := 0) ((stmtChallenge x ⟨i, h.2⟩ : ℕ) : (I 0).K)
  else 0

theorem castElt_castElt_zero {v : ℕ} (hv : program.valueField v = 0) (y : (I 0).K) :
    (RealizedProgram.castElt (RealizedProgram.castElt (a := 0) (b := program.valueField v) y) : (I 0).K) = y := by
  rw [RealizedProgram.castElt_castElt_eq, if_pos hv.symm]
  exact RealizedProgram.castElt_self _

theorem ringEntry_stmtOf (x : RStmt G) (s : ℕ) :
    ringEntry (stmtOf (program := program) (I := I) x) s = ((keyEntry x s : ℕ) : (I 0).K) := by
  unfold ringEntry stmtOf
  rw [if_pos rfl,
    castElt_castElt_zero ((FalconRingMember.fields (program := program)) _ (by simp))]

theorem chalEntry_stmtOf (x : RStmt G) (i : Fin falcon512.n) :
    chalEntry (stmtOf (program := program) (I := I) x) i = ((stmtChallenge x i : ℕ) : (I 0).K) := by
  unfold chalEntry stmtOf
  rw [if_neg (FalconRingMember.chal_ne_ring (program := program)), dif_pos ⟨rfl, i.isLt⟩,
    castElt_castElt_zero ((FalconRingMember.fields (program := program)) _ (by simp))]

theorem stmtOf_ring (x : RStmt G) (i : ℕ) :
    stmtOf (program := program) (I := I) x (FalconRingMember.ring program) i =
      RealizedProgram.castElt (a := 0) ((keyEntry x i : ℕ) : (I 0).K) := by
  unfold stmtOf
  rw [if_pos rfl]

theorem stmtOf_chal (x : RStmt G) {i : ℕ} (hi : i < falcon512.n) :
    stmtOf (program := program) (I := I) x (FalconRingMember.chal program) i =
      RealizedProgram.castElt (a := 0) ((stmtChallenge x ⟨i, hi⟩ : ℕ) : (I 0).K) := by
  unfold stmtOf
  rw [if_neg (FalconRingMember.chal_ne_ring (program := program)), dif_pos ⟨rfl, hi⟩]

theorem keyEntry_lt (x : RStmt G) (s : ℕ) : keyEntry x s < 12289 := by
  unfold keyEntry EmulatedAlgebraCircuit.keyCoeffs
  split_ifs
  · exact ZMod.val_lt _
  · norm_num

/-- **The coordinate of coefficient `c` of key `r`** of the program's statement's ring. -/
theorem keyEntry_add (x : RStmt G) (r : ℕ) (c : Fin falcon512.n) :
    keyEntry x (r * 512 + c) = EmulatedAlgebraCircuit.keyCoeffs (Native.ringKey x r).h c := by
  obtain ⟨c, hc⟩ := c
  have hc' : c < 512 := hc
  have h1 : (r * 512 + c) / 512 = r := by omega
  have h2 : (r * 512 + c) % 512 = c := by omega
  unfold keyEntry
  rw [dif_pos (by rw [h2]; exact hc)]
  simp only [h1, h2]
  rfl

/-- **The ring keys of the program's statement** are the statement's keys. -/
theorem ringKey_stmtOf (x : RStmt G) (r : ℕ) :
    Ring.ringKey (stmtOf (program := program) (I := I) x) r = Native.ringKey x r := by
  have hc : ∀ c : Fin falcon512.n,
      (((I 0).toNat (ringEntry (stmtOf (program := program) (I := I) x) (r * 512 + c)) : ℕ) :
        _root_.Falcon.Coeff) = Falcon512.coeff (Native.ringKey x r).h c := fun c => by
    rw [ringEntry_stmtOf, AReading.toNat_natCast (keyEntry_lt x _), keyEntry_add]
    simp only [EmulatedAlgebraCircuit.keyCoeffs, ZMod.natCast_zmod_val]
  unfold Ring.ringKey
  cases hk : Native.ringKey x r with
  | mk h' =>
    rw [hk] at hc
    congr 1
    rw [← Falcon512.ofCoeff_coeff h']
    exact congrArg Falcon512.ofCoeff (funext hc)

/-- **The challenge of the program's statement** is the statement's `HashToPoint(r ‖ m)`. -/
theorem chalNat_stmtOf (x : RStmt G) (i : Fin falcon512.n) :
    chalNat (stmtOf (program := program) (I := I) x) i = stmtChallenge x i := by
  unfold chalNat
  rw [chalEntry_stmtOf, AReading.toNat_natCast (stmtChallenge_lt x i)]

/-- **The realized program's relation at a checked statement gives the ring relation**: the
signer's position is in the ring, the signature encoded from
`s2` with the statement's salt carries the salt (`extractSig_spec`), and it verifies under the
signer's key on `m`: the challenge of the realized program's relation is `HashToPoint(r ‖ m)`
(`chalNat_stmtOf`, `ofCoeff_stmtChallenge`). -/
theorem ringRel_of_rel {x : RStmt G} (hok : ringOk x = true) {w : CoreWit}
    (h : (stmtOf (program := program) (I := I) x, w) ∈ Ring.rel) :
    (x, w.withSalt (G := G) x.pub) ∈ ringRel64 G := by
  obtain ⟨hlen, hsome⟩ := ringOk_iff.1 hok
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hidx, halg, henc⟩ := h
  have hjlt : w.idx < x.ring.1.length := by rw [hlen]; exact hidx
  have hkey : Native.ringKey x w.idx = x.ring.1[w.idx]'hjlt := ringKey_eq hjlt
  rw [ringKey_stmtOf, hkey] at halg
  have hch : (fun i => (chalNat (stmtOf (program := program) (I := I) x) i : _root_.Falcon.Coeff)) =
      fun i => (stmtChallenge x i : _root_.Falcon.Coeff) := funext fun i => by rw [chalNat_stmtOf]
  rw [hch, ofCoeff_stmtChallenge hc] at halg
  have hdec : GordieHowe.Falcon512.verifyDecoded (x.ring.1[w.idx]'hjlt) (List.ofFn x.msg) x.pub w.s2.toRq :=
    ⟨c, by rw [hashToPoint_eq_ringChallenge]; exact hc, halg⟩
  obtain ⟨hver, hsalt⟩ := extractSig_spec henc hdec
  exact ⟨hlen, hjlt, hsalt, verifySig_eq_true_iff.mpr hver⟩

end GordieHowe.Falcon512.Ring
