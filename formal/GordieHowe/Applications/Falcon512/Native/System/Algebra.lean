-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.System.Source
public import GordieHowe.Applications.Falcon512.System.Honest
public import GordieHowe.Applications.Falcon512.Circuits.NativeAlgebraHonest

@[expose] public section

/-!
# Falcon native: the algebra constraints of domain A

The native algebra of Falcon native (`lib/gordiehowe/examples/falcon/falcon_native.h`, over a
field `F` of characteristic `q = 12289`): the sample bits `c_A` (`512 × 16` Bit cells), the private
input `s2`, and the advice `s1`, the native norm's witness and `encoding.slack_hi` (`Committed`),
with

* `signature.equation` (`SignatureRows`, 512 affine rows, `falcon_native.h:258-259`):
  `assert_mod(s1 + NegacyclicConv(Spectrum{key})(s2), from_digits(c_A, 2), q)` at `m = q = char F`,
  that is `from_digits(c_A, 2)_i − (h · s2)_i − s1_i = 0` in `F`;
* the native norm on `s1 ‖ s2` (`assert_norm_native`, `norm.h:426-459`, `falcon_native.h:269`):
  the constraint groups `NativeNorm.Holds` on `normInputs`;
* the encoding check (`assert_encodable_native`, `norm.h:461-503`, `falcon_native.h:278`): the derived
  bit `b = a₁ − 2h` of every `s2` coefficient is a bit (`NativeEncoding.BitsHold`);
* the Boolean check of the Bit cells `c_A` (`x (x − 1) = 0`, in domain A's Boolean batch
  `A.boolean`);

and the range requests below `64` (`AlgRequests`): the norm's digits (`NativeNorm.DigitsBelow`)
and the encoding's `h + 48`, `slack_lo`, `slack_hi` (`NativeEncoding.RequestsHold`).

**Soundness** (`algebra_sound`): the samples read from `c_A` and the signature polynomial read from
`s2` satisfy Falcon's algebraic verifier and the encoding bounds (`GordieHowe.Falcon512.Emulated.AlgebraSpec`, the
emulated instance's conclusion). `NativeNorm.sound_of_holds` lifts `s1 ‖ s2` to naturals with
centered norm at most `β²`, `NativeEncoding.sound` gives the encoding magnitudes, and
`GordieHowe.Falcon512.Native.Rows.establish` pulls the signature rows (`signatureRows_rowsHold`, through the row
witness `sigWit`) back to `R_q`.
-/

namespace GordieHowe.Falcon512.Native

open GordieHowe.Bits

variable {F : Type} [Field F]

/-- The norm's coefficient wires: `s1 ‖ s2` (`norm.h`, `concat(s1, s2)`). -/
def normInputs (s2 : Fin falcon512.n → F) (c : Committed F) (i : Fin 1024) : F :=
  if hi : (i : ℕ) < falcon512.n then c.s1 ⟨i, hi⟩
  else s2 ⟨i - falcon512.n, by have := _root_.GordieHowe.Falcon512.NativeAlgebraCircuit.normCoeffs_eq; omega⟩

omit [Field F] in
theorem normInputs_low (s2 : Fin falcon512.n → F) (c : Committed F) (i : Fin falcon512.n) :
    normInputs s2 c (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.lowIndex i) = c.s1 i :=
  dite_eq_left i.isLt

omit [Field F] in
theorem normInputs_high (s2 : Fin falcon512.n → F) (c : Committed F) (i : Fin falcon512.n) :
    normInputs s2 c (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.highIndex i) = s2 i := by
  have hi : ¬ ((_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.highIndex i : ℕ) < falcon512.n) :=
    Nat.not_lt.mpr (Nat.le_add_right _ _)
  rw [normInputs, dite_eq_right hi]
  exact congrArg _ (Fin.ext (Nat.add_sub_cancel_left ..))

/-- **The signature rows** (`signature.equation`, field equality at `m = q`): for every coefficient,
`c_i − (h · s2)_i − s1_i = 0`. -/
def SignatureRows (h : _root_.Falcon.Rq falcon512.n) (cA : Fin falcon512.n → BitWires F falconSampleBits)
    (s2 : Fin falcon512.n → F) (c : Committed F) : Prop :=
  ∀ i, Emulated.sampleValue cA i -
    LatticeCrypto.negacyclicConvCoeff (fun j => (_root_.GordieHowe.Falcon512.EmulatedAlgebraCircuit.keyCoeffs h j : F)) s2 i -
      c.s1 i = 0

/-- **The `Rows` witness** of the signature rows (`Rows.Wit`): the sample
bits flattened (`16 i + b`), `s2`, `s1`. -/
def sigWit (cA : Fin falcon512.n → BitWires F falconSampleBits) (s2 : Fin falcon512.n → F)
    (c : Committed F) : Rows.Wit F falcon512.n :=
  (fun k => cA (Emulated.sampleBitOf k).1 (Emulated.sampleBitOf k).2, s2, c.s1)

/-- Coefficient `i` of `c` on the `Rows` witness is sample `i` of the sample bits. -/
theorem cCoeff_sigWit (cA : Fin falcon512.n → BitWires F falconSampleBits)
    (s2 : Fin falcon512.n → F) (c : Committed F) (i : Fin falcon512.n) :
    Rows.cCoeff i (sigWit cA s2 c) = Emulated.sampleValue cA i := by
  simp only [Rows.cCoeff, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.comp_apply, LinearMap.proj_apply, Emulated.sampleValue]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Rows.cBits, sigWit, LinearMap.fst_apply, Emulated.sampleBitOf_mk]

/-- The `Rows` key vector is the cast of the key coefficients. -/
theorem keyVec_eq_keyCoeffs (h : _root_.Falcon.Rq falcon512.n) :
    Rows.keyVec (F := F) h = fun j => (_root_.GordieHowe.Falcon512.EmulatedAlgebraCircuit.keyCoeffs h j : F) :=
  rfl

/-- **The signature rows are the rows of `Rows`** on its witness `sigWit`. -/
theorem signatureRows_rowsHold {h : _root_.Falcon.Rq falcon512.n}
    {cA : Fin falcon512.n → BitWires F falconSampleBits} {s2 : Fin falcon512.n → F}
    {c : Committed F} (hs : SignatureRows h cA s2 c) :
    rowsHold (Rows.rows h) (sigWit cA s2 c) := by
  apply _root_.GordieHowe.Falcon512.NativeAlgebraCircuit.Honest.rows_hold_of_eq
  intro k
  rw [cCoeff_sigWit, keyVec_eq_keyCoeffs]
  have := hs k
  change c.s1 k - _ + LatticeCrypto.negacyclicConvCoeff _ s2 k = 0
  linear_combination -this

variable [DecidableEq F]

/-- The `Rows` reading of the samples on the row witness is `cNat`. -/
theorem cNat_sigWit (cA : Fin falcon512.n → BitWires F falconSampleBits)
    (s2 : Fin falcon512.n → F) (c : Committed F) (i : Fin falcon512.n) :
    Rows.cNat (sigWit cA s2 c) i = Emulated.cNat cA i := by
  unfold Rows.cNat Emulated.cNat
  congr 1
  funext b
  simp only [Rows.cBits, sigWit, LinearMap.fst_apply, Emulated.sampleBitOf_mk]

/-- **The algebra constraints of domain A**: the sample bits are bits, the signature rows, the native
norm's constraint groups on `s1 ‖ s2`, and the encoding's Boolean checks. -/
structure AlgebraConstraints (h : _root_.Falcon.Rq falcon512.n)
    (cA : Fin falcon512.n → BitWires F falconSampleBits) (s2 : Fin falcon512.n → F)
    (c : Committed F) : Prop where
  /-- The sample bits are bits. -/
  bits : ∀ i b, cA i b = 0 ∨ cA i b = 1
  /-- The signature rows. -/
  signature : SignatureRows h cA s2 c
  /-- The native norm on `s1 ‖ s2`. -/
  norm : NativeNorm.Holds (normInputs s2 c) c.norm
  /-- The encoding's Boolean checks. -/
  encoding : NativeEncoding.BitsHold c.norm

/-- **The algebra's range requests** below `64`: the norm's digits and the encoding's requests. -/
structure AlgRequests (c : Committed F) : Prop where
  /-- The norm's digits. -/
  norm : NativeNorm.DigitsBelow c.norm
  /-- The encoding's requests. -/
  encoding : NativeEncoding.RequestsHold c.norm c.slackHi

/-- Any representative in `[0, q]` of an `s2` wire casts to the same coefficient as the extracted
`s2Nat` (characteristic `q`). -/
theorem s2Nat_coeff_eq_of_rep [CharP F 12289] (s2 : Fin falcon512.n → F) (i : Fin falcon512.n)
    {a : ℕ} (ha : a ≤ 12289) (hcast : (a : F) = s2 i) :
    (Emulated.s2Nat s2 i : _root_.Falcon.Coeff) = (a : _root_.Falcon.Coeff) := by
  have hex : Range.IsNatBelow (falcon512.q + 1) (s2 i) :=
    ⟨a, by change a < 12289 + 1; omega, hcast⟩
  have hcp : CharP F _root_.Falcon.modulus := by unfold _root_.Falcon.modulus; infer_instance
  have hinj : Function.Injective (ZMod.castHom (dvd_refl _root_.Falcon.modulus) F) :=
    ZMod.castHom_injective F
  apply hinj
  rw [map_natCast, map_natCast]
  unfold Emulated.s2Nat
  rw [(Range.natBelow_spec hex).2, hcast]

/-- **Soundness of the algebra constraints**: with the range requests below `64` (`AlgRequests`),
the algebra constraints at the key `h` give Falcon's algebraic verifier and the encoding bounds on
the extracted values. -/
theorem algebra_sound [CharP F 12289] {h : _root_.Falcon.Rq falcon512.n}
    {cA : Fin falcon512.n → BitWires F falconSampleBits} {s2 : Fin falcon512.n → F}
    {c : Committed F} (hc : AlgebraConstraints h cA s2 c) (hreq : AlgRequests c) :
    Emulated.AlgebraSpec h cA s2 := by
  -- The native norm.
  obtain ⟨vals, hlifted, hmagExact⟩ := NativeNorm.sound_of_holds hreq.norm hc.norm
  -- The encoding.
  obtain ⟨mags, hmagsLifted⟩ := NativeEncoding.sound hreq.norm.a
    ((NativeEncoding.inTable_needles_iff c.norm c.slackHi).mpr hreq.encoding)
    ((NativeEncoding.run_ok_iff c.norm c.slackHi).mpr hc.encoding)
  -- The signature rows, pulled back to `R_q`.
  have hx₁ : ∀ i : Fin falcon512.n, ((vals (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.lowIndex i) : ℕ) : F) =
      Rows.s₁ (sigWit cA s2 c) i :=
    fun i => (hlifted.cast_eq _).trans (normInputs_low s2 c i)
  have hx₂ : ∀ i : Fin falcon512.n, ((vals (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.highIndex i) : ℕ) : F) =
      Rows.s₂ (sigWit cA s2 c) i :=
    fun i => (hlifted.cast_eq _).trans (normInputs_high s2 c i)
  have hbits : Bits.AllBool (Rows.cBits (sigWit cA s2 c)) := fun k => hc.bits _ _
  have hestablish := Rows.establish (signatureRows_rowsHold hc.signature) hbits hx₁ hx₂
  simp only [cNat_sigWit] at hestablish
  have hx₂coeff : ∀ i : Fin falcon512.n,
      (vals (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.highIndex i) : _root_.Falcon.Coeff) =
        (Emulated.s2Nat s2 i : _root_.Falcon.Coeff) := fun i =>
    (s2Nat_coeff_eq_of_rep s2 i (hlifted.bounded _) (hx₂ i)).symm
  have hx₂ofCoeff : (Falcon512.ofCoeff fun i =>
      (vals (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.highIndex i) : _root_.Falcon.Coeff)) =
        Emulated.decodeS2 s2 := by
    unfold Emulated.decodeS2
    exact congrArg Falcon512.ofCoeff (funext hx₂coeff)
  rw [hx₂ofCoeff] at hestablish
  have halgebra : Falcon512.algebraOk falcon512 h
      (Falcon512.ofCoeff fun i => (Emulated.cNat cA i : _root_.Falcon.Coeff))
      (Emulated.decodeS2 s2) := by
    unfold Falcon512.algebraOk
    rw [hestablish, Falcon512.pairL2NormSq_eq_sum_append, Falcon512.coeff_ofCoeff]
    have happend : Fin.append
        (fun i : Fin falcon512.n =>
          (vals (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.lowIndex i) : _root_.Falcon.Coeff))
        (Falcon512.coeff (Emulated.decodeS2 s2)) =
        fun i : Fin (falcon512.n + falcon512.n) =>
          (vals (Fin.cast _root_.GordieHowe.Falcon512.NativeAlgebraCircuit.normAppend_eq i) : _root_.Falcon.Coeff) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]
        rfl
      · rw [Fin.append_right]
        dsimp only [Emulated.decodeS2]
        rw [Falcon512.coeff_ofCoeff]
        exact (hx₂coeff i).symm
    rw [happend]
    calc
      _ = ∑ i : Fin 1024,
          (LatticeCrypto.centeredRepr (vals i : _root_.Falcon.Coeff)).natAbs ^ 2 :=
        Fintype.sum_equiv (finCongr _root_.GordieHowe.Falcon512.NativeAlgebraCircuit.normAppend_eq) _ _ (fun _ => rfl)
      _ ≤ falcon512.βSq := hlifted.norm
  have hmagEq : ∀ i : Fin falcon512.n,
      (LatticeCrypto.centeredRepr (Falcon512.coeff (Emulated.decodeS2 s2) i)).natAbs =
        mags i := by
    intro i
    obtain ⟨a, haLt, haCast, haEq⟩ :=
      hmagExact (_root_.GordieHowe.Falcon512.NativeAlgebraCircuit.highIndex i) (Nat.le_add_right _ _)
    have heqF : (a : F) = (mags i : F) := haCast.trans (hmagsLifted.cast_eq i).symm
    have haNat : a = mags i := IntLift.natCast_inj_of_lt (K := F)
      (haLt.trans_le (by norm_num))
      ((hmagsLifted.bounded i).trans_le (by rw [Codec.magnitudeBound_eq]; norm_num)) heqF
    rw [← haNat, ← haEq]
    dsimp only [Emulated.decodeS2]
    rw [Falcon512.coeff_ofCoeff]
    exact congrArg (fun x => (LatticeCrypto.centeredRepr x).natAbs) (hx₂coeff i).symm
  have hencoding : Falcon512.EncodingBounds falcon512 (Emulated.decodeS2Int s2) := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [Emulated.decodeS2Int, Vector.get_ofFn, hmagEq i]
      exact hmagsLifted.bounded i
    · simp only [Emulated.decodeS2Int, Vector.get_ofFn, hmagEq]
      exact hmagsLifted.highSum
  exact ⟨halgebra, hencoding⟩

end GordieHowe.Falcon512.Native
