-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.System.Algebra
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Params
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Scheme
public import GordieHowe.Applications.Falcon512.NegacyclicSpectrum
public import GordieHowe.Applications.Falcon512.Spec.KeyNTT

@[expose] public section

/-!
# Falcon ring, native arm: the algebra constraints

The algebra of the native Falcon ring (`lib/gordiehowe/examples/rings/falcon_ring.h`,
`falcon_ring_native`) in domain `A` over a field `F` of characteristic `q = 12289`, on the
committed key spectrum `key.spectrum` (`n` subfield values), the private input `s2` and Falcon
native's algebra advice (`GordieHowe.Falcon512.Native.Committed`: `signature.s1`, the native norm's witness,
`enc.slack_hi`):

* **The transform root** (`psiF`, `isPrimitiveRoot_psiF`, `psiF_pow`): `ψ = 10302`, a primitive
  `2n`-th root of unity in `F`.
* **The spectral signature relation** (`SpectralRows`, `falcon_ring.h:194-225`,
  `native_signature_relation`): `Ntt(c − s1) = spectrum ⊙ Ntt(s2)` coefficientwise, the transform
  in natural order at `ψ` (`DFT.negSpectrum`), `c` the statement's challenge.
* **The algebra constraints** (`RingAlgebra`): the spectral relation, the native norm on
  `s1 ‖ s2` and the encoding's Boolean checks (Falcon native's, `examples/rings/falcon_ring.h`).
* **The key record** (`keyRecord`): the natural-order transform of a key, the record of the ring's
  public table (`falcon_ring.h:180-189`, `RowMap::negacyclic(…, psi, NttOrder::kNatural)`).

**Soundness** (`ringAlgebra_sound`): when the spectrum is the key record of a key `h`, the
spectral relation is `c − s1 = h · s2` in `R_q` (`sub_eq_negacyclicConv_of_spectralRows`: the
transform turns the negacyclic product into the pointwise product,
`DFT.negSpectrum_negacyclicConvCoeff`, and is injective, `DFT.negSpectrum_injective`), which is
Falcon native's signature rows at the sample bits of `c` (`algebraConstraints_of_ringAlgebra`:
`GordieHowe.Falcon512.Native.SignatureRows` at `FalconEmulated.sampleBits c`, a proof device: the ring has no
sample bits, `c` is public); Falcon native's `algebra_sound` then gives Falcon's algebraic verifier
and the encoding bounds on `c` and the extracted `s2`.

**The honest algebra facts** (`HonestAlgebra`): Falcon's algebraic verifier on the challenge and
the signature polynomial, and the encoding bounds of the signature polynomial.
-/

namespace GordieHowe.Falcon512.Ring.Native

open GordieHowe.Bits GordieHowe.DFT
open GordieHowe.Falcon512.Native (Committed normInputs SignatureRows AlgebraConstraints
  AlgRequests algebra_sound normInputs_low normInputs_high)

/-! ### The transform root -/

section Root

variable (F : Type) [Field F]

/-- **The transform root** `ψ = 10302` in `F` (`falcon_ring.h:85`, `kNativePsi`). -/
def psiF : F := ((Params.psi : ℕ) : F)

variable [CharP F 12289]

/-- `ψ` is a primitive `1024`-th root of unity in every field of characteristic `q`
(`KeyNTT.falconRoot2n_512_isPrimitiveRoot`, the root `falcon_root_2n(512, 12289) = 10302`). -/
theorem isPrimitiveRoot_psiF : IsPrimitiveRoot (psiF F) (2 * falcon512.n) := by
  have h := KeyNTT.falconRoot2n_512_isPrimitiveRoot.map_of_injective
    (ZMod.castHom_injective (n := 12289) F)
  rw [KeyNTT.falconRoot2n_512, map_natCast] at h
  exact h

/-- `ψ ^ n = -1`. -/
theorem psiF_pow : psiF F ^ falcon512.n = -1 :=
  DFT.IsPrimitiveRoot.pow_half_eq_neg_one (isPrimitiveRoot_psiF F) (by decide)

/-- `n = 512` is nonzero in `F`. -/
theorem natCast_n_ne_zero : ((falcon512.n : ℕ) : F) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff F 12289]
  decide

end Root

variable {F : Type} [Field F]

/-- **The key record** of a key: its natural-order transform at `ψ`, the record of its row in the
ring's public table. -/
def keyRecord (pk : PublicKey) : Fin falcon512.n → F :=
  negSpectrum (psiF F) fun j => (EmulatedAlgebraCircuit.keyCoeffs (n := falcon512.n) pk.h j : F)

/-! ### The algebra constraints -/

variable [DecidableEq F]

/-- **The spectral signature relation** (`signature.equation`, `assert_spectral(c − s1,
SpectralProduct(spectrum, s2))`): for every frequency `k`, `Ntt(c − s1)_k = spectrum_k ·
Ntt(s2)_k`. -/
def SpectralRows (c spectrum s2 : Fin falcon512.n → F) (alg : Committed F) : Prop :=
  ∀ k, negSpectrum (psiF F) (c - alg.s1) k = spectrum k * negSpectrum (psiF F) s2 k

/-- **The algebra constraints of the native Falcon ring** at the challenge `c`: the spectral
signature relation, the native norm on `s1 ‖ s2` and the encoding's Boolean checks. -/
structure RingAlgebra (c spectrum s2 : Fin falcon512.n → F) (alg : Committed F) : Prop where
  /-- The spectral signature relation. -/
  signature : SpectralRows c spectrum s2 alg
  /-- The native norm on `s1 ‖ s2`. -/
  norm : NativeNorm.Holds (normInputs s2 alg) alg.norm
  /-- The encoding's Boolean checks. -/
  encoding : NativeEncoding.BitsHold alg.norm

variable [CharP F 12289]

/-- **The spectral relation at a key record is the signature relation**: `c − s1 = h · s2`
coefficientwise (the negacyclic product of the key's coefficients and `s2`). -/
theorem sub_eq_negacyclicConv_of_spectralRows {pk : PublicKey} {c s2 : Fin falcon512.n → F}
    {alg : Committed F} (h : SpectralRows c (keyRecord pk) s2 alg) :
    c - alg.s1 = LatticeCrypto.negacyclicConvCoeff
      (fun j => (EmulatedAlgebraCircuit.keyCoeffs (n := falcon512.n) pk.h j : F)) s2 := by
  apply negSpectrum_injective (isPrimitiveRoot_psiF F) (natCast_n_ne_zero F)
  rw [negSpectrum_negacyclicConvCoeff (psiF_pow F)]
  funext k
  exact h k

omit [CharP F 12289] in
/-- The sample bits of a public challenge below `2^16` read back the challenge. -/
theorem cNat_sampleBits {c : Fin falcon512.n → ℕ}
    (hc : ∀ i, c i < 2 ^ falconSampleBits) :
    Emulated.cNat (Emulated.sampleBits (K := F) c) = c :=
  funext fun i => Emulated.natOfBits_sampleBits hc i

/-- **The ring's algebra constraints give Falcon native's at the sample bits of the challenge**,
when the spectrum is the key record of `pk` (a proof device: the ring commits no sample bits). -/
theorem algebraConstraints_of_ringAlgebra {pk : PublicKey}
    {c : Fin falcon512.n → ℕ} (hc : ∀ i, c i < 2 ^ falconSampleBits) {s2 : Fin falcon512.n → F}
    {alg : Committed F} (h : RingAlgebra (fun i => (c i : F)) (keyRecord pk) s2 alg) :
    AlgebraConstraints pk.h (Emulated.sampleBits c) s2 alg where
  bits i b := Emulated.sampleBits_bool _ i b
  signature i := by
    have hrow := congrFun (sub_eq_negacyclicConv_of_spectralRows h.signature) i
    have hval : Emulated.sampleValue (Emulated.sampleBits (K := F) c) i = (c i : F) := by
      rw [← Emulated.cNat_cast (fun i b => Emulated.sampleBits_bool _ i b),
        cNat_sampleBits hc]
    rw [hval, ← hrow, Pi.sub_apply]
    ring
  norm := h.norm
  encoding := h.encoding

/-- **Soundness of the ring's algebra**: when the spectrum is the key record of `pk`, the algebra
constraints at the challenge `c` (below `2^16`) and the algebra's range requests give Falcon's
algebraic verifier on `c` and the extracted `s2`, and the encoding bounds
(`Native.algebra_sound`). -/
theorem ringAlgebra_sound {pk : PublicKey} {c : Fin falcon512.n → ℕ}
    (hc : ∀ i, c i < 2 ^ falconSampleBits) {s2 : Fin falcon512.n → F} {alg : Committed F}
    (h : RingAlgebra (fun i => (c i : F)) (keyRecord pk) s2 alg) (hreq : AlgRequests alg) :
    Falcon512.algebraOk falcon512 pk.h (Falcon512.ofCoeff fun i => (c i : _root_.Falcon.Coeff))
        (Emulated.decodeS2 s2) ∧
      Falcon512.EncodingBounds falcon512 (Emulated.decodeS2Int s2) := by
  have hspec := algebra_sound (algebraConstraints_of_ringAlgebra hc h) hreq
  have ha := hspec.algebra
  rw [cNat_sampleBits hc] at ha
  exact ⟨ha, hspec.encoding⟩

/-! ### The honest prover -/

variable {pk : PublicKey} {c : Fin falcon512.n → ℕ} {s : _root_.Falcon.IntPoly 512}

/-- **The honest algebra facts**: Falcon's algebraic verifier on `c` and `s`, and the encoding
bounds of `s`. -/
structure HonestAlgebra (pk : PublicKey) (c : Fin falcon512.n → ℕ)
    (s : _root_.Falcon.IntPoly 512) : Prop where
  /-- Falcon's algebraic verifier. -/
  algebra : Falcon512.algebraOk falcon512 pk.h (Falcon512.ofCoeff fun j => (c j : _root_.Falcon.Coeff))
    s.toRq
  /-- The encoding bounds. -/
  encoding : Falcon512.EncodingBounds falcon512 s

end GordieHowe.Falcon512.Ring.Native
