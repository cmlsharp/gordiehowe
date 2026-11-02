-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.SecondSignature

@[expose] public section

/-!
# The key-free ML-DSA signing attempt

One idealized FIPS 204 signing attempt (`Ideal.lean`: the mask `y` uniform on the mask box, the
commitment hash `c̃` uniform) outputs its commitment `w₁ = HighBits(Â·y)` and its signature
`(c̃, z, h)`, `z = y + c·s₁`. Its law equals the law of an attempt that reads only the published key
`(ρ, t₁, t₀)`: draw `z` uniform on the mask box and `c̃` uniform, compute
`Â·z − c·t = Â·z − c·t₁·2^d − c·t₀`, run the four checks of FIPS 204 Algorithm 7 on it and output
`HighBits(Â·z − c·t)` with `(c̃, z, MakeHint(−c·t₀, Â·z − c·t₁·2^d))`. This is the shift argument
of the zero-knowledge proof of the Dilithium round 3 specification (Version 3.1, §3.1 and Appendix
B) and of KLS18 §4.3.1 (Kiltz–Lyubashevsky–Schaffner, Eurocrypt 2018) with `t₀` public, and the two
laws are equal, with no statistical error.

The proof shifts the mask: `(y, c̃) ↦ (y + c·s₁, c̃)` is a bijection from the accepted pairs of the
ideal attempt onto the accepted pairs of the key-free attempt, both in the mask box (the z-check
`‖z‖∞ < γ₁ − β` and `‖c·s₁‖∞ ≤ β` put `z` and `y = z − c·s₁` in `(−γ₁, γ₁]`), with the same
output; it extends to a permutation of all pairs, the rejected pairs of the two attempts having
the same number.

* `exists_equiv_comp_eq_of_isSome`, `PMF.map_uniformOfFintype_comp_equiv`,
  `PMF.map_uniformOfFintype_eq_of_isSome`: maps `φ, ψ` exchanging the accepted points of
  `f, g : α → Option β` with equal outputs give a permutation `σ` with `g ∘ σ = f`, so `f` and `g`
  push the uniform law to the same law.
* `inMaskBox_of_polyVecNorm_lt`, `inMaskBox_of_zCheck`, `inMaskBox_sub_of_zCheck`: a vector
  passing the z-check, and the vector minus a shift of norm at most `β`, lie in the mask box;
  `rqVec_add_sub_cancel`, `rqVec_sub_add_cancel`.
* `keyFreeWApprox`, `keyFreeCommit`, `keyFreeHint`, `keyFreeAccept`, `keyFreeSig`, `keyFreeW1`:
  `w'_Approx = Â·z − c·t₁·2^d` (FIPS 204 Algorithm 8 line 9), `Â·z − c·t`, the hint, the four
  checks, the signature and the commitment computed from the public key `(ρ, t₁)` and `t₀`.
* `keyFreeWApprox_add`, `keyFreeCommit_add`: **the public form of the attempt**: for an honest key
  and `z = y + c·s₁`, `Â·z − c·t₁·2^d = Â·y − c·s₂ + c·t₀` and `Â·z − c·t = Â·y − c·s₂`.
* `keyFreeHint_add`, `keyFreeAccept_add`, `keyFreeSig_add`, `keyFreeW1_add`: for an honest key the
  key-free hint and checks at `y + c·s₁` are `attemptHint` and `signAccept` at `y`, the key-free
  signature is `attemptOutput`, and on acceptance the key-free commitment is `HighBits(Â·y)`.
* `idealAttemptW1`, `idealAttemptW1Law`, `map_snd_idealAttemptW1Law`: the ideal attempt with its
  commitment `realBuckets`, whose signature law is `idealAttemptLaw`; `keyFreeAttempt`,
  `keyFreeAttemptLaw`; `maskAdd`, `maskSub`: the shift inside the mask box.
* `idealAttemptW1_eq_keyFreeAttempt`, `exists_equiv_keyFreeAttempt`,
  `idealAttemptW1Law_eq_keyFreeAttemptLaw`: **the ideal and the key-free attempt have the same
  law** of `Option (w₁, σ)`, for an honest key with `‖s₁‖∞, ‖s₂‖∞ ≤ η`, given the signing and
  verification laws and an encoding coherent with `bucketsOf`.
* `keptCall`, `map_uniformOfFintype_keptCall_eq`, `outWeight`, `idealCall`, `idealCallLaw`,
  `keyFreeCall`, `keyFreeCallLaw`, `idealCallLaw_eq_keyFreeCallLaw`: **one call** of `T` attempts
  with independent uniform pairs `(mask, c̃)` and a keep coin on `Fin D`, the first accepted
  output kept when the coin is below `D · wt(w₁, c̃)`: the ideal and the key-free call have the
  same law for every keep weight `wt`.
* `flattenCoin_eq_flattenKeep_t0Weight`, `idealCallLaw_flattenCoin_eq`: the signer's flattening
  coin is a function of its published `t₀`, so the ideal call kept with it has the law of the
  key-free call kept with the weight of the published `t₀`.
* `idealAttemptW1Law_eq_keyFreeAttemptLaw_concrete`, `idealCallLaw_eq_keyFreeCallLaw_concrete`:
  the hypotheses hold at the concrete primitives for every seed at every approved parameter set.
-/

open scoped ENNReal

/-- **Exchanging the accepted points of two maps** to `Option β` on a finite type: if `φ` sends
every point accepted by `f` to a point where `g` gives the same output, `ψ` sends every point
accepted by `g` to a point where `f` gives the same output, and the two are inverse there, then
some permutation `σ` has `g ∘ σ = f` (it is `φ` on the points accepted by `f`). -/
theorem exists_equiv_comp_eq_of_isSome {α β : Type*} [Fintype α]
    (f g : α → Option β) (φ ψ : α → α)
    (hφ : ∀ a, (f a).isSome → g (φ a) = f a ∧ ψ (φ a) = a)
    (hψ : ∀ a, (g a).isSome → f (ψ a) = g a ∧ φ (ψ a) = a) :
    ∃ σ : α ≃ α, ∀ a, g (σ a) = f a := by
  classical
  let e : {a // (f a).isSome} ≃ {a // (g a).isSome} :=
    { toFun := fun a => ⟨φ a.1, by rw [(hφ a.1 a.2).1]; exact a.2⟩
      invFun := fun a => ⟨ψ a.1, by rw [(hψ a.1 a.2).1]; exact a.2⟩
      left_inv := fun a => Subtype.ext (hφ a.1 a.2).2
      right_inv := fun a => Subtype.ext (hψ a.1 a.2).2 }
  have hc : Fintype.card {a // ¬ (f a).isSome} = Fintype.card {a // ¬ (g a).isSome} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_congr e]
  let σ : α ≃ α := Equiv.subtypeCongr e (Fintype.equivOfCardEq hc)
  have hσ : ∀ a, g (σ a) = f a := by
    intro a
    by_cases ha : (f a).isSome
    · have h1 : σ a = φ a := by simp [σ, Equiv.subtypeCongr, ha, e]
      rw [h1]
      exact (hφ a ha).1
    · have h0 : σ a = ((Fintype.equivOfCardEq hc) ⟨a, ha⟩).1 := by
        simp [σ, Equiv.subtypeCongr, ha]
      rw [h0]
      have h1 := ((Fintype.equivOfCardEq hc) ⟨a, ha⟩).2
      rw [Option.not_isSome_iff_eq_none] at h1 ha
      rw [h1, ha]
  exact ⟨σ, hσ⟩

namespace PMF

/-- A uniform law pushed through `F ∘ σ` for a permutation `σ` is pushed through `F`. -/
theorem map_uniformOfFintype_comp_equiv {α β : Type*} [Fintype α] [Nonempty α] (σ : α ≃ α)
    (F : α → β) : (uniformOfFintype α).map (F ∘ σ) = (uniformOfFintype α).map F := by
  rw [← map_comp, map_uniformOfFintype_equiv]

/-- **Exchanging the accepted points of two maps** to `Option β` (`exists_equiv_comp_eq_of_isSome`):
`f` and `g` push the uniform law to the same law. -/
theorem map_uniformOfFintype_eq_of_isSome {α β : Type*} [Fintype α] [Nonempty α]
    (f g : α → Option β) (φ ψ : α → α)
    (hφ : ∀ a, (f a).isSome → g (φ a) = f a ∧ ψ (φ a) = a)
    (hψ : ∀ a, (g a).isSome → f (ψ a) = g a ∧ φ (ψ a) = a) :
    (uniformOfFintype α).map f = (uniformOfFintype α).map g := by
  obtain ⟨σ, hσ⟩ := exists_equiv_comp_eq_of_isSome f g φ ψ hφ hψ
  rw [show f = g ∘ σ from funext fun a => (hσ a).symm, map_uniformOfFintype_comp_equiv]

end PMF

namespace GordieHowe.MLDSA

open _root_.MLDSA LatticeCrypto TransformOps PMF

/-! ### The mask box and the z-check -/

section Box

/-- A vector of centered `∞`-norm below `γ₁` lies in the mask box `(−γ₁, γ₁]`. -/
theorem inMaskBox_of_polyVecNorm_lt {γ₁ l : ℕ} {z : RqVec l} (h : polyVecNorm z < γ₁) :
    InMaskBox γ₁ z := by
  have h' := (polyVecNorm_lt_iff z (lt_of_le_of_lt (Nat.zero_le _) h)).1 h
  intro j i
  have := h' j i
  omega

variable {p : Params}

/-- A vector passing the z-check lies in the mask box. -/
theorem inMaskBox_of_zCheck {z : RqVec p.l} (hz : zCheck z = true) : InMaskBox p.gamma1 z := by
  simp only [zCheck, decide_eq_true_eq] at hz
  exact inMaskBox_of_polyVecNorm_lt (lt_of_lt_of_le hz (Nat.sub_le _ _))

/-- **The mask behind an accepted response lies in the mask box**: if `z` passes the z-check
`‖z‖∞ < γ₁ − β` and `‖v‖∞ ≤ β`, then `z − v` lies in `(−γ₁, γ₁]`. -/
theorem inMaskBox_sub_of_zCheck {z v : RqVec p.l} (hz : zCheck z = true)
    (hv : polyVecNorm v ≤ p.beta) : InMaskBox p.gamma1 (z - v) := by
  simp only [zCheck, decide_eq_true_eq] at hz
  exact inMaskBox_of_polyVecNorm_lt ((polyVecNorm_sub_le z v).trans_lt (by omega))

end Box

/-- `(a + b) − b = a` in `R_q^k`. -/
theorem rqVec_add_sub_cancel {k : ℕ} (a b : RqVec k) : a + b - b = a :=
  Vector.ext fun i _ => by
    rw [Vector.getElem_sub, Vector.getElem_add]; exact add_sub_cancel_right _ _

/-- `(a − b) + b = a` in `R_q^k`. -/
theorem rqVec_sub_add_cancel {k : ℕ} (a b : RqVec k) : a - b + b = a :=
  Vector.ext fun i _ => by
    rw [Vector.getElem_add, Vector.getElem_sub]; exact sub_add_cancel _ _

/-! ### The attempt from the published key -/

section KeyFree

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]

/-- `w'_Approx = Â·z − c·t₁·2^d` with `Â = ExpandA(ρ)` and `c = SampleInBall(c̃)` (FIPS 204
Algorithm 8, line 9), from the public key `(ρ, t₁)`. -/
def keyFreeWApprox (pk : PublicKey p prims) (z : RqVec p.l) (cTilde : CommitHashBytes p) :
    RqVec p.k :=
  computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde) z pk.t1

/-- `Â·z − c·t` with `t = t₁·2^d + t₀`: `w'_Approx − c·t₀`, from the published `(ρ, t₁, t₀)`. -/
def keyFreeCommit (pk : PublicKey p prims) (t0 : RqVec p.k) (z : RqVec p.l)
    (cTilde : CommitHashBytes p) : RqVec p.k :=
  keyFreeWApprox prims pk z cTilde - prims.sampleInBall cTilde • t0

/-- The hint `MakeHint(−c·t₀, Â·z − c·t₁·2^d)` from the published key. -/
def keyFreeHint (pk : PublicKey p prims) (t0 : RqVec p.k) (z : RqVec p.l)
    (cTilde : CommitHashBytes p) : Vector prims.Hint p.k :=
  prims.makeHintVec (-(prims.sampleInBall cTilde • t0)) (keyFreeWApprox prims pk z cTilde)

/-- **The four checks of FIPS 204 Algorithm 7 (lines 23 and 28) from the published key**: the
z-check on `z`, the r0-check on `LowBits(Â·z − c·t)`, the ct₀-check and the hint count. -/
def keyFreeAccept (pk : PublicKey p prims) (t0 : RqVec p.k) (z : RqVec p.l)
    (cTilde : CommitHashBytes p) : Bool :=
  zCheck z && r0Check (prims.lowBitsVec (keyFreeCommit prims pk t0 z cTilde)) &&
    ct0Check (prims.sampleInBall cTilde • t0) && hintCheck prims (keyFreeHint prims pk t0 z cTilde)

/-- The key-free signature `(c̃, z, h)`. -/
def keyFreeSig (pk : PublicKey p prims) (t0 : RqVec p.k) (z : RqVec p.l)
    (cTilde : CommitHashBytes p) : FIPSSignature p prims :=
  ⟨cTilde, z, keyFreeHint prims pk t0 z cTilde⟩

/-- The key-free commitment `HighBits(Â·z − c·t)`, as a bucket vector. -/
def keyFreeW1 (pk : PublicKey p prims) (t0 : RqVec p.k) (z : RqVec p.l)
    (cTilde : CommitHashBytes p) : BucketVec p :=
  bucketsOf (rqVecCoeffs (keyFreeCommit prims pk t0 z cTilde))

variable {prims}

/-- **The public form of `w'_Approx`**: for the key of `seed` and `z = y + c·s₁`,
`Â·z − c·t₁·2^d = Â·y − c·s₂ + c·t₀` (`VerifyLaws.wApprox_eq`). -/
theorem keyFreeWApprox_add (hv : VerifyLaws prims) {seed : Bytes 32} {pk : PublicKey p prims}
    {sk : SecretKey p} (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) :
    keyFreeWApprox prims pk (y + prims.sampleInBall cTilde • sk.s1) cTilde =
      prims.expandA pk.rho * y - prims.sampleInBall cTilde • sk.s2 +
        prims.sampleInBall cTilde • sk.t0 :=
  hv.wApprox_eq prims seed hkeygen _ y

/-- **The public form of the attempt**: for the key of `seed` and `z = y + c·s₁`,
`Â·z − c·t = Â·y − c·s₂`. -/
theorem keyFreeCommit_add (hv : VerifyLaws prims) {seed : Bytes 32} {pk : PublicKey p prims}
    {sk : SecretKey p} (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) :
    keyFreeCommit prims pk sk.t0 (y + prims.sampleInBall cTilde • sk.s1) cTilde =
      prims.expandA pk.rho * y - prims.sampleInBall cTilde • sk.s2 := by
  rw [keyFreeCommit, keyFreeWApprox_add hv hkeygen, rqVec_add_sub_cancel]

/-- The key-free hint at `y + c·s₁` is the attempt's hint at `y`. -/
theorem keyFreeHint_add (hv : VerifyLaws prims) {seed : Bytes 32} {pk : PublicKey p prims}
    {sk : SecretKey p} (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) :
    keyFreeHint prims pk sk.t0 (y + prims.sampleInBall cTilde • sk.s1) cTilde =
      attemptHint prims sk (prims.expandA pk.rho) y cTilde := by
  rw [keyFreeHint, keyFreeWApprox_add hv hkeygen, attemptHint]

/-- **The key-free checks at `y + c·s₁` are the attempt's checks at `y`**, for the key of
`seed`. -/
theorem keyFreeAccept_add (hv : VerifyLaws prims) {seed : Bytes 32} {pk : PublicKey p prims}
    {sk : SecretKey p} (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (y : RqVec p.l)
    (cTilde : CommitHashBytes p) :
    keyFreeAccept prims pk sk.t0 (y + prims.sampleInBall cTilde • sk.s1) cTilde =
      signAccept prims sk (prims.expandA pk.rho) y cTilde := by
  rw [keyFreeAccept, keyFreeCommit_add hv hkeygen, keyFreeHint_add hv hkeygen, signAccept]

/-- The key-free signature at `y + c·s₁` is the attempt's signature at `y`. -/
theorem keyFreeSig_add [Nonempty (MaskBox p)] (hv : VerifyLaws prims) {seed : Bytes 32}
    {pk : PublicKey p prims} {sk : SecretKey p} (hkeygen : keyGenFromSeed p prims seed = (pk, sk))
    (y : MaskBox p) (cTilde : CommitHashBytes p) :
    keyFreeSig prims pk sk.t0 (y.1 + prims.sampleInBall cTilde • sk.s1) cTilde =
      attemptOutput prims sk (prims.expandA pk.rho) (y, cTilde) := by
  rw [keyFreeSig, keyFreeHint_add hv hkeygen, attemptOutput]

/-- **On acceptance the key-free commitment is the attempt's commitment** `HighBits(Â·y)`, for the
key of `seed` with `‖s₂‖∞ ≤ η`, given the signing and verification laws and an encoding `enc`
coherent with `bucketsOf` (`SigningLaws.highBitsVec_sub_eq_of_isSome`). -/
theorem keyFreeW1_add (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs2 : polyVecBounded sk.s2 p.eta)
    (y : RqVec p.l) (cTilde : CommitHashBytes p)
    (hacc : signAccept prims sk (prims.expandA pk.rho) y cTilde = true) :
    keyFreeW1 prims pk sk.t0 (y + prims.sampleInBall cTilde • sk.s1) cTilde =
      bucketsOf (rqVecCoeffs (prims.expandA pk.rho * y)) := by
  have hsome : (idealAttempt prims sk (prims.expandA pk.rho) y cTilde).isSome := by
    rw [idealAttempt_eq_ite, ite_eq_left hacc]; rfl
  rw [keyFreeW1, keyFreeCommit_add hv hkeygen, ← henc, ← henc,
    h_laws.highBitsVec_sub_eq_of_isSome prims hs2 hsome]

end KeyFree

/-! ### The two attempt laws -/

section Law

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)]

/-- **One ideal attempt with its commitment**: on the four checks of `signAccept`, the commitment
`w₁ = HighBits(Â·y)` (`realBuckets`) and the signature `(c̃, y + c·s₁, h)`. -/
def idealAttemptW1 (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (yc : MaskBox p × CommitHashBytes p) : Option (BucketVec p × FIPSSignature p prims) :=
  if attemptAccept prims sk aHat yc.1 yc.2 then
    some (realBuckets aHat yc.1, attemptOutput prims sk aHat yc)
  else none

/-- **The law of one ideal attempt with its commitment**: `y` uniform on the mask box and `c̃`
uniform, independent. -/
noncomputable def idealAttemptW1Law (sk : SecretKey p) (aHat : TqMatrix p.k p.l) :
    PMF (Option (BucketVec p × FIPSSignature p prims)) :=
  (uniformOfFintype (MaskBox p × CommitHashBytes p)).map (idealAttemptW1 prims sk aHat)

/-- The signature law of `idealAttemptW1Law` is `idealAttemptLaw`. -/
theorem map_snd_idealAttemptW1Law (sk : SecretKey p) (aHat : TqMatrix p.k p.l) :
    (idealAttemptW1Law prims sk aHat).map (Option.map Prod.snd) =
      idealAttemptLaw prims sk aHat := by
  rw [idealAttemptW1Law, map_comp, uniformOfFintype_prod_eq_bind, map_bind, idealAttemptLaw,
    maskUniform]
  congr 1
  funext y
  rw [map_comp]
  congr 1
  funext c
  simp only [Function.comp_apply, idealAttemptW1, idealAttempt_eq_ite, attemptAccept]
  by_cases h : signAccept prims sk aHat y.1 c <;> simp [h, attemptOutput]

/-- **One key-free attempt**: on the key-free checks at `(z, c̃)`, the commitment
`HighBits(Â·z − c·t)` and the signature `(c̃, z, h)`, from the published `(ρ, t₁)` and `t₀`. -/
def keyFreeAttempt (pk : PublicKey p prims) (t0 : RqVec p.k)
    (zc : MaskBox p × CommitHashBytes p) : Option (BucketVec p × FIPSSignature p prims) :=
  if keyFreeAccept prims pk t0 zc.1.1 zc.2 then
    some (keyFreeW1 prims pk t0 zc.1.1 zc.2, keyFreeSig prims pk t0 zc.1.1 zc.2)
  else none

/-- **The law of one key-free attempt**: `z` uniform on the mask box and `c̃` uniform,
independent. -/
noncomputable def keyFreeAttemptLaw (pk : PublicKey p prims) (t0 : RqVec p.k) :
    PMF (Option (BucketVec p × FIPSSignature p prims)) :=
  (uniformOfFintype (MaskBox p × CommitHashBytes p)).map (keyFreeAttempt prims pk t0)

/-- Add `v` to a mask when the sum stays in the mask box; otherwise keep the mask. -/
def maskAdd (v : RqVec p.l) (y : MaskBox p) : MaskBox p :=
  if h : InMaskBox p.gamma1 (y.1 + v) then ⟨y.1 + v, h⟩ else y

/-- Subtract `v` from a mask when the difference stays in the mask box; otherwise keep the mask. -/
def maskSub (v : RqVec p.l) (y : MaskBox p) : MaskBox p :=
  if h : InMaskBox p.gamma1 (y.1 - v) then ⟨y.1 - v, h⟩ else y

variable {prims}

/-- **The ideal attempt at `y` is the key-free attempt at `z = y + c·s₁`**, for the key of `seed`
with `‖s₂‖∞ ≤ η`, given the signing and verification laws and a coherent encoding. -/
theorem idealAttemptW1_eq_keyFreeAttempt (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs2 : polyVecBounded sk.s2 p.eta)
    (y z : MaskBox p) (cTilde : CommitHashBytes p)
    (hz : z.1 = y.1 + prims.sampleInBall cTilde • sk.s1) :
    idealAttemptW1 prims sk (prims.expandA pk.rho) (y, cTilde) =
      keyFreeAttempt prims pk sk.t0 (z, cTilde) := by
  unfold idealAttemptW1 keyFreeAttempt
  dsimp only
  rw [hz, keyFreeAccept_add hv hkeygen]
  by_cases hacc : signAccept prims sk (prims.expandA pk.rho) y.1 cTilde
  · rw [ite_eq_left hacc, ite_eq_left (by exact hacc),
      keyFreeW1_add h_laws hv henc hkeygen hs2 _ _ hacc,
      keyFreeSig_add hv hkeygen]
    rfl
  · rw [ite_eq_right hacc, ite_eq_right (by exact hacc)]

/-- **A permutation of the pairs `(mask, c̃)` carries the ideal attempt to the key-free one**:
`keyFreeAttempt ∘ σ = idealAttemptW1`, with `σ (y, c̃) = (y + c·s₁, c̃)` on the accepted pairs. For
the key of `seed` with `‖s₁‖∞, ‖s₂‖∞ ≤ η`, given the signing and verification laws and an encoding
`enc` coherent with `bucketsOf`. -/
theorem exists_equiv_keyFreeAttempt (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims) {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs1 : polyVecBounded sk.s1 p.eta)
    (hs2 : polyVecBounded sk.s2 p.eta) :
    ∃ σ : MaskBox p × CommitHashBytes p ≃ MaskBox p × CommitHashBytes p,
      ∀ a, keyFreeAttempt prims pk sk.t0 (σ a) =
        idealAttemptW1 prims sk (prims.expandA pk.rho) a := by
  set cs : CommitHashBytes p → RqVec p.l := fun c => prims.sampleInBall c • sk.s1
  have hcs : ∀ c, polyVecNorm (cs c) ≤ p.beta := fun c =>
    h_laws.polyVecNorm_sampleInBall_smul_le prims c sk.s1 hs1
  refine exists_equiv_comp_eq_of_isSome _ _
    (fun yc => (maskAdd (cs yc.2) yc.1, yc.2)) (fun zc => (maskSub (cs zc.2) zc.1, zc.2)) ?_ ?_
  · rintro ⟨y, c⟩ hsome
    have hacc : signAccept prims sk (prims.expandA pk.rho) y.1 c = true := by
      by_contra h
      simp [idealAttemptW1, attemptAccept, h] at hsome
    have hbox : InMaskBox p.gamma1 (y.1 + cs c) := by
      refine inMaskBox_of_zCheck ?_
      rw [← keyFreeAccept_add hv hkeygen] at hacc
      simp only [keyFreeAccept, Bool.and_eq_true] at hacc
      exact hacc.1.1.1
    have hadd : maskAdd (cs c) y = ⟨y.1 + cs c, hbox⟩ := dite_eq_left hbox
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [hadd]
      exact (idealAttemptW1_eq_keyFreeAttempt h_laws hv henc hkeygen hs2 y _ c rfl).symm
    · dsimp only
      rw [hadd]
      have hsub : InMaskBox p.gamma1 (y.1 + cs c - cs c) := by
        rw [rqVec_add_sub_cancel]; exact y.2
      rw [maskSub, dite_eq_left hsub]
      exact Prod.ext (Subtype.ext (rqVec_add_sub_cancel _ _)) rfl
  · rintro ⟨z, c⟩ hsome
    have hacc : keyFreeAccept prims pk sk.t0 z.1 c = true := by
      by_contra h
      simp [keyFreeAttempt, h] at hsome
    have hz : zCheck z.1 = true := by
      simp only [keyFreeAccept, Bool.and_eq_true] at hacc
      exact hacc.1.1.1
    have hbox : InMaskBox p.gamma1 (z.1 - cs c) := inMaskBox_sub_of_zCheck hz (hcs c)
    have hsub : maskSub (cs c) z = ⟨z.1 - cs c, hbox⟩ := dite_eq_left hbox
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [hsub]
      exact idealAttemptW1_eq_keyFreeAttempt h_laws hv henc hkeygen hs2 _ z c
        (rqVec_sub_add_cancel _ _).symm
    · dsimp only
      rw [hsub]
      have hadd : InMaskBox p.gamma1 (z.1 - cs c + cs c) := by
        rw [rqVec_sub_add_cancel]; exact z.2
      rw [maskAdd, dite_eq_left hadd]
      exact Prod.ext (Subtype.ext (rqVec_sub_add_cancel _ _)) rfl

/-- **The ideal and the key-free attempt have the same law** of `Option (w₁, σ)`: `y` uniform on
the mask box with `c̃` uniform, the four checks of FIPS 204 Algorithm 7, the commitment
`HighBits(Â·y)` and the signature `(c̃, y + c·s₁, h)`, against `z` uniform on the mask box with `c̃`
uniform, the checks, commitment and hint computed from the published `(ρ, t₁)` and `t₀`, and the
signature `(c̃, z, h)`. For the key of `seed` with `‖s₁‖∞, ‖s₂‖∞ ≤ η`, given the signing and
verification laws and an encoding `enc` coherent with `bucketsOf`. -/
theorem idealAttemptW1Law_eq_keyFreeAttemptLaw (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims) {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs1 : polyVecBounded sk.s1 p.eta)
    (hs2 : polyVecBounded sk.s2 p.eta) :
    idealAttemptW1Law prims sk (prims.expandA pk.rho) = keyFreeAttemptLaw prims pk sk.t0 := by
  obtain ⟨σ, hσ⟩ := exists_equiv_keyFreeAttempt h_laws hv henc hkeygen hs1 hs2
  rw [idealAttemptW1Law, keyFreeAttemptLaw,
    show idealAttemptW1 prims sk (prims.expandA pk.rho) = keyFreeAttempt prims pk sk.t0 ∘ σ from
      funext fun a => (hσ a).symm, map_uniformOfFintype_comp_equiv]

end Law

/-! ### One call of `T` attempts with a keep coin -/

section Call

open Classical in
/-- **One call with a keep coin**: the first accepted output `s` among the attempts `att`, kept
when the coin `u ∈ Fin D` is below `D · κ s`; `none` when no attempt accepts or the coin
rejects. -/
noncomputable def keptCall {S : Type*} {T D : ℕ} (κ : S → ℝ≥0∞) (att : Fin T → Option S)
    (u : Fin D) : Option S :=
  match (List.finRange T).findSome? att with
  | none => none
  | some s => if ((u : ℕ) : ℝ≥0∞) < D * κ s then some s else none

/-- **A permutation of the attempt coins carries one call to the other**: if `g ∘ σ = f` for a
permutation `σ`, the call over uniform coins of `T` attempts and a uniform keep coin has the same
law with the attempts `f` and with the attempts `g`. -/
theorem map_uniformOfFintype_keptCall_eq {α S : Type*} [Fintype α] [Nonempty α] {T D : ℕ}
    [NeZero D] (κ : S → ℝ≥0∞) {f g : α → Option S} (σ : α ≃ α) (hσ : ∀ a, g (σ a) = f a) :
    (uniformOfFintype ((Fin T → α) × Fin D)).map
        (fun x => keptCall κ (fun t => f (x.1 t)) x.2) =
      (uniformOfFintype ((Fin T → α) × Fin D)).map
        (fun x => keptCall κ (fun t => g (x.1 t)) x.2) := by
  let τ : (Fin T → α) × Fin D ≃ (Fin T → α) × Fin D :=
    Equiv.prodCongr (Equiv.arrowCongr (Equiv.refl _) σ) (Equiv.refl _)
  have h : (fun x : (Fin T → α) × Fin D => keptCall κ (fun t => f (x.1 t)) x.2) =
      (fun x => keptCall κ (fun t => g (x.1 t)) x.2) ∘ τ := by
    funext x
    simp [τ, hσ]
  rw [h, map_uniformOfFintype_comp_equiv]

variable {p : Params} [NeZero (bucketCount p)] (prims : Primitives p) [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)]

/-- The keep weight `wt (w₁, c̃)` of an output `(w₁, σ)`, read at the signature's `c̃`. -/
def outWeight (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞)
    (s : BucketVec p × FIPSSignature p prims) : ℝ≥0∞ :=
  wt (s.1, s.2.cTilde)

/-- **One ideal call**: `T` ideal attempts at the pairs `x t = (y_t, c̃_t)`, the first accepted one
kept when the coin `u` is below `D · wt (w₁, c̃)`. -/
noncomputable def idealCall {T D : ℕ} (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞) (x : Fin T → MaskBox p × CommitHashBytes p)
    (u : Fin D) : Option (BucketVec p × FIPSSignature p prims) :=
  keptCall (outWeight prims wt) (fun t => idealAttemptW1 prims sk aHat (x t)) u

/-- **The law of one ideal call**: `T` independent pairs of a mask uniform on the mask box and a
uniform commitment hash, and a uniform keep coin on `Fin D`. -/
noncomputable def idealCallLaw (T D : ℕ) [NeZero D] (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞) :
    PMF (Option (BucketVec p × FIPSSignature p prims)) :=
  (uniformOfFintype ((Fin T → MaskBox p × CommitHashBytes p) × Fin D)).map
    fun x => idealCall prims sk aHat wt x.1 x.2

/-- **One key-free call**: `T` key-free attempts at the pairs `x t = (z_t, c̃_t)`, the first
accepted one kept when the coin `u` is below `D · wt (w₁, c̃)`. -/
noncomputable def keyFreeCall {T D : ℕ} (pk : PublicKey p prims) (t0 : RqVec p.k)
    (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞) (x : Fin T → MaskBox p × CommitHashBytes p)
    (u : Fin D) : Option (BucketVec p × FIPSSignature p prims) :=
  keptCall (outWeight prims wt) (fun t => keyFreeAttempt prims pk t0 (x t)) u

/-- **The law of one key-free call**: `T` independent pairs of a response uniform on the mask box
and a uniform commitment hash, and a uniform keep coin on `Fin D`. -/
noncomputable def keyFreeCallLaw (T D : ℕ) [NeZero D] (pk : PublicKey p prims) (t0 : RqVec p.k)
    (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞) :
    PMF (Option (BucketVec p × FIPSSignature p prims)) :=
  (uniformOfFintype ((Fin T → MaskBox p × CommitHashBytes p) × Fin D)).map
    fun x => keyFreeCall prims pk t0 wt x.1 x.2

variable {prims}

/-- **The ideal and the key-free call have the same law**, for every keep weight `wt` of
`(w₁, c̃)`, under the hypotheses of `idealAttemptW1Law_eq_keyFreeAttemptLaw`. -/
theorem idealCallLaw_eq_keyFreeCallLaw (T D : ℕ) [NeZero D] (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims) {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs1 : polyVecBounded sk.s1 p.eta)
    (hs2 : polyVecBounded sk.s2 p.eta) (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞) :
    idealCallLaw prims T D sk (prims.expandA pk.rho) wt = keyFreeCallLaw prims T D pk sk.t0 wt := by
  obtain ⟨σ, hσ⟩ := exists_equiv_keyFreeAttempt h_laws hv henc hkeygen hs1 hs2
  exact map_uniformOfFintype_keptCall_eq (outWeight prims wt) σ hσ

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The signer's flattening coin is a function of its published `t₀`**: `min(1, β_min / aw)`
with `aw` the acceptance weight `t0Weight` of `t₀` (`signerWeight_eq_t0Weight`). -/
theorem flattenCoin_eq_flattenKeep_t0Weight (sk : SecretKey p) (βmin : ℚ≥0) :
    (fun a => (flattenCoin prims sk βmin a : ℝ≥0∞)) =
      PMF.flattenKeep (fun a => (t0Weight prims sk.t0 a : ℝ≥0∞)) βmin :=
  funext (coe_flattenCoin prims sk βmin)

/-- **The ring call at the flattening weight**: the ideal call kept with weight
`min(1, β_min / aw_i) · og(w₁)` (the signer's flattening coin `flattenCoin` and a weight `og` of
the commitment, such as the other members' weights) has the law of the key-free call kept with
the same weight read from the published `t₀` (`t0Weight`). -/
theorem idealCallLaw_flattenCoin_eq (T D : ℕ) [NeZero D] (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims) {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs1 : polyVecBounded sk.s1 p.eta)
    (hs2 : polyVecBounded sk.s2 p.eta) (βmin : ℚ≥0) (og : BucketVec p → ℝ≥0∞) :
    idealCallLaw prims T D sk (prims.expandA pk.rho)
        (fun vc => flattenCoin prims sk βmin vc * og vc.1) =
      keyFreeCallLaw prims T D pk sk.t0
        (fun vc => PMF.flattenKeep (fun a => (t0Weight prims sk.t0 a : ℝ≥0∞)) βmin vc * og vc.1) :=
          by
  simp only [← congrFun (flattenCoin_eq_flattenKeep_t0Weight (prims := prims) sk βmin)]
  exact idealCallLaw_eq_keyFreeCallLaw T D h_laws hv henc hkeygen hs1 hs2 _

end Call

/-! ### The hypotheses at the concrete primitives -/

section Concrete

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec GordieHowe.Ring.MLDSAW1

attribute [local instance] concreteNTTRingOps

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

/-- **The key-free attempt at the concrete primitives**: for every seed at every approved parameter
set, the ideal attempt of the key of `seed` at the vendored FIPS 204 primitives with the FIPS 204
`ExpandS` (`concretePrimitivesKeyGen`) and the concrete NTT has the law of the key-free attempt of
its published key (`idealAttemptW1Law_eq_keyFreeAttemptLaw` with `signingLaws_concreteKeyGen`,
`verifyLaws_concreteKeyGen`, `concreteEnc_highBitsVec_keyGen`, `keyGenFromSeed_s1_bounded` and
`keyGenFromSeed_s2_bounded`). -/
theorem idealAttemptW1Law_eq_keyFreeAttemptLaw_concrete (hp : p.isApproved) (seed : Bytes 32) :
    idealAttemptW1Law (concretePrimitivesKeyGen p)
        (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2
        ((concretePrimitivesKeyGen p).expandA
          (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).1.rho) =
      keyFreeAttemptLaw (concretePrimitivesKeyGen p)
        (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).1
        (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2.t0 :=
  idealAttemptW1Law_eq_keyFreeAttemptLaw (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp) rfl
    (keyGenFromSeed_s1_bounded hp seed) (keyGenFromSeed_s2_bounded hp seed)

/-- **The key-free call at the concrete primitives**: `idealCallLaw_eq_keyFreeCallLaw` for every
seed at every approved parameter set and every keep weight, with the hypotheses discharged as in
`idealAttemptW1Law_eq_keyFreeAttemptLaw_concrete`. -/
theorem idealCallLaw_eq_keyFreeCallLaw_concrete (hp : p.isApproved) (seed : Bytes 32)
    (T D : ℕ) [NeZero D] (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞) :
    idealCallLaw (concretePrimitivesKeyGen p) T D
        (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2
        ((concretePrimitivesKeyGen p).expandA
          (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).1.rho) wt =
      keyFreeCallLaw (concretePrimitivesKeyGen p) T D
        (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).1
        (keyGenFromSeed p (concretePrimitivesKeyGen p) seed).2.t0 wt :=
  idealCallLaw_eq_keyFreeCallLaw T D (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp) rfl
    (keyGenFromSeed_s1_bounded hp seed) (keyGenFromSeed_s2_bounded hp seed) wt

end Concrete

end GordieHowe.MLDSA
