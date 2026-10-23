-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Kernel
public import GordieHowe.Model.QROM.Compressed

@[expose] public section

/-!
# The purified random oracle and its Fourier basis

Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability"
(CRYPTO 2019, ePrint 2018/276; cited as Zha19), sections 1.1 and 3. This file defines, for a
`t`-query algorithm `A : QueryAlg (Bits m) (BitStr I J) t O`, the run of `A` against the
purified random oracle and the same run in the Fourier basis of the oracle register.

## Paper text and its transcription

Zha19 section 3, "Standard Oracle", p. 11:

    The oracle takes as input a state consisting of three sets of registers: m-qubit x registers
    representing inputs to the function, n-qubit y registers for writing the response, and
    n2^m-qubit H registers containing the truth table of the actual function. […] On basis
    states |x, y⟩ ⊗ |H⟩, the oracle performs the map |x, y⟩ ⊗ |H⟩ ↦ |x, y ⊕ H(x)⟩ ⊗ |H⟩.
    For initialization, the oracle H will be initialized to the uniform superposition over all
    H […]. We will call this oracle StO.

    Lemma 2. StO and StO′ are perfectly indistinguishable. […] This can be seen by tracing out
    the oracle registers.

The oracle register has basis `Bits m → BitStr I J`; `stO` applies `queryPerm h` to the
adversary's registers on the branch `h` (`controlled`), and the run `purStage A` starts from
`A.init ⊗ (1/√|Y^X|) ∑_h |h⟩` (`purInit`) and applies `A`'s unitaries as the identity on the oracle
register. Lemma 2 is `purStage_apply` (the branch `h` of the purified run is `A^h`, with amplitude
`1/√|Y^X|`) and `realLaw_eq_bornWeight` (the law of `A`'s output and `h` in the random-oracle model
is the law of measuring the purified state).

Zha19 section 3, Lemma 3, p. 12, and CMS19 section 3.6, p. 16, "O_h = (I^m ⊗ H^n) O′_h
(I^m ⊗ H^n)": `stO_eq` (the standard query is the phase query `phO`,
`|x, u⟩ ⊗ |h⟩ ↦ (−1)^{u·h(x)} |x, u⟩ ⊗ |h⟩`, between two Hadamard transforms `ansH` of the answer
register).

Zha19 section 1.1, pp. 6–7:

    Next, notice that by applying the Quantum Fourier transform to h, the h registers will now
    contain (P_{x1,u1} + ⋯ + P_{xq,uq}) mod 2. Working in the Fourier domain, we see that each
    query simply adds P_{x,u} (modulo 2) to the result. In the Fourier domain, the initial state
    is 0.

`fourier` is the Hadamard transform `H^n` on every entry of the oracle register: the tensor
product over `x` of `(1/√2^n) (−1)^{r·y}` (`hk`). `shiftPerm` adds the point function `P_{x,u}`
(`Pi.single x u`) to the Fourier-basis oracle register, and `fourier_shift_fourier` says that in
the Fourier basis the phase query is this addition. The run `fourStage A` starts from
`A.init ⊗ |0⟩` (`fourInit`) and answers each query by `ansH ∘ shift ∘ ansH`; `fourier_fourStage`
says it is the purified run in the Fourier basis, and `supported_fourStage` that after `k` queries
the Fourier-basis oracle register is nonzero on at most `k` inputs ("after q queries, D is
non-zero on at most q inputs", p. 7).
-/

open Finset GordieHowe.Quantum
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}

/-! ### Bit strings -/

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem BitStr.add_self (u : BitStr I J) : u + u = 0 :=
  funext fun _ => funext fun _ => CharTwo.add_self_eq_zero _

/-- **The Hadamard matrix** `H^n` on `{0,1}^n`: `hk y r = (1/√2^n) (−1)^{r·y}`. -/
noncomputable def hk (y r : BitStr I J) : ℂ := invSqrtCard I J * signOf (r.dot y)

theorem hk_comm (y r : BitStr I J) : hk y r = hk r y := by
  rw [hk, hk, BitStr.dot_comm]

theorem star_hk (y r : BitStr I J) : star (hk y r) = hk y r := by
  rw [hk, star_mul', star_invSqrtCard, star_signOf]

/-- `H^n · H^n = 1`. -/
theorem sum_hk_mul (y y' : BitStr I J) : ∑ r, hk y r * hk r y' = if y = y' then 1 else 0 := by
  have h := hadamardMatrix_inv y y'
  refine Eq.trans (sum_congr rfl fun r _ => ?_) h
  rw [hk, hk, BitStr.dot_comm r y, BitStr.dot_comm y' r]

/-- The columns of `H^n` are orthonormal. -/
theorem hk_orthonormal (r r' : BitStr I J) :
    ∑ y, star (hk y r) * hk y r' = if r = r' then 1 else 0 := by
  simp only [star_hk, hk_comm _ r]
  exact sum_hk_mul r r'

theorem hk_zero (y : BitStr I J) : hk y 0 = invSqrtCard I J := by
  simp [hk, BitStr.dot]

theorem hk_add (y r u : BitStr I J) : hk y (r + u) = hk y r * signOf (u.dot y) := by
  rw [hk, hk, BitStr.dot_add_left, signOf_add, mul_assoc]

/-! ### Basis states of the query registers -/

section Query

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The basis state `r` of the adversary's registers with answer register `u`. -/
def withAns (r : QueryReg W 1 (Bits m) (BitStr I J)) (u : BitStr I J) :
    QueryReg W 1 (Bits m) (BitStr I J) :=
  (r.1, fun _ => (qIn r, u))

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
@[simp] theorem qIn_withAns (r : QueryReg W 1 (Bits m) (BitStr I J)) (u : BitStr I J) :
    qIn (withAns r u) = qIn r := rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
@[simp] theorem qAns_withAns (r : QueryReg W 1 (Bits m) (BitStr I J)) (u : BitStr I J) :
    qAns (withAns r u) = u := rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
@[simp] theorem fst_withAns (r : QueryReg W 1 (Bits m) (BitStr I J)) (u : BitStr I J) :
    (withAns r u).1 = r.1 := rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
theorem withAns_self (r : QueryReg W 1 (Bits m) (BitStr I J)) : withAns r (qAns r) = r := by
  obtain ⟨w, q⟩ := r
  simp only [withAns, Prod.mk.injEq, true_and]
  exact funext fun i => by rw [Subsingleton.elim i 0]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
theorem withAns_withAns (r : QueryReg W 1 (Bits m) (BitStr I J)) (u u' : BitStr I J) :
    withAns (withAns r u) u' = withAns r u' := rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
theorem withAns_injective (r : QueryReg W 1 (Bits m) (BitStr I J)) :
    Function.Injective (withAns r) := fun u u' h => by
  simpa using congrArg qAns h

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
/-- A basis state agrees with `r` outside the answer register exactly when it is `r` with
another answer. -/
theorem eq_withAns_iff {r r' : QueryReg W 1 (Bits m) (BitStr I J)} :
    (r'.1 = r.1 ∧ qIn r' = qIn r) ↔ r' = withAns r (qAns r') := by
  constructor
  · rintro ⟨h1, h2⟩
    conv_lhs => rw [← withAns_self r']
    simp only [withAns, h1, h2]
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
theorem queryPerm_symm_apply (h : Bits m → BitStr I J) (r : QueryReg W 1 (Bits m) (BitStr I J)) :
    (queryPerm h).symm r = withAns r (qAns r + h (qIn r)) := by
  rw [Equiv.symm_apply_eq]
  conv_lhs => rw [← withAns_self r]
  simp only [queryPerm_apply, withAns, add_assoc, BitStr.add_self, add_zero]

end Query

/-! ### The Hadamard transform of the answer register -/

section AnsH

variable (W : Type) [Fintype W] [DecidableEq W] (L : Type) [Fintype L] [DecidableEq L]

/-- **`I ⊗ H^n` on the answer register**, with any register `L` beside the adversary's:
`|x, y, z, l⟩ ↦ (1/√2^n) ∑_u (−1)^{u·y} |x, u, z, l⟩`. On `L = Slots I J m t` it is
`hadamard` (`hadamard_eq_ansH`). -/
noncomputable def ansH :
    QState (QueryReg W 1 (Bits m) (BitStr I J) × L) →L[ℂ]
      QState (QueryReg W 1 (Bits m) (BitStr I J) × L) :=
  kernelOp fun b' b =>
    if b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1 ∧ b'.2 = b.2 then
      invSqrtCard I J * signOf ((qAns b'.1).dot (qAns b.1))
    else 0

theorem hadamard_eq_ansH (t : ℕ) :
    hadamard (I := I) (J := J) (m := m) W t = ansH W (Slots I J m t) :=
  rfl

/-- The matrix of `ansH` leaves the second register unchanged. -/
theorem ansH_eq_kernelMap :
    ansH (I := I) (J := J) (m := m) W L = kernelMap (idRight fun r' r =>
      if r'.1 = r.1 ∧ qIn r' = qIn r then hk (qAns r) (qAns r') else 0) := by
  rw [ansH, kernelOp_eq_kernelMap]
  congr 1
  funext b' b
  simp only [idRight, hk]
  by_cases h2 : b'.2 = b.2
  · by_cases h1 : b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1
    · simp [h1, h2]
    · have : ¬(b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1 ∧ b'.2 = b.2) := fun h => h1 ⟨h.1, h.2.1⟩
      rw [if_neg this, if_pos h2, if_neg h1]
  · simp [h2]

variable {W L}

theorem ansH_apply (v : QState (QueryReg W 1 (Bits m) (BitStr I J) × L))
    (r : QueryReg W 1 (Bits m) (BitStr I J)) (l : L) :
    ansH W L v (r, l) = ∑ u, hk u (qAns r) * v (withAns r u, l) := by
  rw [ansH_eq_kernelMap, kernelMap_idRight_apply]
  refine (Fintype.sum_of_injective (withAns r) (withAns_injective r) _ _ (fun r' hr' => ?_)
    (fun u => ?_)).symm
  · rw [if_neg, zero_mul]
    intro h
    exact hr' ⟨qAns r', ((eq_withAns_iff (r := r) (r' := r')).1
      ⟨h.1.symm, h.2.symm⟩).symm⟩
  · simp

end AnsH

/-! ### The Hadamard transform of the oracle register -/

section Fourier

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The matrix of `H^n` on every entry of a truth table `X → {0,1}^n`:
`fourierK h F = ∏_x (1/√2^n) (−1)^{F(x)·h(x)}`. -/
noncomputable def fourierK : (X → BitStr I J) → (X → BitStr I J) → ℂ :=
  piKernel fun _ => hk

omit [DecidableEq X] in
theorem fourierK_comm (h F : X → BitStr I J) : fourierK h F = fourierK F h := by
  simp only [fourierK, piKernel, hk_comm]

/-- `fourierK · fourierK = 1`. -/
theorem sum_fourierK_mul (h F : X → BitStr I J) :
    ∑ G, fourierK h G * fourierK G F = if h = F then 1 else 0 := by
  rw [fourierK, sum_piKernel_mul]
  simp only [sum_hk_mul]
  exact piKernel_ite_eq h F

omit [DecidableEq X] in
theorem fourierK_zero (h : X → BitStr I J) :
    fourierK h 0 = invSqrtCard I J ^ Fintype.card X := by
  simp [fourierK, piKernel, hk_zero]

/-- Adding the point function `P_{x,u}` to the Fourier index multiplies by `(−1)^{u·h(x)}`. -/
theorem fourierK_add_single (h F : X → BitStr I J) (x : X) (u : BitStr I J) :
    fourierK h (F + Pi.single x u) = fourierK h F * signOf (u.dot (h x)) := by
  simp only [fourierK, piKernel]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x),
    ← Finset.mul_prod_erase _ (fun x' => hk (h x') (F x')) (Finset.mem_univ x)]
  have hrest : ∏ x' ∈ univ.erase x, hk (h x') ((F + Pi.single x u : X → BitStr I J) x') =
      ∏ x' ∈ univ.erase x, hk (h x') (F x') :=
    prod_congr rfl fun x' hx' => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hx'), add_zero]
  rw [hrest, Pi.add_apply, Pi.single_eq_same, hk_add]
  ring

variable (Q : Type) [Fintype Q] [DecidableEq Q]

/-- **`H^n` on every entry of the oracle register** `X → {0,1}^n`, beside a register `Q`
(Zha19 section 1.1: "applying the Quantum Fourier transform to h"). -/
noncomputable def fourier : QState (Q × (X → BitStr I J)) →L[ℂ] QState (Q × (X → BitStr I J)) :=
  kernelMap (idLeft fun _ => fourierK)

variable {Q}

theorem fourier_apply (v : QState (Q × (X → BitStr I J))) (q : Q) (h : X → BitStr I J) :
    fourier Q v (q, h) = ∑ F, fourierK h F * v (q, F) :=
  kernelMap_idLeft_apply _ v q h

/-- `fourier` is an involution. -/
theorem fourier_fourier (v : QState (Q × (X → BitStr I J))) : fourier Q (fourier Q v) = v := by
  ext ⟨q, h⟩
  simp only [fourier_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, sum_fourierK_mul]
  simp

/-- `fourier` is unitary. -/
theorem norm_fourier (v : QState (Q × (X → BitStr I J))) : ‖fourier Q v‖ = ‖v‖ := by
  refine norm_kernelMap (idLeft_orthonormal (S := fun _ => Set.univ) fun _ F _ F' _ => ?_)
    fun b hb => absurd (Set.mem_univ _) hb
  exact piKernel_orthonormal (fun _ => hk_orthonormal) F F'

/-- `fourier` acts on the oracle register: it commutes with any matrix on the other register. -/
theorem fourier_kernelMap_idRight (Qm : Q → Q → ℂ) (v : QState (Q × (X → BitStr I J))) :
    fourier Q (kernelMap (idRight Qm) v) = kernelMap (idRight Qm) (fourier Q v) :=
  (idRight_comm Qm fourierK v).symm

/-- `fourier` commutes with a unitary on the other register. -/
theorem fourier_controlled (U : QState Q ≃ₗᵢ[ℂ] QState Q) (v : QState (Q × (X → BitStr I J))) :
    fourier Q (controlled (fun _ => U) v) = controlled (fun _ => U) (fourier Q v) :=
  (controlled_kernelMap_idLeft U fourierK v).symm

end Fourier

/-! ### The standard, phase and Fourier-basis queries -/

section Queries

/-- The registers of the purified run: the adversary's registers and the oracle register
`Bits m → {0,1}^n`. -/
abbrev PurReg (W I J : Type) (m : ℕ) := QueryReg W 1 (Bits m) (BitStr I J) × (Bits m → BitStr I J)

variable (W : Type) [Fintype W] [DecidableEq W]

/-- **`StO`** (Zha19 section 3, p. 11): `|x, y⟩ ⊗ |h⟩ ↦ |x, y ⊕ h(x)⟩ ⊗ |h⟩`, the query
`queryPerm h` on the branch `h` of the oracle register. -/
noncomputable def stO : QState (PurReg W I J m) ≃ₗᵢ[ℂ] QState (PurReg W I J m) :=
  controlled fun h => permOp (queryPerm h)

/-- **The phase query** (Zha19 section 3, p. 12, "PhO"):
`|x, u⟩ ⊗ |h⟩ ↦ (−1)^{u·h(x)} |x, u⟩ ⊗ |h⟩`. -/
noncomputable def phO : QState (PurReg W I J m) →L[ℂ] QState (PurReg W I J m) :=
  kernelOp fun b' b => if b' = b then signOf ((qAns b.1).dot (b.2 (qIn b.1))) else 0

/-- The Fourier-basis oracle register plus the point function `P_{x,u}` of the query. -/
def shift (b : PurReg W I J m) : PurReg W I J m :=
  (b.1, b.2 + Pi.single (qIn b.1) (qAns b.1))

omit [Fintype W] [DecidableEq W] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem shift_shift (b : PurReg W I J m) : shift W (shift W b) = b := by
  obtain ⟨r, F⟩ := b
  simp only [shift, add_assoc, ← Pi.single_add, BitStr.add_self, Pi.single_zero, add_zero]

/-- **The query in the Fourier basis** (Zha19 section 1.1, p. 7: "each query simply adds P_{x,u}
(modulo 2)"): the basis permutation `|x, u⟩ ⊗ |F⟩ ↦ |x, u⟩ ⊗ |F + P_{x,u}⟩`. -/
def shiftPerm : Equiv.Perm (PurReg W I J m) :=
  Function.Involutive.toPerm (shift W) (shift_shift W)

variable {W}

omit [DecidableEq W] in
theorem stO_apply (v : QState (PurReg W I J m)) (r : QueryReg W 1 (Bits m) (BitStr I J))
    (h : Bits m → BitStr I J) : stO W v (r, h) = v (withAns r (qAns r + h (qIn r)), h) := by
  rw [stO, controlled_apply, permOp_apply, queryPerm_symm_apply]

theorem phO_apply (v : QState (PurReg W I J m)) (b : PurReg W I J m) :
    phO W v b = signOf ((qAns b.1).dot (b.2 (qIn b.1))) * v b := by
  rw [phO, kernelOp_apply, Finset.sum_eq_single b (fun c _ h => by simp [Ne.symm h]) (by simp)]
  simp

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype W] [DecidableEq W] in
theorem shiftPerm_symm_apply (b : PurReg W I J m) : (shiftPerm W).symm b = shift W b :=
  rfl

/-- **Zha19 Lemma 3** (p. 12; CMS19 section 3.6, p. 16, `O_h = (I^m ⊗ H^n) O′_h (I^m ⊗ H^n)`): the
standard query is the phase query between two Hadamard transforms of the answer register. -/
theorem stO_eq (v : QState (PurReg W I J m)) : stO W v = ansH W _ (phO W (ansH W _ v)) := by
  ext ⟨r, h⟩
  rw [stO_apply, ansH_apply]
  simp only [phO_apply, ansH_apply, qAns_withAns, qIn_withAns, withAns_withAns, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hk' : ∀ u u' : BitStr I J, hk u (qAns r) * (signOf (u.dot (h (qIn r))) *
      (hk u' u * v (withAns r u', h))) = hk u' u * hk u (qAns r + h (qIn r)) *
        v (withAns r u', h) := fun u u' => by
    rw [hk_add, BitStr.dot_comm u]
    ring
  simp_rw [hk', ← Finset.sum_mul, sum_hk_mul]
  simp

/-- **The phase query is the addition of `P_{x,u}` in the Fourier basis** (Zha19 section 1.1,
pp. 6–7). -/
theorem fourier_shift_fourier (v : QState (PurReg W I J m)) :
    fourier _ (permOp (shiftPerm W) (fourier _ v)) = phO W v := by
  ext ⟨r, h⟩
  simp only [fourier_apply, permOp_apply, shiftPerm_symm_apply, shift, phO_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have hK : ∀ G F : Bits m → BitStr I J, fourierK h G *
      (fourierK (G + Pi.single (qIn r) (qAns r)) F * v (r, F)) =
        fourierK h G * fourierK G F * (signOf ((qAns r).dot (F (qIn r))) * v (r, F)) :=
    fun G F => by
      rw [fourierK_comm _ F, fourierK_add_single, fourierK_comm F]
      ring
  simp_rw [hK, ← Finset.sum_mul, sum_fourierK_mul]
  simp

/-- **A query of the Fourier-basis run**: `ansH ∘ shift ∘ ansH`. -/
noncomputable def fourQuery : QState (PurReg W I J m) →L[ℂ] QState (PurReg W I J m) :=
  ansH W _ ∘L ((permOp (shiftPerm (I := I) (J := J) (m := m) W)).toContinuousLinearEquiv :
      QState (PurReg W I J m) →L[ℂ] QState (PurReg W I J m)) ∘L
    ansH W _

theorem fourQuery_apply (v : QState (PurReg W I J m)) :
    fourQuery v = ansH W _ (permOp (shiftPerm W) (ansH W _ v)) :=
  rfl

theorem fourier_ansH (v : QState (PurReg W I J m)) :
    fourier _ (ansH W _ v) = ansH W _ (fourier _ v) := by
  rw [ansH_eq_kernelMap]
  exact fourier_kernelMap_idRight _ v

/-- **The Fourier-basis query is the standard query in the Fourier basis.** -/
theorem fourier_fourQuery (v : QState (PurReg W I J m)) :
    fourier _ (fourQuery v) = stO W (fourier _ v) := by
  rw [fourQuery_apply, fourier_ansH, ← fourier_fourier (ansH W _ v), fourier_shift_fourier,
    stO_eq, fourier_ansH]

end Queries

/-! ### The purified run and the Fourier-basis run -/

section Runs

variable {O : Type} {t : ℕ} (A : QueryAlg (Bits m) (BitStr I J) t O)

/-- `A`'s unitary `step k`, extended by the identity on a register `L` beside the adversary's. -/
noncomputable def liftStep (L : Type) [Fintype L] (k : ℕ) :
    QState (QueryReg A.W 1 (Bits m) (BitStr I J) × L) ≃ₗᵢ[ℂ]
      QState (QueryReg A.W 1 (Bits m) (BitStr I J) × L) :=
  controlled fun _ => (A.toOracleAlg ∅).stepAt () k

/-- `1/√|Y^X|`, the amplitude of each truth table in the uniform superposition. -/
noncomputable abbrev unifAmp (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (m : ℕ) : ℂ :=
  invSqrtCard I J ^ Fintype.card (Bits m)

/-- The initial state of the purified run: `A.init ⊗ (1/√|Y^X|) ∑_h |h⟩`. -/
noncomputable def purInit : QState (PurReg A.W I J m) :=
  WithLp.toLp 2 fun b => A.init b.1 * unifAmp I J m

/-- **The run of `A` against the purified random oracle `StO`** (Zha19 section 3, p. 11): the
state after `step k`. -/
noncomputable def purStage (k : ℕ) : QState (PurReg A.W I J m) :=
  Nat.rec (liftStep A _ 0 (purInit A)) (fun k v => liftStep A _ (k + 1) (stO A.W v)) k

/-- The branch `h` of the purified run is the run of `A` with oracle `h`, with amplitude
`1/√|Y^X|` (Zha19 Lemma 2). -/
theorem purStage_apply (k : ℕ) (r : QueryReg A.W 1 (Bits m) (BitStr I J))
    (h : Bits m → BitStr I J) :
    purStage A k (r, h) = unifAmp I J m * (A.toOracleAlg ∅).stage (queryPerm h) () k r := by
  have hslice : ∀ k, (WithLp.toLp 2 fun r' => purStage A k (r', h) : QState _) =
      unifAmp I J m • (A.toOracleAlg ∅).stage (queryPerm h) () k := by
    intro k
    induction k with
    | zero =>
      ext r'
      show liftStep A _ 0 (purInit A) (r', h) = _
      rw [liftStep, controlled_apply]
      have : (WithLp.toLp 2 fun r'' => purInit A (r'', h) : QState _) = unifAmp I J m • A.init := by
        ext r''
        simp only [purInit, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [this, map_smul]
      rfl
    | succ k ih =>
      ext r'
      show liftStep A _ (k + 1) (stO A.W (purStage A k)) (r', h) = _
      rw [liftStep, controlled_apply]
      have : (WithLp.toLp 2 fun r'' => stO A.W (purStage A k) (r'', h) : QState _) =
          permOp (queryPerm h) (WithLp.toLp 2 fun r'' => purStage A k (r'', h)) := by
        ext r''
        rw [stO, controlled_apply]
      rw [this, ih, map_smul, map_smul]
      rfl
  have := congrArg (fun v : QState _ => v r) (hslice k)
  simpa using this

/-- The initial state of the Fourier-basis run: `A.init ⊗ |0⟩`. -/
def fourInit : QState (PurReg A.W I J m) :=
  WithLp.toLp 2 fun b => A.init b.1 * if b.2 = 0 then 1 else 0

/-- **The run of `A` in the Fourier basis of the oracle register** (Zha19 section 1.1, pp. 6–7):
it starts from `A.init ⊗ |0⟩` and answers each query by `ansH ∘ shift ∘ ansH`. -/
noncomputable def fourStage (k : ℕ) : QState (PurReg A.W I J m) :=
  Nat.rec (liftStep A _ 0 (fourInit A)) (fun k v => liftStep A _ (k + 1) (fourQuery v)) k

theorem fourStage_zero : fourStage A 0 = liftStep A _ 0 (fourInit A) :=
  rfl

theorem fourStage_succ (k : ℕ) :
    fourStage A (k + 1) = liftStep A _ (k + 1) (fourQuery (fourStage A k)) :=
  rfl

theorem fourier_fourInit : fourier _ (fourInit A) = purInit A := by
  ext ⟨r, h⟩
  rw [fourier_apply, Finset.sum_eq_single 0 (fun F _ hF => by simp [fourInit, hF]) (by simp),
    fourierK_zero]
  simp only [fourInit, purInit, if_true, mul_one]
  exact mul_comm _ _

/-- **The Fourier-basis run is the purified run in the Fourier basis.** -/
theorem fourier_fourStage (k : ℕ) : fourier _ (fourStage A k) = purStage A k := by
  induction k with
  | zero =>
    rw [fourStage_zero, liftStep, fourier_controlled, fourier_fourInit]
    rfl
  | succ k ih =>
    rw [fourStage_succ, liftStep, fourier_controlled, fourier_fourQuery, ih]
    rfl

/-- The number of inputs on which a Fourier-basis truth table is nonzero. -/
def fourierSize {X : Type} [Fintype X] (F : X → BitStr I J) : ℕ :=
  (univ.filter fun x => F x ≠ 0).card

omit [DecidableEq I] [DecidableEq J] in
theorem fourierSize_add_single_le {X : Type} [Fintype X] [DecidableEq X] (F : X → BitStr I J)
    (x : X) (u : BitStr I J) : fourierSize (F + Pi.single x u) ≤ fourierSize F + 1 := by
  refine (Finset.card_le_card fun x' hx' => ?_).trans (Finset.card_insert_le x _)
  rw [Finset.mem_insert, Finset.mem_filter]
  by_cases h : x' = x
  · exact Or.inl h
  · refine Or.inr ⟨Finset.mem_univ _, ?_⟩
    have := (Finset.mem_filter.1 hx').2
    rwa [Pi.add_apply, Pi.single_eq_of_ne h, add_zero] at this

omit [DecidableEq I] [DecidableEq J] in
@[simp]
theorem fourierSize_zero {X : Type} [Fintype X] : fourierSize (0 : X → BitStr I J) = 0 := by
  simp [fourierSize]

/-- `ansH` preserves support in a set of values of the second register. -/
theorem Supported.ansH {W L : Type} [Fintype W] [DecidableEq W] [Fintype L] [DecidableEq L]
    {Q : Set L} {v : QState (QueryReg W 1 (Bits m) (BitStr I J) × L)}
    (hv : Supported {b | b.2 ∈ Q} v) : Supported {b | b.2 ∈ Q} (GordieHowe.QROM.ansH W L v) :=
  hv.kernelOp fun b' b hb hb' => by
    rw [if_neg]
    rintro ⟨-, -, h⟩
    exact hb' (show b'.2 ∈ Q from h ▸ hb)

/-- **After `k` queries the Fourier-basis oracle register is nonzero on at most `k` inputs**
(Zha19 section 1.1, p. 7: "after q queries, D is non-zero on at most q inputs"). -/
theorem supported_fourStage (k : ℕ) :
    Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F ≤ k}} (fourStage A k) := by
  induction k with
  | zero =>
    refine Supported.controlled _ fun b hb => ?_
    simp only [fourInit, mul_ite, mul_one, mul_zero]
    rw [if_neg]
    rintro h
    exact hb (show fourierSize b.2 ≤ 0 by rw [h, fourierSize_zero])
  | succ k ih =>
    refine Supported.controlled _ ?_
    rw [fourQuery_apply]
    refine Supported.ansH (Supported.permOp (Supported.ansH ih) fun b hb => ?_)
    exact (fourierSize_add_single_le _ _ _).trans (Nat.succ_le_succ hb)

/-- `|1/√|Y^X||² = 1/|Y^X|`. -/
theorem enorm_unifAmp_sq :
    ‖unifAmp I J m‖ₑ ^ 2 = (Fintype.card (Bits m → BitStr I J) : ℝ≥0∞)⁻¹ := by
  have hN : (0 : ℝ) < Fintype.card (BitStr I J) := by exact_mod_cast Fintype.card_pos
  have h1 : ‖invSqrtCard I J‖ₑ ^ 2 = (Fintype.card (BitStr I J) : ℝ≥0∞)⁻¹ := by
    rw [invSqrtCard, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hN)), ← ENNReal.ofReal_pow (inv_pos.2
        (Real.sqrt_pos.2 hN)).le, inv_pow, Real.sq_sqrt hN.le,
      ENNReal.ofReal_inv_of_pos hN, ENNReal.ofReal_natCast]
  rw [unifAmp, enorm_pow, ← pow_mul, mul_comm, pow_mul, h1,
    show Fintype.card (Bits m → BitStr I J) = Fintype.card (BitStr I J) ^ Fintype.card (Bits m)
      from Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- **The law of the output and the oracle in the random-oracle model is the law of measuring
the purified state** (Zha19 Lemma 2: "This can be seen by tracing out the oracle registers"). -/
theorem realLaw_eq_bornWeight {B : Type} (e : BitStr I J ≃ B) (S : Set (Outcome O (Bits m) B)) :
    (A.realLaw e).toOuterMeasure S =
      bornWeight (purStage A t) {b | ⟨A.out b.1.1, e ∘ b.2⟩ ∈ S} := by
  rw [QueryAlg.realLaw, PMF.toOuterMeasure_bind_apply, tsum_fintype, bornWeight_apply_eq_sum,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine sum_congr rfl fun h _ => ?_
  rw [PMF.uniformOfFintype_apply, PMF.toOuterMeasure_map_apply, QueryAlg.outLaw,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype, Finset.mul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [← enorm_unifAmp_sq (I := I) (J := J) (m := m)]
  by_cases hr : (⟨A.out r.1, e ∘ h⟩ : Outcome O (Bits m) B) ∈ S
  · rw [Set.indicator_of_mem (show r ∈ _ from hr), Set.indicator_of_mem (show (r, h) ∈ _ from hr),
      purStage_apply, enorm_mul, mul_pow]
    rfl
  · rw [Set.indicator_of_notMem (show r ∉ _ from hr), mul_zero, eq_comm]
    exact Set.indicator_of_notMem
      (s := {b : PurReg A.W I J m | (⟨A.out b.1.1, e ∘ b.2⟩ : Outcome O (Bits m) B) ∈ S}) hr _

end Runs

end GordieHowe.QROM
