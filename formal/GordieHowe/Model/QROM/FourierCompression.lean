-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Purified

@[expose] public section

/-!
# Compression of the Fourier-basis oracle register and Zhandry's Lemma 4

Zhandry, "How to Record Quantum Queries" (Zha19, ePrint 2018/276), sections 1.1 and 3, and
CMS19 Appendix A. This file maps the Fourier-basis run of `GordieHowe/Model/QROM/Purified.lean` onto the run
`|Sim*(A)⟩` of `GordieHowe/Model/QROM/Compressed.lean` with the compressed phase oracle `O = Dec ∘ O0 ∘ Dec`
of bound `t`: `simStage_eq_compress`, `|Sim*(A)⟩ = compress (fourStage A t)` (Zha19 Lemma 4,
p. 15, "CPhsO and PhO are perfectly indistinguishable", in the form used by CMS19 Lemma 3.3).

## Paper text and its transcription

Zha19 section 1.1, p. 7:

    Notice that after q queries, D is non-zero on at most q inputs (since it is the sum of q
    point functions). Therefore, we can store the database in an extremely compact form, namely
    the list of (x, y) pairs where y = D(x) and y ≠ 0. […] We will call this the compressed
    Fourier oracle. We can then take our compressed Fourier oracle, and convert it back into a
    primal-domain oracle. Namely, for each (x, y) pair, we perform the QFT on the y registers.
    The result is a superposition of databases of (x, w) pairs […]. We call this the compressed
    standard oracle.

Zha19 section 3, p. 12: "For any of the ℓ positions that have been specified, the y registers
are in a state that is orthogonal to the uniform superposition |τ⟩".

`fdb F` is the state of the `t`-slot database register for a Fourier-basis truth table `F` with
at most `t` nonzero entries: the inputs `x` with `F x ≠ 0` are recorded, and the answer register
of `x` holds the Fourier state `(1/√2^n) ∑_y (−1)^{F(x)·y} |y⟩` (orthogonal to `|τ⟩`); the inputs
with `F x = 0` are not recorded. It is a product state `dbVec k` whose amplitude at the database
`D` is `∏_x k x (D(x))`, with entry `fk (F x)`. `compress` maps `|r⟩ ⊗ |F⟩` to `|r⟩ ⊗ fdb F`.

CMS19 Appendix A, p. 47 (`Dec_x` and `O0`, quoted in `GordieHowe/Model/QROM/Compressed.lean`): on product
states whose entries away from `x` record fewer than `t` inputs, `Dec_x` replaces the entry at
`x` by `k x − δ w`, where `δ = k x (⊥) − (1/√2^n) ∑_b k x (b)` and `w` is `1` at `⊥` and
`−1/√2^n` elsewhere (`decXOp_dbVec`); so it exchanges the entry `fk r` (Fourier value `r`,
unrecorded when `r = 0`) with `gk r` (Fourier value `r`, recorded; `gk 0 = |τ⟩`). `O0` multiplies
the entry at `x` by `(−1)^{u·b}`, which maps `gk r` to `gk (r + u)`. So `O = Dec ∘ O0 ∘ Dec` maps
`fdb F` to `fdb (F + P_{x,u})` (`compressedOracle_compress`): the compressed oracle is the
Fourier-basis query, as long as fewer than `t` inputs are recorded. After `k < t` queries the
Fourier-basis run records at most `k` (`supported_fourStage`), so the fixed bound `t` of
CMS19's `O` is never reached by a `t`-query algorithm, and the compressed run is the Fourier-basis
run with its oracle register compressed.
-/

open Finset GordieHowe.Quantum
open scoped BigOperators ENNReal

namespace GordieHowe.QROM

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B : Type} (e : BitStr I J ≃ B) {t : ℕ}

/-! ### Product states of the database register -/

section Product


/-- The amplitude `∏_x k x (D(x))` of the product state with entries `k x` at the database `D`. -/
def dbAmp (k : Bits m → Option B → ℂ) (D : DB (Bits m) B) : ℂ :=
  ∏ x, k x (D.lookup x)

/-- The product of the entries away from `x`. -/
def dbAmpOff (k : Bits m → Option B → ℂ) (x : Bits m) (D : DB (Bits m) B) : ℂ :=
  ∏ x' ∈ univ.erase x, k x' (D.lookup x')

theorem dbAmp_eq_mul (k : Bits m → Option B → ℂ) (x : Bits m) (D : DB (Bits m) B) :
    dbAmp k D = k x (D.lookup x) * dbAmpOff k x D :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ x)).symm

theorem dbAmpOff_congr {k : Bits m → Option B → ℂ} {x : Bits m} {D D' : DB (Bits m) B}
    (h : ∀ x' ≠ x, D.lookup x' = D'.lookup x') : dbAmpOff k x D = dbAmpOff k x D' :=
  prod_congr rfl fun x' hx' => by rw [h x' (Finset.ne_of_mem_erase hx')]

theorem dbAmpOff_erase (k : Bits m → Option B → ℂ) (x : Bits m) (D : DB (Bits m) B) :
    dbAmpOff k x (D.erase x) = dbAmpOff k x D :=
  dbAmpOff_congr fun _ h => Finmap.lookup_erase_ne h

theorem dbAmpOff_extend (k : Bits m → Option B → ℂ) (x : Bits m) (D : DB (Bits m) B) (b : B) :
    dbAmpOff k x (D.extend x b) = dbAmpOff k x D :=
  dbAmpOff_congr fun _ h => DB.lookup_extend_of_ne h

theorem dbAmpOff_update (k : Bits m → Option B → ℂ) (x : Bits m) (k' : Option B → ℂ)
    (D : DB (Bits m) B) : dbAmpOff (Function.update k x k') x D = dbAmpOff k x D :=
  prod_congr rfl fun x' hx' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx')]

theorem dbAmp_update (k : Bits m → Option B → ℂ) (x : Bits m) (k' : Option B → ℂ)
    (D : DB (Bits m) B) : dbAmp (Function.update k x k') D = k' (D.lookup x) * dbAmpOff k x D := by
  rw [dbAmp_eq_mul _ x, Function.update_self, dbAmpOff_update]

variable (t) in
/-- **The product state of the `t`-slot database register** with entries `k x`: amplitude
`∏_x k x (D(x))` at each database state `|D_t⟩`, `0` on the other slot tuples. -/
noncomputable def dbVec (k : Bits m → Option B → ℂ) : QState (Slots I J m t) :=
  WithLp.toLp 2 fun s => if IsDBState e s then dbAmp k (slotsDB e s) else 0

theorem dbVec_dbSlots (k : Bits m → Option B → ℂ) {D : DB (Bits m) B} (hD : D.size ≤ t) :
    dbVec e t k (dbSlots e t D) = dbAmp k D := by
  simp [dbVec, isDBState_dbSlots e hD, slotsDB_dbSlots e hD]

theorem dbVec_of_not (k : Bits m → Option B → ℂ) {s : Slots I J m t} (hs : ¬ IsDBState e s) :
    dbVec e t k s = 0 := by
  simp [dbVec, hs]

variable (t) in
open Classical in
/-- **`Dec_x` on the `t`-slot register** (CMS19 App. A, p. 47): the reflection matrix of
`decMatrix_eq`. -/
noncomputable def decXOp (x : Bits m) : QState (Slots I J m t) →L[ℂ] QState (Slots I J m t) :=
  kernelMap (reflKernel (decBlock e t x) (decAmp e t x))

/-- `δ = k(⊥) − (1/√2^n) ∑_y k(y)` for an entry `k`: `√2` times its inner product with the block
vector `u` of `Dec_x`. -/
noncomputable def decDefect (k : Option B → ℂ) : ℂ :=
  k none - invSqrtCard I J * ∑ y : BitStr I J, k (some (e y))

/-- The entry of `√2 u` at a value of `D(x)`: `1` at `⊥`, `−1/√2^n` elsewhere. -/
noncomputable def decWeight : Option B → ℂ
  | none => 1
  | some _ => -invSqrtCard I J

theorem decAmp_dbSlots_eq {x : Bits m} {D : DB (Bits m) B} (hD : D.size ≤ t)
    (hsz : DB.size (D.erase x) < t) :
    (decAmp e t x (dbSlots e t D) : ℂ) = decWeight (I := I) (J := J) (D.lookup x) := by
  rw [decAmp_dbSlots e hD, if_pos hsz]
  by_cases hx : x ∈ D
  · obtain ⟨b, hb⟩ := DB.mem_iff_lookup.1 hx
    simp [hx, hb, decWeight, invSqrtCard_eq]
  · simp [hx, Finmap.lookup_eq_none.2 hx, decWeight]

open Classical in
/-- **`Dec_x` on a product state** (CMS19 App. A, p. 47): if every database on which the entries
away from `x` are nonzero has fewer than `t` entries away from `x`, `Dec_x` replaces the entry at
`x` by `k x − δ w`. -/
theorem decXOp_dbVec (k : Bits m → Option B → ℂ) (x : Bits m)
    (hk : ∀ D : DB (Bits m) B, dbAmpOff k x D ≠ 0 → DB.size (D.erase x) < t) :
    decXOp e t x (dbVec e t k) = dbVec e t (Function.update k x
      fun o => k x o - decDefect e (k x) * decWeight (I := I) (J := J) o) := by
  ext s
  rw [decXOp, kernelMap_apply]
  simp only [reflKernel, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hs : IsDBState e s
  · obtain ⟨hD, hsD⟩ := IsDBState.dbSlots_slotsDB e hs
    set D := slotsDB e s
    rw [← hsD, dbVec_dbSlots e _ hD, dbVec_dbSlots e _ hD, dbAmp_update, dbAmp_eq_mul k x]
    by_cases hsz : DB.size (D.erase x) < t
    · have hblk : decBlock e t x (dbSlots e t D) = some (D.erase x) := by
        rw [decBlock_dbSlots e hD, if_pos hsz]
      have hx0 : x ∉ D.erase x := Finmap.notMem_erase_self
      rw [hblk]
      have hsum : ∑ s', (if some (D.erase x) = decBlock e t x s' then
          ((decAmp e t x (dbSlots e t D) * decAmp e t x s' : ℝ) : ℂ) * dbVec e t k s' else 0) =
          (decAmp e t x (dbSlots e t D) : ℂ) * (dbAmpOff k x D * decDefect e (k x)) := by
        simp_rw [eq_comm (a := some (D.erase x))]
        rw [sum_block e hx0 hsz (fun s' => ((decAmp e t x (dbSlots e t D) * decAmp e t x s' : ℝ) : ℂ)
          * dbVec e t k s'), Fintype.sum_option]
        have h3 : dbVec e t k (blockSlot e t x (D.erase x) none) = k x none * dbAmpOff k x D := by
          show dbVec e t k (dbSlots e t (D.erase x)) = _
          rw [dbVec_dbSlots e _ (D := D.erase x) hsz.le, dbAmp_eq_mul k x,
            Finmap.lookup_erase, dbAmpOff_erase]
        have h4 : ∀ y : BitStr I J, dbVec e t k (blockSlot e t x (D.erase x) (some y)) =
            k x (some (e y)) * dbAmpOff k x D := fun y => by
          show dbVec e t k (dbSlots e t (DB.extend (D.erase x) x (e y))) = _
          rw [dbVec_dbSlots e _ (D := DB.extend (D.erase x) x (e y))
            (size_blockDB_le e hx0 hsz (some y)), dbAmp_eq_mul k x,
            DB.lookup_extend_self, dbAmpOff_extend, dbAmpOff_erase]
        rw [decAmp_blockSlot_none e hx0 hsz, h3]
        simp_rw [decAmp_blockSlot_some e hx0 hsz, h4]
        simp only [decDefect, invSqrtCard_eq]
        rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg,
          ← Finset.sum_neg_distrib]
        push_cast
        congr 1
        · ring
        · exact sum_congr rfl fun y _ => by ring
      rw [hsum, decAmp_dbSlots_eq e hD hsz]
      ring
    · have h0 : dbAmpOff k x D = 0 := by
        by_contra h
        exact hsz (hk D h)
      have hamp : decAmp e t x (dbSlots e t D) = 0 := by
        rw [decAmp_dbSlots e hD, if_neg hsz]
      simp [h0, hamp]
  · rw [dbVec_of_not e _ hs, dbVec_of_not e _ hs, decAmp_of_not e hs]
    simp

variable (t) in
/-- **`O0` on the `t`-slot register at the query `x, u`** (CMS19 App. A, p. 47):
`|D⟩ ↦ (−1)^{u·D(x)} |D⟩` with `u·⊥ = 0`. -/
noncomputable def phaseXOp (u : BitStr I J) (x : Bits m) :
    QState (Slots I J m t) →L[ℂ] QState (Slots I J m t) :=
  kernelMap fun s' s => if s' = s then dbPhase e u x (slotsDB e s) else 0

/-- The phase `(−1)^{u·b}` of an answer `b`, `1` at `⊥`. -/
def phaseWeight (u : BitStr I J) : Option B → ℂ
  | none => 1
  | some b => signOf (u.dot (e.symm b))

omit [DecidableEq I] [DecidableEq J] in
theorem dbPhase_eq (u : BitStr I J) (x : Bits m) (D : DB (Bits m) B) :
    dbPhase e u x D = phaseWeight e u (D.lookup x) := by
  unfold dbPhase phaseWeight
  split <;> simp_all

/-- **`O0` on a product state** multiplies the entry at `x` by the phase. -/
theorem phaseXOp_dbVec (k : Bits m → Option B → ℂ) (u : BitStr I J) (x : Bits m) :
    phaseXOp e t u x (dbVec e t k) =
      dbVec e t (Function.update k x fun o => k x o * phaseWeight e u o) := by
  ext s
  rw [phaseXOp, kernelMap_apply, Finset.sum_eq_single s (fun s' _ h => by simp [Ne.symm h])
    (by simp), if_pos rfl]
  by_cases hs : IsDBState e s
  · obtain ⟨hD, hsD⟩ := IsDBState.dbSlots_slotsDB e hs
    rw [← hsD, dbVec_dbSlots e _ hD, dbVec_dbSlots e _ hD, dbAmp_update, dbAmp_eq_mul k x,
      slotsDB_dbSlots e hD, dbPhase_eq]
    ring
  · rw [dbVec_of_not e _ hs, dbVec_of_not e _ hs, mul_zero]

open Classical in
/-- The matrix of `Dec` leaves the adversary's registers unchanged and applies `Dec_x`. -/
theorem decOp_eq_idLeft (W : Type) [Fintype W] [DecidableEq W] :
    decOp e W t = kernelMap (idLeft fun r : QueryReg W 1 (Bits m) (BitStr I J) =>
      reflKernel (decBlock e t (qIn r)) (decAmp e t (qIn r))) := by
  rw [decOp_eq, kernelOp_eq_kernelMap]
  rfl

/-- The matrix of `O0` leaves the adversary's registers unchanged and applies `O0` at `x, u`. -/
theorem phaseOp_eq_idLeft (W : Type) [Fintype W] [DecidableEq W] :
    phaseOp e W t = kernelMap (idLeft fun (r : QueryReg W 1 (Bits m) (BitStr I J)) s' s =>
      if s' = s then dbPhase e (qAns r) (qIn r) (slotsDB e s) else 0) := by
  rw [phaseOp, kernelOp_eq_kernelMap]
  congr 1
  funext b' b
  simp only [idLeft]
  by_cases h1 : b'.1 = b.1
  · by_cases h2 : b'.2 = b.2
    · simp [h1, h2, Prod.ext_iff]
    · simp [h1, h2, Prod.ext_iff]
  · simp [h1, Prod.ext_iff]

end Product

/-! ### Fourier-basis entries and the compression map -/

section Compress

/-- **The entry of an input with Fourier value `r`**: unrecorded (`⊥`) if `r = 0`, else recorded
with the answer register in the Fourier state `(1/√2^n) ∑_y (−1)^{r·y} |y⟩`. -/
noncomputable def fk (r : BitStr I J) : Option B → ℂ
  | none => if r = 0 then 1 else 0
  | some b => if r = 0 then 0 else hk (e.symm b) r

/-- **The entry of a recorded input with Fourier value `r`**: the answer register in the Fourier
state of `r`; `gk 0` is the uniform superposition `|τ⟩`. -/
noncomputable def gk (r : BitStr I J) : Option B → ℂ
  | none => 0
  | some b => hk (e.symm b) r

theorem sum_hk_left (r : BitStr I J) :
    ∑ y : BitStr I J, hk y r = if r = 0 then invSqrtCard I J * Fintype.card (BitStr I J) else 0 := by
  simp only [hk, ← Finset.mul_sum, BitStr.dot_comm r, sum_signOf_dot]
  split_ifs <;> simp

theorem sum_hk_left_equiv (r : BitStr I J) :
    ∑ y : BitStr I J, hk (e.symm (e y)) r =
      if r = 0 then invSqrtCard I J * Fintype.card (BitStr I J) else 0 := by
  simp only [Equiv.symm_apply_apply, sum_hk_left]

/-- `Dec_x` maps the entry `fk r` to `gk r`. -/
theorem fk_sub_decDefect (r : BitStr I J) :
    (fun o => fk e r o - decDefect e (fk e r) * decWeight (I := I) (J := J) o) = gk e r := by
  have hδ : decDefect e (fk e r) = if r = 0 then 1 else 0 := by
    by_cases h : r = 0
    · simp [decDefect, fk, h]
    · simp only [decDefect, fk, if_neg h, sum_hk_left_equiv, mul_zero, sub_zero]
  funext o
  rw [hδ]
  rcases o with _ | b <;> by_cases h : r = 0 <;> simp [fk, gk, decWeight, h, hk_zero]

/-- `Dec_x` maps the entry `gk r` to `fk r`. -/
theorem gk_sub_decDefect (r : BitStr I J) :
    (fun o => gk e r o - decDefect e (gk e r) * decWeight (I := I) (J := J) o) = fk e r := by
  have hδ : decDefect e (gk e r) = if r = 0 then -1 else 0 := by
    simp only [decDefect, gk, sum_hk_left_equiv, zero_sub]
    split_ifs
    · rw [← mul_assoc, invSqrtCard_mul_self_mul_card]
    · simp
  funext o
  rw [hδ]
  rcases o with _ | b <;> by_cases h : r = 0 <;> simp [fk, gk, decWeight, h, hk_zero]

/-- `O0` at `x, u` maps the entry `gk r` to `gk (r + u)`. -/
theorem gk_mul_phaseWeight (r u : BitStr I J) :
    (fun o => gk e r o * phaseWeight e u o) = gk e (r + u) := by
  funext o
  rcases o with _ | b
  · simp [gk, phaseWeight]
  · simp only [gk, phaseWeight, hk_add]

variable (t) in
/-- **The database register of a Fourier-basis truth table `F`** with at most `t` nonzero entries
(Zha19 section 1.1, p. 7, the compressed Fourier oracle with the QFT applied to each recorded
answer): the product state with entries `fk (F x)`. -/
noncomputable def fdb (F : Bits m → BitStr I J) : QState (Slots I J m t) :=
  dbVec e t fun x => fk e (F x)

/-- The databases on which `fdb F` is nonzero away from `x` have at most `|F|` entries away
from `x`. -/
theorem size_erase_le_of_dbAmpOff_fk {F : Bits m → BitStr I J} {x : Bits m} {D : DB (Bits m) B}
    (h : dbAmpOff (fun x => fk e (F x)) x D ≠ 0) : DB.size (D.erase x) ≤ fourierSize F := by
  rw [DB.size, Finmap.keys_erase]
  refine Finset.card_le_card fun x' hx' => ?_
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hx'
  obtain ⟨b, hb⟩ := DB.mem_iff_lookup.1 (Finmap.mem_keys.1 hmem)
  have hfac := (Finset.prod_ne_zero_iff.1 h) x' (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
  rw [hb] at hfac
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h0 => hfac ?_⟩
  simp [fk, h0]

open Classical in
/-- **The compressed oracle on `fdb F`** (CMS19 App. A, p. 47): if `F` has fewer than `t` nonzero
entries, `Dec_x ∘ O0 ∘ Dec_x` maps `fdb F` to `fdb (F + P_{x,u})`. -/
theorem decXOp_phaseXOp_decXOp_fdb (F : Bits m → BitStr I J) (x : Bits m) (u : BitStr I J)
    (hF : fourierSize F < t) :
    decXOp e t x (phaseXOp e t u x (decXOp e t x (fdb e t F))) = fdb e t (F + Pi.single x u) := by
  have hyp : ∀ k' : Option B → ℂ, ∀ D : DB (Bits m) B,
      dbAmpOff (Function.update (fun x' => fk e (F x')) x k') x D ≠ 0 →
        DB.size (D.erase x) < t := fun k' D h => by
    rw [dbAmpOff_update] at h
    exact (size_erase_le_of_dbAmpOff_fk e h).trans_lt hF
  have hk : (fun x' => fk e (F x')) = Function.update (fun x' => fk e (F x')) x (fk e (F x)) :=
    (Function.update_eq_self x _).symm
  rw [fdb, hk, decXOp_dbVec e _ x (hyp _), Function.update_self, Function.update_idem,
    fk_sub_decDefect, phaseXOp_dbVec, Function.update_self, Function.update_idem,
    gk_mul_phaseWeight, decXOp_dbVec e _ x (hyp _), Function.update_self, Function.update_idem,
    gk_sub_decDefect, fdb]
  congr 1
  funext x'
  by_cases h : x' = x
  · subst h
    simp
  · simp [h]

open Classical in
theorem dbAmp_fk_zero (D : DB (Bits m) B) :
    dbAmp (fun _ => fk e (0 : BitStr I J)) D = if D = ∅ then 1 else 0 := by
  have h : ∀ x, fk e (0 : BitStr I J) (D.lookup x) = if D.lookup x = none then 1 else 0 :=
    fun x => by cases D.lookup x <;> simp [fk]
  rw [dbAmp]
  simp_rw [h]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro hx
    exact Finmap.ext_lookup fun x => by rw [hx x (Finset.mem_univ x), Finmap.lookup_empty]
  · rintro rfl x _
    exact Finmap.lookup_empty x

open Classical in
/-- `fdb 0` is the empty database `|∅_t⟩`. -/
theorem fdb_zero_apply (s : Slots I J m t) :
    fdb e t (0 : Bits m → BitStr I J) s = if s = dbSlots e t (∅ : DB (Bits m) B) then 1 else 0 := by
  by_cases hs : IsDBState e s
  · obtain ⟨hD, hsD⟩ := IsDBState.dbSlots_slotsDB e hs
    rw [fdb, ← hsD, dbVec_dbSlots e _ hD]
    simp only [Pi.zero_apply, dbAmp_fk_zero]
    exact if_congr (dbSlots_inj e (by simp) hD).symm rfl rfl
  · rw [fdb, dbVec_of_not e _ hs, if_neg]
    rintro rfl
    exact hs (isDBState_dbSlots e (by simp))

variable (W : Type) [Fintype W] [DecidableEq W]

variable (t) in
/-- **The compression map** (Zha19 section 1.1, p. 7): `|r⟩ ⊗ |F⟩ ↦ |r⟩ ⊗ fdb F` from the
Fourier-basis oracle register to the `t`-slot database register. -/
noncomputable def compress : QState (PurReg W I J m) →L[ℂ] QState (SimRegister W I J m t) :=
  kernelMap (idLeft fun _ s F => fdb e t F s)

theorem compress_single (r : QueryReg W 1 (Bits m) (BitStr I J)) (F : Bits m → BitStr I J) :
    compress e t W (EuclideanSpace.single (r, F) 1) = ketTensor r (fdb e t F) := by
  rw [compress, kernelMap_idLeft_single]

theorem permOp_single {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) (b : ι) :
    permOp π (EuclideanSpace.single b (1 : ℂ)) = EuclideanSpace.single (π b) 1 := by
  ext i
  rw [permOp_apply, PiLp.single_apply, PiLp.single_apply]
  exact if_congr (Equiv.symm_apply_eq π) rfl rfl

open Classical in
/-- **The compressed oracle is the Fourier-basis query on compressed states** whose Fourier-basis
oracle register has fewer than `t` nonzero entries. -/
theorem compressedOracle_compress {v : QState (PurReg W I J m)}
    (hv : Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F < t}} v) :
    compressedOracle e W t (compress e t W v) = compress e t W (permOp (shiftPerm W) v) := by
  let σL : QState (PurReg W I J m) →L[ℂ] QState (PurReg W I J m) :=
    (permOp (shiftPerm (I := I) (J := J) (m := m) W)).toContinuousLinearEquiv.toContinuousLinearMap
  refine eq_of_supported (compressedOracle e W t ∘L compress e t W).toLinearMap
    (compress e t W ∘L σL).toLinearMap (fun b hb => ?_) hv
  obtain ⟨r, F⟩ := b
  show compressedOracle e W t (compress e t W (EuclideanSpace.single (r, F) 1)) =
    compress e t W (permOp (shiftPerm W) (EuclideanSpace.single (r, F) 1))
  rw [permOp_single, compress_single, compressedOracle, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, compress_single, decOp_eq_idLeft, phaseOp_eq_idLeft,
    kernelMap_idLeft_ketTensor, kernelMap_idLeft_ketTensor, kernelMap_idLeft_ketTensor]
  exact congrArg _ (decXOp_phaseXOp_decXOp_fdb e F _ _ hb)

/-- The Hadamard transform of the answer register commutes with `compress`. -/
theorem hadamard_compress (v : QState (PurReg W I J m)) :
    hadamard W t (compress e t W v) = compress e t W (ansH W _ v) := by
  rw [hadamard_eq_ansH, ansH_eq_kernelMap, ansH_eq_kernelMap, compress]
  exact idRight_comm _ _ v

/-- **A simulated query on a compressed state is the Fourier-basis query**, while fewer than `t`
inputs are recorded. -/
theorem simQuery_compress {v : QState (PurReg W I J m)}
    (hv : Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F < t}} v) :
    simQuery e W t (compress e t W v) = compress e t W (fourQuery v) := by
  rw [simQuery, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hadamard_compress, compressedOracle_compress e W (Supported.ansH hv), hadamard_compress,
    fourQuery_apply]

variable {O : Type} (A : QueryAlg (Bits m) (BitStr I J) t O)

theorem simStep_compress (k : ℕ) (v : QState (PurReg A.W I J m)) :
    simStep A k (compress e t A.W v) = compress e t A.W (liftStep A _ k v) :=
  controlled_kernelMap_idLeft _ _ v

theorem compress_fourInit : compress e t A.W (fourInit A) = simInit e A := by
  ext ⟨r, s⟩
  rw [compress, kernelMap_idLeft_apply,
    Finset.sum_eq_single 0 (fun F _ hF => by simp [fourInit, hF]) (by simp)]
  simp only [fourInit, simInit, if_true, mul_one, fdb_zero_apply]
  exact mul_comm _ _

/-- **Zha19 Lemma 4** (p. 15; CMS19 Lemma 3.3), for the fixed-bound compressed phase oracle of
CMS19: up to `t` queries, the run `Sim*(A)` is the Fourier-basis run of `A` with its oracle
register compressed. So `Dec_x` never meets the case `D(x) = ⊥, |D| = t` on the run of a
`t`-query algorithm. -/
theorem simStage_eq_compress {k : ℕ} (hk : k ≤ t) :
    simStage e A k = compress e t A.W (fourStage A k) := by
  induction k with
  | zero =>
    show simStep A 0 (simInit e A) = _
    rw [← compress_fourInit, simStep_compress]
    rfl
  | succ k ih =>
    show simStep A (k + 1) (simQuery e A.W t (simStage e A k)) = _
    have hsupp : Supported {b | b.2 ∈ {F : Bits m → BitStr I J | fourierSize F < t}}
        (fourStage A k) := fun b hb =>
      supported_fourStage A k b fun h => hb (lt_of_le_of_lt h (Nat.lt_of_succ_le hk))
    rw [ih (Nat.le_of_succ_le hk), simQuery_compress e A.W hsupp, simStep_compress]
    rfl

/-- `|Sim*(A)⟩ = compress (fourStage A t)`. -/
theorem simState_eq_compress : simState e A = compress e t A.W (fourStage A t) :=
  simStage_eq_compress e A le_rfl

end Compress

end GordieHowe.QROM
