-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.CoSimQuery
public import GordieHowe.Model.QROM.SimScratch

@[expose] public section

/-!
# Query points from local additions, with a scratch register

A query algorithm with request points `G` (over the oracle `X → BitStr I J`) whose steps are read
after lists of local additions of a base part `ω : X → Y₁` (`StepAdds` on its query registers):
before step `k`, the values `ω (x k i p)` added in sequence to the parts `L k i` on the branches
`on k i`. For the split `sp : Y ≃+ Y₁ × Y₂` of a real oracle `H : X → Y`, the algorithm `G` with a
scratch register `Y₁ × Y₂` in the uniform superposition (`plusAlg`) has query points on every
branch (`StepAdds.plus`, `StepAdds.allOn_plus`) whose action at `H` is the additions of
`base sp H` on `G`'s registers and shifts of the scratch (`permOp_plus_perm_plusEmb`). The scratch
stays uniform, so `simLaw` of the instance with the query points at `H` is `simLaw` of `G` read
after the additions of `base sp H` (`simLaw_plus_inst`).

- `unifVec`, `plusSplit`, `plusEmb`, `plusAlg`, `plusAlg_step`: the scratch register.
- `addLens`, `StepAdds.plus`, `StepAdds.allOn_plus`, `plus_add_perm_fst`,
  `permOp_plus_add_plusEmb`, `permOp_seqPerm_plusEmb`, `permOp_plus_perm_plusEmb`: the query
  points of the additions.
- `instSplit`, `slice_plus`, `plus_inst_step`, `plus_inst_init`, `simLaw_plus_inst`,
  `simState_plus_inst_ne`: the instance with the scratch.
-/

open Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace ReqQueryAlg

open GordieHowe.QROM

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)

/-! ### The uniform vector -/

/-- **The uniform superposition** over a finite type. -/
noncomputable def unifVec (Sc : Type) [Fintype Sc] : QState Sc :=
  WithLp.toLp 2 fun _ => ((Real.sqrt (Fintype.card Sc) : ℝ) : ℂ)⁻¹

theorem norm_unifVec (Sc : Type) [Fintype Sc] [Nonempty Sc] : ‖unifVec Sc‖ = 1 := by
  have h : ‖unifVec Sc‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [unifVec, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    have : (Fintype.card Sc : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp
  have h0 := norm_nonneg (unifVec Sc)
  nlinarith [h]

/-! ### The algorithm with a scratch register -/

variable (Sc : Type) [Fintype Sc] [DecidableEq Sc] [Nonempty Sc]

/-- The query registers of `G` with the scratch as those of `G` and the scratch. -/
def plusSplit : QueryReg (G.W × Sc) 1 (Bits m) (BitStr I J) ≃
    QueryReg G.W 1 (Bits m) (BitStr I J) × Sc where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A vector of `G`'s query registers with the scratch uniform. -/
noncomputable def plusEmb (x : QState (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    QState (QueryReg (G.W × Sc) 1 (Bits m) (BitStr I J)) :=
  relabel (plusSplit G Sc).symm (tensorVec x (unifVec Sc))

theorem norm_plusEmb (x : QState (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    ‖plusEmb G Sc x‖ = ‖x‖ := by
  rw [plusEmb, LinearIsometryEquiv.norm_map]
  have h : ‖tensorVec x (unifVec Sc)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    have hu : ∑ s, ‖(unifVec Sc) s‖ ^ 2 = 1 := by
      rw [← EuclideanSpace.norm_sq_eq, norm_unifVec, one_pow]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [tensorVec_apply, norm_mul, mul_pow]
    rw [← Finset.mul_sum, hu, mul_one]
  have := norm_nonneg (tensorVec x (unifVec Sc))
  nlinarith [norm_nonneg x]

/-- **`G` with a scratch register in the uniform superposition**: work register `G.W × Sc`, the
initial state with the scratch uniform, the steps of `G` on `G`'s registers, the requests, the
writes and the output of `G`. -/
noncomputable abbrev plusAlg : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O where
  W := G.W × Sc
  init := plusEmb G Sc G.init
  norm_init := by rw [norm_plusEmb, G.norm_init]
  step k := (relabel (plusSplit G Sc)).trans ((controlled fun _ => G.step k).trans
    (relabel (plusSplit G Sc).symm))
  req k w := G.req k w.1
  write k b := (G.write k b).prodCongr (Equiv.refl _)
  req_write k b w := G.req_write k b w.1
  out w := G.out w.1

theorem plusEmb_apply (x : QState (QueryReg G.W 1 (Bits m) (BitStr I J)))
    (p : QueryReg (G.W × Sc) 1 (Bits m) (BitStr I J)) :
    plusEmb G Sc x p = x (p.1.1, p.2) * unifVec Sc p.1.2 :=
  rfl

/-- `plusAlg`'s steps act on the vectors with the scratch uniform as `G`'s. -/
theorem plusAlg_step (k : Fin (t + 1)) (x : QState (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    (plusAlg G Sc).step k (plusEmb G Sc x) = plusEmb G Sc (G.step k x) := by
  change relabel (plusSplit G Sc).symm (controlled (fun _ => G.step k)
    (relabel (plusSplit G Sc) (relabel (plusSplit G Sc).symm (tensorVec x (unifVec Sc))))) = _
  rw [← relabel_symm, LinearIsometryEquiv.apply_symm_apply, controlled_tensorVec]
  rfl

/-! ### The query points of local additions -/

variable {Y₁ Y Y₂ : Type} [AddGroup Y₁] [Fintype Y] [DecidableEq Y] [AddGroup Y] [AddGroup Y₂]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₁] [Nonempty Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (D : StepAdds (QueryReg G.W 1 (Bits m) (BitStr I J)) (Fin (t + 1)) (Bits m) Y₁)

variable {G}

/-- **The answer part of query point `i` of step `k`** of `G` with the scratch `Y₁ × Y₂`: `sp.symm`
of the part `L k i` (on the branches `on k i`, the first scratch elsewhere) and the second
scratch. -/
def addLens (k : Fin (t + 1)) (i : Fin (D.nb k)) :
    RegLens (QueryReg (G.W × (Y₁ × Y₂)) 1 (Bits m) (BitStr I J)) Y where
  get q := sp.symm (if D.on k i (plusSplit G (Y₁ × Y₂) q).1 then
      (D.L k i).get (plusSplit G (Y₁ × Y₂) q).1 else (plusSplit G (Y₁ × Y₂) q).2.1,
    (plusSplit G (Y₁ × Y₂) q).2.2)
  set q y := (plusSplit G (Y₁ × Y₂)).symm (if D.on k i (plusSplit G (Y₁ × Y₂) q).1 then
      ((D.L k i).set (plusSplit G (Y₁ × Y₂) q).1 (sp y).1,
        ((plusSplit G (Y₁ × Y₂) q).2.1, (sp y).2))
    else ((plusSplit G (Y₁ × Y₂) q).1, ((sp y).1, (sp y).2)))
  get_set q y := by
    by_cases h : D.on k i (plusSplit G (Y₁ × Y₂) q).1
    · simp only [h, ↓reduceIte, Equiv.apply_symm_apply, D.on_set k i _ _, RegLens.get_set,
        Prod.mk.eta, AddEquiv.symm_apply_apply]
    · simp only [h, ↓reduceIte, Equiv.apply_symm_apply, Bool.false_eq_true, Prod.mk.eta,
        AddEquiv.symm_apply_apply]
  set_get q := by
    by_cases h : D.on k i (plusSplit G (Y₁ × Y₂) q).1
    · simp only [h, ↓reduceIte, AddEquiv.apply_symm_apply, RegLens.set_get, Prod.mk.eta,
        Equiv.symm_apply_apply]
    · simp only [h, ↓reduceIte, Bool.false_eq_true, AddEquiv.apply_symm_apply, Prod.mk.eta,
        Equiv.symm_apply_apply]
  set_set q y y' := by
    by_cases h : D.on k i (plusSplit G (Y₁ × Y₂) q).1
    · simp only [h, ↓reduceIte, Equiv.apply_symm_apply, D.on_set k i _ _, RegLens.set_set]
    · simp only [h, ↓reduceIte, Bool.false_eq_true, Equiv.apply_symm_apply]

/-- **The query points of the additions**: query point `i` of step `k` reads the point `x k i` of
`G`'s registers into the answer part `addLens`, on every branch. -/
def _root_.GordieHowe.Quantum.StepAdds.plus : StepAdds (QueryReg (G.W × (Y₁ × Y₂)) 1 (Bits m) (BitStr I J)) (Fin (t + 1))
    (Bits m) Y where
  nb := D.nb
  L k i := addLens sp D k i
  on _ _ _ := true
  x k i q := D.x k i (plusSplit G (Y₁ × Y₂) q).1
  on_set _ _ _ _ := rfl
  x_set k i q y := by
    change D.x k i (plusSplit G (Y₁ × Y₂) ((addLens sp D k i).set q y)).1 = _
    by_cases h : D.on k i (plusSplit G (Y₁ × Y₂) q).1
    · simp only [addLens, h, ↓reduceIte, Equiv.apply_symm_apply, D.x_set k i _ _]
    · simp only [addLens, h, ↓reduceIte, Bool.false_eq_true, Equiv.apply_symm_apply]

theorem _root_.GordieHowe.Quantum.StepAdds.allOn_plus : (D.plus sp).AllOn := fun _ _ _ => rfl

/-- **Query point `i` of step `k` at `H` acts on `G`'s registers as the addition of
`base sp H`.** -/
theorem plus_add_perm_fst (H : Bits m → Y) (k : Fin (t + 1)) (i : Fin (D.nb k))
    (q : QueryReg (G.W × (Y₁ × Y₂)) 1 (Bits m) (BitStr I J)) :
    (plusSplit G (Y₁ × Y₂) (((D.plus sp).add H k i).perm q)).1 =
      (D.add (fun x => (sp (H x)).1) k i).perm (plusSplit G (Y₁ × Y₂) q).1 := by
  rw [RegAdd.perm_apply, RegAdd.perm_apply]
  change (plusSplit G (Y₁ × Y₂) ((addLens sp D k i).set q ((addLens sp D k i).get q +
    (if true = true then H (D.x k i (plusSplit G (Y₁ × Y₂) q).1) else 0)))).1 =
    (D.L k i).set (plusSplit G (Y₁ × Y₂) q).1 ((D.L k i).get (plusSplit G (Y₁ × Y₂) q).1 +
      if D.on k i (plusSplit G (Y₁ × Y₂) q).1 then
        (sp (H (D.x k i (plusSplit G (Y₁ × Y₂) q).1))).1 else 0)
  by_cases h : D.on k i (plusSplit G (Y₁ × Y₂) q).1
  · simp only [addLens, h, ↓reduceIte, Equiv.apply_symm_apply, map_add,
      AddEquiv.apply_symm_apply, Prod.fst_add]
  · simp only [addLens, h, ↓reduceIte, Bool.false_eq_true, Equiv.apply_symm_apply, add_zero,
      RegLens.set_get]

/-- **Query point `i` of step `k` at `H` keeps the scratch uniform**: on `G`'s vectors with the
scratch uniform it is the addition of `base sp H`. -/
theorem permOp_plus_add_plusEmb (H : Bits m → Y) (k : Fin (t + 1)) (i : Fin (D.nb k))
    (x : QState (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    permOp ((D.plus sp).add H k i).perm (plusEmb G (Y₁ × Y₂) x) =
      plusEmb G (Y₁ × Y₂) (permOp (D.add (fun x => (sp (H x)).1) k i).perm x) := by
  ext q
  rw [permOp_apply, plusEmb_apply, plusEmb_apply, permOp_apply]
  have h := plus_add_perm_fst sp D H k i (((D.plus sp).add H k i).perm.symm q)
  rw [Equiv.apply_symm_apply] at h
  have h' : (plusSplit G (Y₁ × Y₂) (((D.plus sp).add H k i).perm.symm q)).1 =
      (D.add (fun x => (sp (H x)).1) k i).perm.symm (plusSplit G (Y₁ × Y₂) q).1 := by
    rw [Equiv.eq_symm_apply]
    exact h.symm
  have hu : ∀ a b : Y₁ × Y₂, unifVec (Y₁ × Y₂) a = unifVec (Y₁ × Y₂) b := fun _ _ => rfl
  change x (plusSplit G (Y₁ × Y₂) (((D.plus sp).add H k i).perm.symm q)).1 * _ =
    x ((D.add (fun x => (sp (H x)).1) k i).perm.symm (plusSplit G (Y₁ × Y₂) q).1) * _
  rw [h', hu]

variable (G) in
/-- Permutations in sequence that each act on the vectors with the scratch uniform as
permutations of `G`'s registers act in sequence so. -/
theorem permOp_seqPerm_plusEmb :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm (QueryReg (G.W × (Y₁ × Y₂)) 1 (Bits m) (BitStr I J)))
      (g : Fin n → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J))),
      (∀ i x, permOp (f i) (plusEmb G (Y₁ × Y₂) x) = plusEmb G (Y₁ × Y₂) (permOp (g i) x)) →
      ∀ x, permOp (seqPerm n f) (plusEmb G (Y₁ × Y₂) x) =
        plusEmb G (Y₁ × Y₂) (permOp (seqPerm n g) x)
  | 0, _, _, _, x => by
    change permOp (Equiv.refl _) _ = plusEmb G (Y₁ × Y₂) (permOp (Equiv.refl _) x)
    rw [permOp_refl', permOp_refl']
  | n + 1, f, g, h, x => by
    change permOp ((seqPerm n fun i => f i.castSucc).trans (f (Fin.last n))) _ =
      plusEmb G (Y₁ × Y₂) (permOp ((seqPerm n fun i => g i.castSucc).trans (g (Fin.last n))) x)
    rw [permOp_trans, permOp_trans, permOp_seqPerm_plusEmb n _ _ (fun i => h i.castSucc), h]

/-- **The query points of step `k` at `H` keep the scratch uniform**: on `G`'s vectors with the
scratch uniform they are the additions of `base sp H`. -/
theorem permOp_plus_perm_plusEmb (H : Bits m → Y) (k : Fin (t + 1))
    (x : QState (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    permOp ((D.plus sp).perm H k) (plusEmb G (Y₁ × Y₂) x) =
      plusEmb G (Y₁ × Y₂) (permOp (D.perm (fun x => (sp (H x)).1) k) x) :=
  permOp_seqPerm_plusEmb G _ _ _ (fun i x => permOp_plus_add_plusEmb sp D H k i x) x

/-! ### The instance with the scratch -/

variable (H : Bits m → Y) (a : ℕ → Req → Option Resp)

variable (G) in
/-- The work registers of the instance with the scratch as those of the instance and the scratch. -/
def instSplit (Sc : Type) : (G.W × Sc) × LogReg Req (t + 1) ≃ (G.W × LogReg Req (t + 1)) × Sc where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The slice of an instance vector at the logs `lg` with the scratch uniform. -/
theorem slice_plus (Sc : Type) [Fintype Sc] [DecidableEq Sc] [Nonempty Sc]
    {P' : Fin (t + 1) → Equiv.Perm (QueryReg (G.W × Sc) 1 (Bits m) (BitStr I J))}
    {P₀ : Fin (t + 1) → Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J))} (k : Fin (t + 1))
    (w : QState (QueryReg (G.W × LogReg Req (t + 1)) 1 (Bits m) (BitStr I J)))
    (lg : LogReg Req (t + 1)) :
    (WithLp.toLp 2 fun d => relabel ((plusAlg G Sc).withPerm P').logSplit
      (permOp ((((plusAlg G Sc).withPerm P').reqPerm a k).prodCongr (Equiv.refl _))
        (qEmb ((G.withPerm P₀).inst a) (((plusAlg G Sc).withPerm P').inst a) (instSplit G Sc)
          (unifVec Sc) w)) (d, lg) : QState (QueryReg (G.W × Sc) 1 (Bits m) (BitStr I J))) =
      plusEmb G Sc (WithLp.toLp 2 fun d => relabel (G.withPerm P₀).logSplit
        (permOp (((G.withPerm P₀).reqPerm a k).prodCongr (Equiv.refl _)) w) (d, lg)) := by
  ext d
  rfl

/-- **The instance's steps with the query points at `H` act on the vectors with the scratch
uniform as the instance's steps with the additions of `base sp H`.** -/
theorem plus_inst_step (k : Fin (t + 1))
    (w : QState (QueryReg (G.W × LogReg Req (t + 1)) 1 (Bits m) (BitStr I J))) :
    (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a).step k
        (qEmb ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
          (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a)
          (instSplit G (Y₁ × Y₂)) (unifVec (Y₁ × Y₂)) w) =
      qEmb ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
        (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a)
        (instSplit G (Y₁ × Y₂)) (unifVec (Y₁ × Y₂))
        (((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a).step k w) := by
  ext p
  obtain ⟨⟨⟨w', sc⟩, lg⟩, q⟩ := p
  change ((controlled fun _ =>
    ((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).step k)
    (relabel ((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).logSplit
      (permOp ((((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).reqPerm a
        k).prodCongr (Equiv.refl _))
        (qEmb ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
          (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a)
          (instSplit G (Y₁ × Y₂)) (unifVec (Y₁ × Y₂)) w)))) (((w', sc), q), lg) =
    ((controlled fun _ => (G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).step k)
      (relabel (G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).logSplit
        (permOp (((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).reqPerm a k).prodCongr
          (Equiv.refl _)) w))) ((w', q), lg) * unifVec (Y₁ × Y₂) sc
  rw [controlled_apply, controlled_apply, slice_plus a (Y₁ × Y₂) k w lg]
  change (permOp ((D.plus sp).perm H k)).trans ((plusAlg G (Y₁ × Y₂)).step k) _ ((w', sc), q) = _
  rw [LinearIsometryEquiv.trans_apply, permOp_plus_perm_plusEmb, plusAlg_step, plusEmb_apply]
  rfl

theorem plus_inst_init :
    (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a).init =
      qEmb ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
        (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a)
        (instSplit G (Y₁ × Y₂)) (unifVec (Y₁ × Y₂))
        ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a).init := by
  ext p
  obtain ⟨⟨⟨w', sc⟩, lg⟩, q⟩ := p
  change plusEmb G (Y₁ × Y₂) G.init ((w', sc), q) * (if lg = fun _ => none then 1 else 0) =
    G.init (w', q) * (if lg = fun _ => none then 1 else 0) * unifVec (Y₁ × Y₂) sc
  rw [plusEmb_apply]
  ring

/-- **`simLaw` of the instance with the query points at `H` is that of the instance with the
additions of `base sp H`**, the scratch staying uniform. -/
theorem simLaw_plus_inst :
    simLaw e (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a) =
      simLaw e ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a) :=
  simLaw_eq_of_scratch e ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
    (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a)
    (instSplit G (Y₁ × Y₂)) (unifVec (Y₁ × Y₂)) (plus_inst_init sp D H a)
    (fun k w => plus_inst_step sp D H a k w) (norm_unifVec _) fun _ => rfl

/-- **The support of the instance with the query points at `H` lies over that of the instance with
the additions of `base sp H`.** -/
theorem simState_plus_inst_ne
    (b : SimRegister ((G.W × (Y₁ × Y₂)) × LogReg Req (t + 1)) I J m t)
    (hb : simState e (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a) b ≠
      0) :
    simState e ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
      (((b.1.1.1.1, b.1.1.2), b.1.2), b.2) ≠ 0 := by
  have h := simStage_scratch e ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
    (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a)
    (instSplit G (Y₁ × Y₂)) (unifVec (Y₁ × Y₂)) (plus_inst_init sp D H a)
    (fun k w => plus_inst_step sp D H a k w) t
  have hb' : sEmb ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a)
      (((plusAlg G (Y₁ × Y₂)).withPerm fun k => (D.plus sp).perm H k).inst a)
      (instSplit G (Y₁ × Y₂)) (unifVec (Y₁ × Y₂))
      (simStage e ((G.withPerm fun k => D.perm (fun x => (sp (H x)).1) k).inst a) t) b ≠ 0 := by
    rw [← h]
    exact hb
  exact left_ne_zero_of_mul hb'

end ReqQueryAlg

end GordieHowe.Quantum
