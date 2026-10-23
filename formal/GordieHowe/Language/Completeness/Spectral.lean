-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Digits

@[expose] public section

/-!
# GordieHowe: completeness certificates, the spectral convolutions and the field-form rows

The transformed value `z` of a spectrally realized convolution `k` of `RealizedProgram.convs` is
generated as its transformed value (`Gen.spec k`): the honest committed value is the integer reading
of the products `NTT_M(P_a) · NTT_M(P_b)` in the environment of the execution (`specNat`). Where the
convolution's facts check (`specHonestCB`), its products predicate holds at the source environment
of the honest committed values (`holds_specProductsC_srcEnv`), and so does every realization of a
source predicate's field equation through the convolutions (`specRowCB`,
`holds_specRowC_srcEnv`). The field equation of a source field-form `mod_q` holds there where the
execution has its field equations (`holds_fieldRowC_srcEnv`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

variable (ir primeNodes) in
/-- **The honest facts of the spectrally realized convolution `k`** at the certificate's generators
`G`, as a check: `k` is a convolution of the program
whose products predicate is a field `equal` `NTT_M(P_a) · NTT_M(P_b) = z` of a domain `d` where it
is realized (`ConvOkAt`); the operand views are well formed and have intervals from the source
values (`srcIvl`); every value the products' left side reads is a source value reading no challenge
and no late value, or a constant; and `z` is a committed cell generated as `k`'s transformed value,
no source value. -/
def specHonestCB (G : Gens) (k : ℕ) : Bool :=
  match ir.convs[k]? with
  | none => false
  | some cv =>
    match (ir.predicate cv.products).body with
    | .equal d (.mul (.apply op pa) (.apply op' pb)) (.leaf z) _ =>
      decide (ir.ConvOkAt d cv) && decide (ir.ExprOk (ir.domainField d) pa) &&
        decide (ir.ExprOk (ir.domainField d) pb) &&
        (ir.srcIvl (ir.srcLeafIvl primeNodes) (ir.domainField d) pa).isSome &&
        (ir.srcIvl (ir.srcLeafIvl primeNodes) (ir.domainField d) pb).isSome &&
        (ir.exprNodes (.mul (.apply op pa) (.apply op' pb))).all (fun w =>
          (decide (ir.IsSourceValue w) && (ir.readsT.getD w []).isEmpty) || ir.isConstant w) &&
        decide (G.at z = .spec k) && ir.privCellB z && !decide (ir.IsSourceValue z)
    | _ => false

variable (ir primeNodes) in
/-- **Predicate `q` realizes the field equation of the source predicate `m`**, as a check:
every spectrally realized convolution has its honest
facts (`specHonestCB`), and `m` is a source field `equal` or `mod_0` with the target `realized q`
admitted (`RealizedAdmits`), a `mod_0` with the intervals of its sides from the source values within
the exported ones (`srcIvl`) in a field of characteristic above `2`. -/
def specRowCB (G : Gens) (m q : ℕ) : Bool :=
  (List.range ir.convs.length).all (ir.specHonestCB primeNodes G) &&
    ir.inSource (ir.predicate m) &&
      match (ir.predicate m).body with
      | .equal d e e' (.realized q') => q' == q && decide (ir.RealizedAdmits d e e' q)
      | .mod d 0 e e' real =>
        real.target == some (.realized q) && decide (ir.RealizedAdmits d e e' q) &&
          decide (IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes) (ir.domainField d) e)
            real.lhsLo real.lhsHi) &&
          decide (IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes) (ir.domainField d) e')
            real.rhsLo real.rhsHi) &&
          decide (2 < ir.charOf (ir.domainField d))
      | _ => false

/-- **The products predicate of a convolution with its honest facts is a predicate of the
program** (`ConvFacts.products_lt`). -/
theorem products_lt_of_specHonestCB {G : Gens} {k : ℕ} {cv : SpectralConv}
    (hk : ir.convs[k]? = some cv) (hc : ir.specHonestCB primeNodes G k = true) :
    cv.products < ir.predicates.length := by
  unfold specHonestCB at hc
  rw [hk] at hc
  simp only at hc
  split at hc
  case h_2 => cases hc
  rename_i d op pa op' pb z t hbody
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨s', r, q, -, -, -, F⟩ := hc.1.1.1.1.1.1.1.1.facts hbody
  exact F.products_lt

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  {G : Gens} (R : ir.CommittedFacts I G) {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The source environment of the honest committed values of the execution. -/
local notation "SE" => ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π

include hwf hI hL R hA in
/-- **The products predicate of a spectrally realized convolution holds** at the source
environment of the honest committed values where the execution accepts (`specHonestCB`): the honest `z` is the integer reading of the products read at the
execution (`specNat`, generated as `k`'s transformed value), the left side reads alike there, and
the products are a cast of an integer, so the integer reading casts back to them
(`natCast_toNat_of_intCast`). -/
theorem holds_specProductsC_srcEnv (hbd : ir.StmtBounded I x) {k : ℕ} {cv : SpectralConv}
    (hk : ir.convs[k]? = some cv) (hc : ir.specHonestCB primeNodes G k = true) :
    ir.HoldsWith (ir.reader SE) (ir.predicate cv.products).body := by
  unfold specHonestCB at hc
  rw [hk] at hc
  simp only at hc
  split at hc
  case h_2 => cases hc
  rename_i d op pa op' pb z t hbody
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, Bool.or_eq_true, Option.isSome_iff_exists, and_assoc] at hc
  obtain ⟨hok, hea, heb, ⟨Ja, hJa⟩, ⟨Jb, hJb⟩, hnodes, hown, hcell, hns⟩ := hc
  obtain ⟨s', r, q, -, -, hq, F⟩ := hok.facts hbody
  have hQ := Expr.eq_of_convProducts? hq
  simp only [Expr.mul.injEq, Expr.apply.injEq] at hQ
  obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hQ
  have hpl := F.products_lt
  have hpo := hwf.predicates _ (predicate_mem hpl)
  rw [hbody] at hpo
  have hd : d < ir.domains.length := (hpo.1 (d, .leaf z) (by simp [PredBody.exprs])).1
  have hlenP : ir.exprLen _ = ir.exprLen (.leaf z) := hpo.2
  set f := ir.domainField d with hfdef
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  have hdec := hL.decode_natCast f hf
  have h2 : 2 < ir.charOf f := F.char
  have hpsi : (I f).decode cv.root = (cv.root : (I f).K) := hdec _ F.root_lt
  have hlaM : cv.left ≤ cv.length := by have := F.fits; have := F.right_pos; omega
  have hlbM : cv.right ≤ cv.length := by have := F.fits; have := F.left_pos; omega
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.leafIvl_justified primeNodes ir.declaredRanges
  rw [hbody]
  intro i hi
  have hiz : i < (ir.value z).size := by
    rw [hlenP] at hi
    simpa [exprLen, Expr.len] using hi
  -- The honest `z`.
  have hzv : ir.evalWith (ir.reader SE) d (.leaf z) i =
      (((I f).toNat (ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d
        (.mul (.apply (.batched q.B (.ntt q.M q.psi .scheme)) (.reindex q.pA
          (.concat q.a (.leaf q.zA)))) (.apply (.batched q.B' (.ntt q.M' q.psi' .scheme))
            (.reindex q.pB (.concat q.b (.leaf q.zB))))) i) : ℕ) : (I f).K) := by
    simp only [evalWith]
    rw [evalE_leaf, reader_srcEnvL_of_privCellB x _ _ c π hcell hiz]
    simp only [genCommitted, withGens, if_neg hns, hown, hk, specNat, hbody]
    exact castElt_natCast (F.fields z (by simp)) _
  -- The products read alike at the execution.
  have hagree : ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d
      (.mul (.apply (.batched q.B (.ntt q.M q.psi .scheme)) (.reindex q.pA
        (.concat q.a (.leaf q.zA)))) (.apply (.batched q.B' (.ntt q.M' q.psi' .scheme))
          (.reindex q.pB (.concat q.b (.leaf q.zB))))) i =
      ir.evalWith (ir.reader SE) d
      (.mul (.apply (.batched q.B (.ntt q.M q.psi .scheme)) (.reindex q.pA
        (.concat q.a (.leaf q.zA)))) (.apply (.batched q.B' (.ntt q.M' q.psi' .scheme))
          (.reindex q.pB (.concat q.b (.leaf q.zB))))) i := by
    simp only [evalWith]
    rw [evalE_congr fun w hw => ?_]
    rcases hnodes w hw with ⟨hsw, hew⟩ | hcw
    · exact (reader_srcEnvC_eq_exec0 hwf hI hL R hA π hsw hew).symm
    · funext j
      rw [reader_of_constant _ (kind_of_isConstant hcw), reader_of_constant _ (kind_of_isConstant hcw)]
  rw [hzv, hagree]
  -- The products are a cast of an integer.
  have hrange : ir.evalWith (ir.reader SE) d
      (.mul (.apply (.batched q.B (.ntt q.M q.psi .scheme)) (.reindex q.pA
        (.concat q.a (.leaf q.zA)))) (.apply (.batched q.B' (.ntt q.M' q.psi' .scheme))
          (.reindex q.pB (.concat q.b (.leaf q.zB))))) i ∈ (Int.castRingHom (I f).K).range := by
    have hiBM : i < cv.blocks * cv.length := by
      have h' := hi
      rw [exprLen_mul, exprLen_apply, exprLen_reindex, F.pA, IndexMap.size_zeroExtend hlaM] at h'
      simp only [NamedOp.cols, NamedOp.rows, F.qB.1, F.qM.1] at h'
      exact lt_of_lt_of_le h' (Nat.div_mul_le_self _ _)
    have hblk : i / cv.length < cv.blocks := by
      have hM0 : 0 < cv.length := by have := F.left_pos; omega
      exact (Nat.div_lt_iff_lt_mul hM0).2 hiBM
    have hside : ∀ (B' M' psi' : ℕ) (P : Expr) (J : Ivl), B' = cv.blocks → M' = cv.length →
        psi' = cv.root → ir.ExprOk f P → ir.srcIvl (ir.srcLeafIvl primeNodes) f P = some J →
        ir.exprLen P = cv.blocks * cv.length →
        ir.evalE (ir.reader SE) f (.apply (.batched B' (.ntt M' psi' .scheme)) P) i ∈
          (Int.castRingHom (I f).K).range := by
      intro B' M' psi' P J hB hM hp hP hJ hPl
      subst hB hM hp
      have hrow : i < cv.blocks * NamedOp.rows ir (.ntt cv.length cv.root .scheme) := hiBM
      rw [evalE_apply_batched _ _ _ _ _ hrow]
      simp only [NamedOp.block, NamedOp.rows, NamedOp.cols, hpsi]
      rw [Ops.nttScheme_apply F.pow2 _ _ (Nat.mod_lt _ (by have := F.left_pos; omega))]
      refine Subring.sum_mem _ fun t _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ ?_ _)
      · have hj : i / cv.length * cv.length + (t : ℕ) < ir.exprLen P := by
          rw [hPl]
          exact IndexMap.block_lt hblk t.isLt
        obtain ⟨-, hcast⟩ := exprIvl_within_of hwf hI hL hIF hlok
          hd h2 hP (lo := J.lo) (hi := J.hi) (by unfold srcIvl at hJ; rw [hJ]; exact ⟨le_rfl, le_rfl⟩) hj
        exact ⟨_, hcast⟩
      · exact ⟨cv.root, by simp⟩
    have hlenA : ir.exprLen (.reindex q.pA (.concat q.a (.leaf q.zA))) = cv.blocks * cv.length := by
      rw [exprLen_reindex, F.pA, IndexMap.size_zeroExtend hlaM]
    have hlenB : ir.exprLen (.reindex q.pB (.concat q.b (.leaf q.zB))) = cv.blocks * cv.length := by
      rw [exprLen_reindex, F.pB, IndexMap.size_zeroExtend hlbM]
    simp only [evalWith]
    rw [evalE_mul]
    exact Subring.mul_mem _ (hside _ _ _ _ Ja F.qB.1 F.qM.1 F.qpsi.1 hea hJa hlenA)
      (hside _ _ _ _ Jb F.qB.2 F.qM.2 F.qpsi.2 heb hJb hlenB)
  exact (natCast_toNat_of_intCast hL hf (lt_trans (by norm_num) h2) hchar hrange).symm

include hwf hI hL R hA in
/-- **A realization of a source predicate's field equation holds** at the source environment of
the honest committed values where the execution accepts (`specRowCB`): the
source predicate's field equation holds there (a source `equal` itself; a source `mod_0` by its
integer equality, its sides' integer readings cast to their values), and every spectrally realized
convolution's products predicate holds (`holds_specProductsC_srcEnv`), so the realization holds
(`holdsWith_realized_of_fieldEq`). -/
theorem holds_specRowC_srcEnv (hbd : ir.StmtBounded I x) {m q : ℕ}
    (h : ir.specRowCB primeNodes G m q = true) :
    ir.HoldsWith (ir.reader SE) (ir.predicate q).body := by
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.leafIvl_justified primeNodes ir.declaredRanges
  have hm : m < ir.predicates.length := by
    by_contra hm
    have hd : ir.predicate m = default := List.getD_eq_default _ _ (Nat.le_of_not_lt hm)
    unfold specRowCB at h
    rw [hd] at h
    simp only [Bool.and_eq_true] at h
    exact Bool.false_ne_true h.2
  unfold specRowCB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hall, hsrc⟩, hB⟩ := h
  have hpo := hwf.predicates _ (predicate_mem hm)
  have hsm := hsat.preds _ (predicate_mem hm) hsrc
  have key : ∀ d e e', ir.RealizedAdmits d e e' q → d < ir.domains.length →
      ir.ExprOk (ir.domainField d) e → ir.ExprOk (ir.domainField d) e' →
      ir.exprLen e' = ir.exprLen e →
      (∀ i < ir.exprLen e, ir.evalWith (ir.reader SE) d e i = ir.evalWith (ir.reader SE) d e' i) →
      ir.HoldsWith (ir.reader SE) (ir.predicate q).body := by
    intro d e e' hR hd he he' hlen hfe
    have hf := domainField_lt hwf hd
    have hp0 : 0 < (ir.field (ir.domainField d)).characteristic := by
      rw [← hI.characteristic _ hf, ← hI.ringChar _ hf]
      exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite (I (ir.domainField d)).K _)
    refine holdsWith_realized_of_fieldEq hwf.refsOrdered
      (fun v hv hfv i => evalE_leaf_zeroConst _ hv hfv
        (by rw [hL.decode_natCast _ hf 0 hp0, Nat.cast_zero]) i)
      (hL.decode_natCast _ hf) (charP_field hI hf) (fun cv hcv _ => ?_) hR he.shape he'.shape hlen hfe
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hcv
    exact holds_specProductsC_srcEnv hwf hI hL R hA π hbd (List.getElem?_eq_getElem hk)
      (hall k hk)
  split at hB
  · rename_i d e e' q' hbody
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
    obtain ⟨-, hR⟩ := hB
    rw [hbody] at hpo hsm
    exact key d e e' hR (hpo.1 (d, e) (by simp [PredBody.exprs])).1
      (hpo.1 (d, e) (by simp [PredBody.exprs])).2 (hpo.1 (d, e') (by simp [PredBody.exprs])).2
      hpo.2.symm hsm
  · rename_i d e e' real hbody
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨⟨-, hR⟩, hwe⟩, hwe'⟩, h2⟩ := hB
    rw [hbody] at hpo hsm
    have hd := (hpo.1 (d, e) (by simp [PredBody.exprs])).1
    have he := (hpo.1 (d, e) (by simp [PredBody.exprs])).2
    have he' := (hpo.1 (d, e') (by simp [PredBody.exprs])).2
    have hlen : ir.exprLen e = ir.exprLen e' := hpo.2
    refine key d e e' hR hd he he' hlen.symm fun i hi => ?_
    obtain ⟨-, hc⟩ := exprIvl_within_of hwf hI hL hIF hlok hd h2 he hwe hi
    obtain ⟨-, hc'⟩ := exprIvl_within_of hwf hI hL hIF hlok hd h2 he' hwe'
      (by rw [← hlen]; exact hi)
    have hz := hsm i hi
    rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at hz
    rw [← hc, ← hc', hz]
  · cases hB

include hwf hI hL R hA in
/-- **The field equation of a source field-form `mod_q` holds** at the source environment of the
honest committed values where the execution has its field equations (`hE`): the source environment
agrees with the execution's on the source values (`agreeOnSourceVals_srcEnvC`), so it has them too
(`holds_fieldRow`). -/
theorem holds_fieldRowC_srcEnv (hE : ir.FieldEqsAt I (ir.execEnv I x s l c)) {q : ℕ}
    (h : ir.fieldRowRealB q = true) : ir.HoldsWith (ir.reader SE) (ir.predicate q).body :=
  holds_fieldRow hwf hI hL ((agreeOnSourceVals_srcEnvC hwf hI hL R hA π).symm.fieldEqsAt R.sourceValid
    R.srcNoMessage hE) h

end

end GordieHowe.RealizedProgram
