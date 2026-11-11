-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Digits
public import GordieHowe.Language.RealizedProgram.Annotations
public import GordieHoweNative.Language.Completeness.Spectral

@[expose] public section

/-!
# GordieHowe: completeness certificates, the spectral convolutions and the field-form rows

The transformed value `z` of a spectrally realized convolution `k` of `RealizedProgram.convs` is
generated as its transformed value (`Gen.spec k`): the honest committed value is the integer reading
of the products `NTT_M(P_a) · NTT_M(P_b)` in the environment of the execution (`specNat`). Where the
convolution's facts check (`specHonestCB`), its products predicate holds at the source environment
of the honest committed values (`holds_specProductsC_srcEnv`), and so does every realization of a
source predicate's field equation through the convolutions (`specRowCB`,
`holds_specRowC_srcEnv`). A directly realized convolution's `C` is generated as its source
(`Gen.specC k`), and its products predicate `C = Σ_{u+v=k} a_u b_v` holds there
(`holds_directProductsC_srcEnv`). The field equation of a source field-form `mod_q` holds there where the
execution has its field equations (`holds_fieldRowC_srcEnv`).

The definitions are in `GordieHoweNative/Language/Completeness/Spectral.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {S : Structure}

/-- **The products predicate of a convolution with its honest facts is a predicate of the
program** (`ConvFacts.products_lt`). -/
theorem products_lt_of_specHonestCB {G : Gens} {k : ℕ} {cv : SpectralConv}
    (hk : ir.convs[k]? = some cv) (hc : ir.specHonestCB primeNodes S G k = true) :
    cv.products < ir.predicates.length := by
  unfold specHonestCB at hc
  rw [hk] at hc
  simp only at hc
  split at hc
  · split at hc
    case h_2 => cases hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.products.1.1
  split at hc
  case h_2 => cases hc
  rename_i d op pa op' pb z t hbody
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨s', r, q, -, -, -, F⟩ := hc.1.1.1.1.1.1.1.1.1.facts hbody
  exact F.products_lt

/-- **The row of a committed reading of a convolution with its honest facts is a predicate of the
program** (`ConvOkAt.committed`). -/
theorem row_lt_of_specHonestCB {G : Gens} {k : ℕ} {cv : SpectralConv}
    (hk : ir.convs[k]? = some cv) (hc : ir.specHonestCB primeNodes S G k = true) {kc r : ℕ}
    (hcm : cv.committed = some (kc, r)) : r < ir.predicates.length := by
  unfold specHonestCB at hc
  rw [hk] at hc
  simp only at hc
  split at hc
  · split at hc
    case h_2 => cases hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [hc.1.products.2] at hcm
    cases hcm
  split at hc
  case h_2 => cases hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact (hc.1.1.1.1.1.1.1.1.1.committed hcm).1

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  {G : Gens} (R : ir.CommittedFacts I G) {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The source environment of the honest committed values of the execution. -/
local notation "SE" => ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π

include hwf hI hL R hA in
/-- **The products predicate of a directly realized convolution holds** at the source environment
of the honest committed values where the execution accepts (`DirectOkAt`, `cHonestB`): the honest
`C` is the integer reading of the source read at the execution (`specCNat`, generated as `k`'s
committed `C`), the source reads alike there and is a cast of an integer, so `C` reads as the
source, which the products' sums read too (`directSums_eq_source`): `C − Σ = 0`. -/
theorem holds_directProductsC_srcEnv (hbd : ir.StmtBounded I x) {k : ℕ} {cv : SpectralConv}
    (hk : ir.convs[k]? = some cv) {d : ℕ} {lhs rhs : Expr} {t : Target}
    (hbody : (ir.predicate cv.products).body = .equal d lhs rhs t) (hok : ir.DirectOkAt d cv)
    (hC : ir.cHonestB primeNodes S G k d cv cv.read = true) :
    ir.HoldsWith (ir.reader SE) (ir.predicate cv.products).body := by
  have hok' := hok
  unfold DirectOkAt at hok'
  split at hok'
  case h_2 => exact hok'.elim
  rename_i so C d' lhs' z t' hsrc hread hbody'
  split at hok'
  case h_2 => exact hok'.elim
  rename_i q hq
  obtain ⟨hdd, -, -, F⟩ := hok'
  subst d'
  have F' := F
  obtain ⟨hsl, hrl, hpl, -, -, -, hzs, hfs, -, -, -, -, hCsz, hCv, hlenP, -, -, hneg, h2, -, -⟩ :=
    F'
  have hpo := hwf.predicates _ (predicate_mem hpl)
  rw [hbody'] at hpo
  have hd : d < ir.domains.length := (hpo.1 (d, .leaf z) (by simp [PredBody.exprs])).1
  set f := ir.domainField d with hfdef
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  have hdec := hL.decode_natCast f hf
  have hp0 : 0 < (ir.field f).characteristic := lt_trans (by norm_num) h2
  have hzero : ∀ v, ir.zeroConst v = true → ir.valueField v = f →
      ∀ i, ir.evalE (ir.reader SE) f (.leaf v) i = 0 := fun v hv hfv i =>
    evalE_leaf_zeroConst _ hv hfv (by rw [hL.decode_natCast _ hf 0 hp0, Nat.cast_zero]) i
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.ivlTab_justified primeNodes S.ivlTrie ir.declaredRanges
  unfold cHonestB at hC
  rw [hread] at hC
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, Bool.or_eq_true, Option.isSome_iff_exists, and_assoc] at hC
  obtain ⟨-, hown, hcell, hns, hfC, hsz, hEok, ⟨J, hJ⟩, hnodes⟩ := hC
  have hQ := Expr.eq_of_directProducts? hq
  rw [hbody', hQ]
  intro i hi
  rw [exprLen_add, hlenP] at hi
  have hiC : i < (ir.value C).size := by rw [hCsz]; exact hi
  have hiS : i < ir.exprLen (.ref cv.source) := by rw [← hsz]; exact hiC
  -- `C` reads as the source.
  have hCval : ir.evalWith (ir.reader SE) d (.leaf C) i =
      ir.evalWith (ir.reader SE) d (.ref cv.source) i := by
    simp only [evalWith]
    rw [evalE_leaf, reader_srcEnvL_of_privCellB x _ _ c π hcell hiC]
    simp only [genCommitted, withGens, if_neg hns, hown, hk, specCNat, hbody']
    rw [castElt_natCast hfC]
    have hagree : ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d
        (.ref cv.source) i = ir.evalWith (ir.reader SE) d (.ref cv.source) i := by
      simp only [evalWith]
      rw [evalE_congr fun w hw => ?_]
      rcases hnodes w hw with ⟨hsw, hew⟩ | hcw
      · exact (reader_srcEnvC_eq_exec0 hwf hI hL R hA π hsw hew).symm
      · funext j
        rw [reader_of_constant _ (kind_of_isConstant hcw),
          reader_of_constant _ (kind_of_isConstant hcw)]
    have hrange : ir.evalWith (ir.reader SE) d (.ref cv.source) i ∈
        (Int.castRingHom (I f).K).range := by
      obtain ⟨-, hcast⟩ := exprIvl_within_of hwf hI hL hIF hlok hd h2 hEok (lo := J.lo)
        (hi := J.hi) (by unfold srcIvl at hJ; rw [hJ]; exact ⟨le_rfl, le_rfl⟩) hiS
      exact ⟨_, hcast⟩
    rw [hagree]
    exact natCast_toNat_of_intCast hL hf (lt_trans (by norm_num) h2) hchar hrange
  have hsums := directSums_eq_source hwf.refsOrdered hzero hdec hsrc F i hi
  have hs1 := decode_pred_char (f := f) hdec hchar hneg
  have hz := hzero z (hzs z (by simp)) (hfs z (by simp)) i
  simp only [evalWith] at hCval ⊢
  rw [evalE_add, evalE_scale_const, hs1, hz, hsums, evalE_of_idView _ f hCv i hi, hCval]
  ring

include hwf hI hL R hA in
/-- **The products predicate of a spectrally realized convolution holds** at the source
environment of the honest committed values where the execution accepts (`specHonestCB`): the honest `z` is the integer reading of the products read at the
execution (`specNat`, generated as `k`'s transformed value), the left side reads alike there, and
the products are a cast of an integer, so the integer reading casts back to them
(`natCast_toNat_of_intCast`). -/
theorem holds_specProductsC_srcEnv (hbd : ir.StmtBounded I x) {k : ℕ} {cv : SpectralConv}
    (hk : ir.convs[k]? = some cv) (hc : ir.specHonestCB primeNodes S G k = true) :
    ir.HoldsWith (ir.reader SE) (ir.predicate cv.products).body := by
  unfold specHonestCB at hc
  rw [hk] at hc
  simp only at hc
  split at hc
  · split at hc
    case h_2 => cases hc
    rename_i d lhs rhs t hbody
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact holds_directProductsC_srcEnv hwf hI hL R hA π hbd hk hbody hc.1 hc.2
  split at hc
  case h_2 => cases hc
  rename_i d op pa op' pb z t hbody
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, Bool.or_eq_true, Option.isSome_iff_exists, and_assoc] at hc
  obtain ⟨hok, hea, heb, ⟨Ja, hJa⟩, ⟨Jb, hJb⟩, hnodes, hown, hcell, hns, -⟩ := hc
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
  have hlok := ir.ivlTab_justified primeNodes S.ivlTrie ir.declaredRanges
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
        psi' = cv.root → ir.ExprOk f P → ir.srcIvl (ir.srcLeafIvl primeNodes S) f P = some J →
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
/-- **The row of a convolution's committed reading holds** at the source environment of the honest
committed values where the execution accepts (`specHonestCB`, `specCHonestB`): the honest `C` is
the integer reading of the source read at the execution (`specCNat`, generated as `k`'s committed
`C`), the source reads alike there and is a cast of an integer (its interval from the source
values), so `C` reads as the source, which the reading equals where the products predicate holds
(`holds_specProductsC_srcEnv`, `convRead_eq_source`). -/
theorem holds_specCRowC_srcEnv (hbd : ir.StmtBounded I x) {k : ℕ} {cv : SpectralConv}
    (hk : ir.convs[k]? = some cv) (hc : ir.specHonestCB primeNodes S G k = true) {kc r : ℕ}
    (hcm : cv.committed = some (kc, r)) :
    ir.HoldsWith (ir.reader SE) (ir.predicate r).body := by
  have hprod := holds_specProductsC_srcEnv hwf hI hL R hA π hbd hk hc
  unfold specHonestCB at hc
  rw [hk] at hc
  simp only at hc
  split at hc
  · split at hc
    case h_2 => cases hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rw [hc.1.products.2] at hcm
    cases hcm
  split at hc
  case h_2 => cases hc
  rename_i d op pa op' pb z t hbody
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hok := hc.1.1.1.1.1.1.1.1.1
  have hC := hc.2
  obtain ⟨-, hlen, t', hb', -⟩ := hok.committed hcm
  obtain ⟨s', r', q', -, -, -, F⟩ := hok.facts hbody
  have hpl := F.products_lt
  have hpo := hwf.predicates _ (predicate_mem hpl)
  rw [hbody] at hpo
  have hd : d < ir.domains.length := (hpo.1 (d, .leaf z) (by simp [PredBody.exprs])).1
  set f := ir.domainField d with hfdef
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  have h2 : 2 < ir.charOf f := F.char
  have hp0 : 0 < (ir.field f).characteristic := lt_trans (by norm_num) h2
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.ivlTab_justified primeNodes S.ivlTrie ir.declaredRanges
  unfold specCHonestB at hC
  rw [hcm] at hC
  simp only at hC
  unfold cHonestB at hC
  split at hC
  case h_2 => cases hC
  rename_i C hkc
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, Bool.or_eq_true, Option.isSome_iff_exists, and_assoc] at hC
  obtain ⟨hkc_lt, hown, hcell, hns, hfC, hsz, hEok, ⟨J, hJ⟩, hnodes⟩ := hC
  have hread := convRead_eq_source hwf.refsOrdered (rd := ir.reader SE)
    (fun v hv hfv i => evalE_leaf_zeroConst _ hv hfv
      (by rw [hL.decode_natCast _ hf 0 hp0, Nat.cast_zero]) i)
    (hL.decode_natCast _ hf) hchar hok hprod
  rw [hb']
  intro i hi
  have hiS : i < ir.exprLen (.ref cv.source) := by
    rw [← hread.1, ← hlen]
    exact hi
  have hiC : i < (ir.value C).size := by rw [hsz]; exact hiS
  -- `C` reads as the source.
  have hCv : ir.evalWith (ir.reader SE) d (.ref kc) i =
      ir.evalWith (ir.reader SE) d (.ref cv.source) i := by
    simp only [evalWith]
    rw [evalE_ref hwf.refsOrdered _ _ hkc_lt, hkc, evalE_leaf,
      reader_srcEnvL_of_privCellB x _ _ c π hcell hiC]
    simp only [genCommitted, withGens, if_neg hns, hown, hk, specCNat, hbody]
    rw [castElt_natCast hfC]
    have hagree : ir.evalWith (ir.reader (ir.execEnv I x s 0 (ir.chal0 I))) d
        (.ref cv.source) i = ir.evalWith (ir.reader SE) d (.ref cv.source) i := by
      simp only [evalWith]
      rw [evalE_congr fun w hw => ?_]
      rcases hnodes w hw with ⟨hsw, hew⟩ | hcw
      · exact (reader_srcEnvC_eq_exec0 hwf hI hL R hA π hsw hew).symm
      · funext j
        rw [reader_of_constant _ (kind_of_isConstant hcw),
          reader_of_constant _ (kind_of_isConstant hcw)]
    have hrange : ir.evalWith (ir.reader SE) d (.ref cv.source) i ∈
        (Int.castRingHom (I f).K).range := by
      obtain ⟨-, hcast⟩ := exprIvl_within_of hwf hI hL hIF hlok hd h2 hEok (lo := J.lo)
        (hi := J.hi) (by unfold srcIvl at hJ; rw [hJ]; exact ⟨le_rfl, le_rfl⟩) hiS
      exact ⟨_, hcast⟩
    rw [hagree]
    exact natCast_toNat_of_intCast hL hf (lt_trans (by norm_num) h2) hchar hrange
  rw [hCv]
  exact hread.2 i hiS

include hwf hI hL R hA in
/-- **A realization of a predicate's field equation holds** at the source environment of the honest
committed values where the execution accepts (`specRowCB`), where the predicate holds there (a
source predicate does, `hmh`): its field equation holds (an `equal` itself; a `mod_0` by its
integer equality, its sides' integer readings cast to their values), and every spectrally realized
convolution's products predicate holds (`holds_specProductsC_srcEnv`), so the realization holds
(`holdsWith_realized_of_fieldEq`). -/
theorem holds_specRowC_srcEnv (hbd : ir.StmtBounded I x) {m q : ℕ}
    (h : ir.specRowCB primeNodes S G m q = true)
    (hmh : ir.inSource (ir.predicate m) = true ∨ ir.HoldsWith (ir.reader SE) (ir.predicate m).body) :
    ir.HoldsWith (ir.reader SE) (ir.predicate q).body := by
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.ivlTab_justified primeNodes S.ivlTrie ir.declaredRanges
  have hm : m < ir.predicates.length := by
    by_contra hm
    have hd : ir.predicate m = default :=
      (ir.predicate_eq_getD m).trans <| List.getD_eq_default _ _ (Nat.le_of_not_lt hm)
    unfold specRowCB at h
    rw [hd] at h
    simp only [Bool.and_eq_true] at h
    exact Bool.false_ne_true h.2
  have hsm : ir.HoldsWith (ir.reader SE) (ir.predicate m).body := by
    rcases hmh with hsrc | hh
    · exact hsat.preds _ (predicate_mem hm) hsrc
    · exact hh
  unfold specRowCB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hall, hB⟩ := h
  have hpo := hwf.predicates _ (predicate_mem hm)
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
    exact ⟨holds_specProductsC_srcEnv hwf hI hL R hA π hbd (List.getElem?_eq_getElem hk)
      (hall k hk), fun kc r hcm => holds_specCRowC_srcEnv hwf hI hL R hA π hbd
        (List.getElem?_eq_getElem hk) (hall k hk) hcm⟩
  split at hB
  · rename_i d e e' q' hbody
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
    obtain ⟨-, hR⟩ := hB
    rw [hbody] at hpo hsm
    exact key d e e' (realizedAdmits_of_realizedAtS hR) (hpo.1 (d, e) (by simp [PredBody.exprs])).1
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
    refine key d e e' (realizedAdmits_of_realizedAtS hR) hd he he' hlen.symm fun i hi => ?_
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
