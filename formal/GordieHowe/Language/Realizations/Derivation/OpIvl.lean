-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Rules
public import GordieHowe.Language.Realizations.Derivation.LinOp

@[expose] public section

/-!
# GordieHowe: intervals of operators and Logic builders, for derivations

Two interval rules of a derivation, each a fact `ivl d e lo hi`:

* `ivlApply k a e lo hi`, `e = .apply op x`: from the interval of the operand `x` (premise `k`)
  and, for an operator with a public operand `v`, an interval of `v` (premise `a`, which gives its
  coordinates as casts of integers): batched numbers from their digits
  (`batched B (fromDigits k b)`), the sum of the operand's interval scaled by the coefficients
  `bˡ mod p` read centred (`digitWeights`), each coefficient a cast of an integer, so the integer
  reading casts; a negacyclic product by `h` in coefficient form, `[−n H M, n H M]` for `h`'s magnitude `H` (`2 H <
  p`) and the operand's `M` (`NamedOp.polyIvl`: each matrix entry `±` a coefficient of `h`, the
  subtracted ones by the symmetric hull); in transform form (`negacyclicConv h (ntt ψ)`),
  `[−n p M, n p M]`: every matrix entry is `±` a coefficient of `INTT(h)`, an element of the prime
  subfield (`ZMod.castHom`), whose integer reading is a centred residue that casts back. The
  transform form's coefficients `INTT(h)` are no value of the program, so their magnitude is
  bounded only by `p`.
* `ivlLogic ks e`, `e = .logic op w args`: from intervals within `[0, 1]` of every argument
  (premises `ks`), `ivl d e 0 1`: on bits, every Logic builder is a bit (`LogicOp.eval_bool`), its
  polynomial form commuting with the cast of the integers (`LogicOp.eval_map`).
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **The centred weights of a number from `k` digits in base `b`** at the characteristic `p`:
`bˡ mod p` read centred, `l < k`. -/
def digitWeights (p b k : ℕ) : List ℤ := (List.range k).map fun l => centeredZ p (b ^ l % p)

section

variable (ir : RealizedProgram)

/-- **The interval of an operator application** at the characteristic `p`, the operand's interval
`J` and the public operand `pub` an interval premise names (`ivlApply`). -/
def specialIvl (p : ℕ) (J : Ivl) (pub : Option (ℕ × Ivl)) : NamedOp → Option Ivl
  | .batched B (.fromDigits k b) =>
    if 0 < p ∧ b < p ∧ 0 < B then some (groupSumIvl J (digitWeights p b k)) else none
  | .negacyclicConv h .coefficients =>
    match pub with
    | some (v, A) =>
      if v = h ∧ 2 * A.mag < p then some (Ivl.sym ((ir.value h).size * A.mag * J.mag)) else none
    | none => none
  | .negacyclicConv h (.ntt psi) =>
    if (pub.map (·.1)) = some h ∧ psi < p then
      some (Ivl.sym ((ir.value h).size * p * J.mag))
    else none
  | _ => none

/-- **The public operand's interval as values' intervals**: `A` for the named value, none
elsewhere. -/
def pubLeafI : Option (ℕ × Ivl) → ℕ → Option Ivl
  | some (v, A), u => if u = v then some A else none
  | none, _ => none

/-- **The interval of an operator application**: the transform-form and digit cases
(`specialIvl`), else the public polynomial and row-form operators' interval at the public
operand's interval (`NamedOp.polyIvl`: `polyBroadcast`, `polyMatVec` and `negacyclicConv` in
coefficient form, `rowDot` by a constant matrix, `acyclicConv`, and their batched forms). -/
def opIvl (p : ℕ) (J : Ivl) (pub : Option (ℕ × Ivl)) (op : NamedOp) : Option Ivl :=
  match ir.specialIvl p J pub op with
  | some J' => some J'
  | none => NamedOp.polyIvl ir (pubLeafI pub) p J op

/-- **The public operand an interval premise names**: the value `v` of field `d`'s and the
interval of the premise `a`'s fact `ivl d (leaf v) …`. -/
def pubOf (fs : List Fact) (d : ℕ) : Option ℕ → Option (ℕ × Ivl)
  | some j =>
    match fs[j]? with
    | some (.ivl d'' (.leaf v) lo hi) =>
      if d'' = d ∧ ir.valueField v = ir.domainField d then some (v, ⟨lo, hi⟩) else none
    | _ => none
  | none => none

/-- **`ivlApply k a e lo hi`** in domain `d`: `e = .apply op x`, `ivl d x` at premise `k`, the
public operand's interval at premise `a`: `ivl d e lo hi` for the operator's interval (`opIvl`)
within `[lo, hi]`. -/
def ivlApplyFact (fs : List Fact) (d k : ℕ) (a : Option ℕ) (e : Expr) (lo hi : ℤ) :
    Option Fact :=
  match e, fs[k]? with
  | .apply op x, some (.ivl d' x' l h) =>
    if d' = d ∧ x'.beq x = true ∧ d < ir.domains.length ∧
        2 < ir.charOf (ir.domainField d) then
      match opIvl ir (ir.charOf (ir.domainField d)) ⟨l, h⟩ (ir.pubOf fs d a) op with
      | some J => if J.Within lo hi then some (.ivl d e lo hi) else none
      | none => none
    else none
  | _, _ => none

/-- **The bit premises of a Logic builder's arguments**: each argument `args[i]` has an interval
within `[0, 1]` at premise `ks[i]`, of the first argument's length. -/
def logicPremOk (fs : List Fact) (d L : ℕ) : List ℕ → List Expr → Bool
  | [], [] => true
  | k :: ks, x :: xs =>
    (match fs[k]? with
      | some (.ivl d' x' lo hi) =>
        decide (d' = d) && x'.beq x && decide (0 ≤ lo) && decide (hi ≤ 1) &&
          decide (ir.exprLen x = L)
      | _ => false) && logicPremOk fs d L ks xs
  | _, _ => false

/-- **`ivlLogic ks e`** in domain `d`: `e = .logic op w args`, each argument within `[0, 1]`
(`logicPremOk`): `ivl d e 0 1`. -/
def ivlLogicFact (fs : List Fact) (d : ℕ) (ks : List ℕ) (e : Expr) : Option Fact :=
  match e with
  | .logic op w (x :: xs) =>
    if 0 < w ∧ ir.logicPremOk fs d (ir.exprLen x) ks (x :: xs) = true then
      some (.ivl d e 0 1)
    else none
  | _ => none

end

variable {ir : RealizedProgram} {I : Interp}

/-! ## Soundness -/

/-- **A sum of constant multiples of members of `A`** lies in `groupSumIvl A cs`. -/
theorem groupSumIvl_mem {A : Ivl} :
    ∀ (k : ℕ) (c : ℕ → ℤ) (y : ℕ → ℤ), (∀ l < k, y l ∈ A) →
      ∑ l ∈ Finset.range k, c l * y l ∈ groupSumIvl A ((List.range k).map c)
  | 0, _, _, _ => by simp [groupSumIvl, Ivl.mem_def]
  | k + 1, c, y, hy => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, groupSumIvl,
      Finset.sum_range_succ']
    rw [add_comm]
    exact Ivl.add_mem (Ivl.smul_mem _ (hy 0 (by omega)))
      (groupSumIvl_mem k (c ∘ Nat.succ) (y ∘ Nat.succ) fun l hl => hy _ (by omega))

/-- **The integer reading of a natural's cast** is the natural read centred, below `p`. -/
theorem coefInt_natCast {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) {c : ℕ} (hc : c < p) :
    (I f).coefInt (c : (I f).K) = centeredZ p c := by
  rw [FieldInterp.coefInt, FieldInterp.centered_eq, hp, htn c hc]

/-- **The integer reading of a batched number from digits with any base**: coordinate `j` is
`Σ_l (bˡ mod p, centred) x_{…+l}` (`block_batched_fromDigits_unit`). -/
theorem applyInt_batched_fromDigits_mod {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (hchar : CharP (I f).K p) (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) (hp0 : 0 < p)
    (leaf : ir.Valuation I) {b k base : ℕ} (hb : 0 < b)
    (hdec : (I f).decode base = (base : (I f).K)) (x : ℕ → ℤ) (j : ℕ) :
    NamedOp.applyInt ir f leaf (.batched b (.fromDigits k base)) x j =
      ∑ l : Fin k, centeredZ p (base ^ (l : ℕ) % p) * x (j / b * (b * k) + (j % b * k + l)) := by
  have hjb : j % b < b := Nat.mod_lt _ hb
  set c := j / b * (b * k)
  set a := j % b * k
  let g : ℕ → ℤ := fun t => if a ≤ t ∧ t < a + k then
    centeredZ p (base ^ ((c + t) - (c + a)) % p) * x (c + t) else 0
  have hentry : ∀ t : Fin (NamedOp.cols ir (.batched b (.fromDigits k base))),
      (I f).coefInt (NamedOp.block ir f leaf (.batched b (.fromDigits k base))
        (fun s => if s = (t : ℕ) then 1 else 0)
          (j % NamedOp.rows ir (.batched b (.fromDigits k base)))) *
        x (j / NamedOp.rows ir (.batched b (.fromDigits k base)) *
          NamedOp.cols ir (.batched b (.fromDigits k base)) + t) = g t := by
    intro t
    simp only [NamedOp.rows, NamedOp.cols, Nat.mul_one]
    rw [NamedOp.block_batched_fromDigits_unit ir leaf hjb]
    simp only [g]
    split_ifs with ht
    · rw [hdec, ← Nat.cast_pow, CharP.natCast_eq_natCast_mod _ p,
        coefInt_natCast hp htn (Nat.mod_lt _ hp0), show (c + t) - (c + a) = t - j % b * k by omega]
    · rw [show (0 : (I f).K) = ((0 : ℕ) : (I f).K) by simp, coefInt_natCast hp htn hp0]
      simp only [centeredZ, Nat.cast_zero, zero_mul]
      split_ifs <;> simp
  unfold NamedOp.applyInt
  rw [Finset.sum_congr rfl fun t _ => hentry t,
    Fin.sum_univ_eq_sum_range g (NamedOp.cols ir (.batched b (.fromDigits k base)))]
  change ∑ t ∈ Finset.range (b * k), g t = _
  rw [← Fin.sum_univ_eq_sum_range g (b * k)]
  have hak : a + k ≤ b * k := by
    have : (j % b + 1) * k ≤ b * k := Nat.mul_le_mul_right _ hjb
    simp only [a]
    nlinarith
  rw [RealizedProgram.sum_fin_indicator c a k (b * k)
    (fun u => centeredZ p (base ^ (u - (c + a)) % p) * x u) hak]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show c + (a + (l : ℕ)) - (c + a) = l by omega]

section Prime

variable {K : Type*} [Field K] {p : ℕ} [CharP K p] [hpr : _root_.Fact p.Prime]

/-- **A negacyclic product of prime-subfield elements is one** (`DFT.negacyclicConvCoeff_map`). -/
theorem negacyclic_mem_range {n : ℕ} {g u : ℕ → K}
    (hg : ∀ s < n, ∃ z : ZMod p, g s = ZMod.castHom (dvd_refl p) K z)
    (hu : ∀ s < n, ∃ z : ZMod p, u s = ZMod.castHom (dvd_refl p) K z) (r : ℕ) :
    ∃ z : ZMod p, Ops.negacyclic n g u r = ZMod.castHom (dvd_refl p) K z := by
  classical
  by_cases hr : r < n
  · let g' : Fin n → ZMod p := fun s => Classical.choose (hg s s.isLt)
    let u' : Fin n → ZMod p := fun s => Classical.choose (hu s s.isLt)
    have hg' : Ops.toFin n g = (ZMod.castHom (dvd_refl p) K) ∘ g' :=
      funext fun s => Classical.choose_spec (hg s s.isLt)
    have hu' : Ops.toFin n u = (ZMod.castHom (dvd_refl p) K) ∘ u' :=
      funext fun s => Classical.choose_spec (hu s s.isLt)
    refine ⟨LatticeCrypto.negacyclicConvCoeff g' u' ⟨r, hr⟩, ?_⟩
    rw [Ops.negacyclic, Ops.ofFin_of_lt _ hr, hg', hu', DFT.negacyclicConvCoeff_map]
  · refine ⟨0, ?_⟩
    rw [Ops.negacyclic, Ops.ofFin, dif_neg hr, map_zero]

/-- **The inverse transform of prime-subfield elements at a prime-subfield root is one**
(`Ops.map_inverseNtt`). -/
theorem inverseNtt_mem_range {n : ℕ} {ψ : K} {g : ℕ → K} (ψ' : ZMod p)
    (hψ : ψ = ZMod.castHom (dvd_refl p) K ψ')
    (hg : ∀ s < n, ∃ z : ZMod p, g s = ZMod.castHom (dvd_refl p) K z) (i : ℕ) :
    ∃ z : ZMod p, Ops.inverseNtt n ψ g i = ZMod.castHom (dvd_refl p) K z := by
  classical
  let g' : ℕ → ZMod p := fun s => if h : s < n then Classical.choose (hg s h) else 0
  refine ⟨Ops.inverseNtt n ψ' g' i, ?_⟩
  rw [Ops.map_inverseNtt, ← hψ]
  refine Ops.inverseNtt_congr (fun m hm => ?_) i
  simp only [g', dif_pos hm]
  exact Classical.choose_spec (hg m hm)

end Prime

/-- **A centred residue's magnitude** is at most the characteristic. -/
theorem abs_centeredZ_le {p c : ℕ} (hc : c < p) : |centeredZ p c| ≤ p := by
  unfold centeredZ
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

/-- **An operator whose matrix entries lie in the prime subfield** (`ZMod.castHom`), at output
coordinate `j`: its integer reading has magnitude at most `cols · p · M` on an operand of
magnitude `M`, and casts to its value on any operand the integers cast to. -/
theorem applyInt_of_range {f p : ℕ} (hp : (I f).spec.characteristic = p)
    [CharP (I f).K p] [_root_.Fact p.Prime] (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k)
    (leaf : ir.Valuation I) (op : NamedOp) {x : ℕ → ℤ} {y : ℕ → (I f).K} {Len M j : ℕ}
    (hj : j < Len / NamedOp.cols ir op * NamedOp.rows ir op)
    (hE : ∀ t < NamedOp.cols ir op, ∃ z : ZMod p,
      NamedOp.block ir f leaf op (fun s => if s = t then 1 else 0) (j % NamedOp.rows ir op) =
        ZMod.castHom (dvd_refl p) (I f).K z)
    (hx : ∀ t < Len, |x t| ≤ M) (hxy : ∀ t < Len, ((x t : ℤ) : (I f).K) = y t) :
    |NamedOp.applyInt ir f leaf op x j| ≤ NamedOp.cols ir op * p * M ∧
      ((NamedOp.applyInt ir f leaf op x j : ℤ) : (I f).K) = NamedOp.apply ir f leaf op y j := by
  have hr : 0 < NamedOp.rows ir op := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hj
    omega
  have hidx : ∀ t < NamedOp.cols ir op,
      j / NamedOp.rows ir op * NamedOp.cols ir op + t < Len := fun t ht =>
    NamedOp.lt_of_cols ir hr hj ht
  have hc : ∀ t : Fin (NamedOp.cols ir op),
      |(I f).coefInt (NamedOp.block ir f leaf op (fun s => if s = (t : ℕ) then 1 else 0)
          (j % NamedOp.rows ir op))| ≤ p ∧
        (((I f).coefInt (NamedOp.block ir f leaf op (fun s => if s = (t : ℕ) then 1 else 0)
          (j % NamedOp.rows ir op)) : ℤ) : (I f).K) =
          NamedOp.block ir f leaf op (fun s => if s = (t : ℕ) then 1 else 0)
            (j % NamedOp.rows ir op) := fun t => by
    obtain ⟨z, hz⟩ := hE t t.isLt
    rw [hz, ZMod.castHom_apply, ZMod.cast_eq_val, coefInt_natCast hp htn (ZMod.val_lt z)]
    exact ⟨abs_centeredZ_le (ZMod.val_lt z), centeredZ_cast p _⟩
  constructor
  · unfold NamedOp.applyInt
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ t ∈ (Finset.univ : Finset (Fin (NamedOp.cols ir op))),
        |(I f).coefInt (NamedOp.block ir f leaf op (fun s => if s = (t : ℕ) then 1 else 0)
          (j % NamedOp.rows ir op)) * x (j / NamedOp.rows ir op * NamedOp.cols ir op + t)| ≤
          (p : ℤ) * M := fun t _ => by
      rw [abs_mul]
      exact mul_le_mul (hc t).1 (hx _ (hidx t t.isLt)) (abs_nonneg _) (by positivity)
    refine (Finset.sum_le_sum this).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring_nf
    exact le_refl _
  · unfold NamedOp.applyInt
    rw [NamedOp.apply, NamedOp.block_eq_sum_unit ir leaf op]
    push_cast
    exact Finset.sum_congr rfl fun t _ => by rw [(hc t).2, hxy _ (hidx t t.isLt)]

/-- **A negacyclic product's matrix entries lie in the prime subfield** where its public
operand's coefficients do (in coefficient form) or its spectrum's and the root do (in transform
form). -/
theorem negacyclicConv_entries {f p : ℕ} [CharP (I f).K p] [_root_.Fact p.Prime]
    (leaf : ir.Valuation I) {h : ℕ} {form : ConvForm}
    (hh : ∀ s < (ir.value h).size, ∃ z : ZMod p,
      (castElt (leaf h s) : (I f).K) = ZMod.castHom (dvd_refl p) (I f).K z)
    (hψ : ∀ psi, form = .ntt psi → ∃ z : ZMod p,
      (I f).decode psi = ZMod.castHom (dvd_refl p) (I f).K z)
    (t r : ℕ) :
    ∃ z : ZMod p, NamedOp.block ir f leaf (.negacyclicConv h form)
      (fun s => if s = t then 1 else 0) r = ZMod.castHom (dvd_refl p) (I f).K z := by
  have hu : ∀ s < (ir.value h).size, ∃ z : ZMod p,
      (if s = t then (1 : (I f).K) else 0) = ZMod.castHom (dvd_refl p) (I f).K z := fun s _ => by
    by_cases hs : s = t
    · exact ⟨1, by simp [hs]⟩
    · exact ⟨0, by simp [hs]⟩
  simp only [NamedOp.block]
  refine negacyclic_mem_range (fun s hs => ?_) hu r
  cases form with
  | coefficients => exact hh s hs
  | ntt psi =>
    obtain ⟨ψ', hψ'⟩ := hψ psi rfl
    exact inverseNtt_mem_range ψ' hψ' hh s

/-- **The public operand an `ivlApply` step names** has its interval at a premise. -/
theorem ivlApply_pub {fs : List Fact} {d : ℕ} {a : Option ℕ} {v : ℕ} {A : Ivl}
    (h : ir.pubOf fs d a = some (v, A)) :
    ∃ j : ℕ, fs[j]? = some (Fact.ivl d (.leaf v) A.lo A.hi) ∧
      ir.valueField v = ir.domainField d := by
  cases a with
  | none => cases h
  | some j =>
    simp only [pubOf] at h
    split at h
    · rename_i d'' v' lo hi hj
      split_ifs at h with hd
      cases h
      obtain ⟨rfl, hf⟩ := hd
      exact ⟨j, hj, hf⟩
    · cases h

/-- **`ivlApplyFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlApplyFact_sound {primeNodes : ℕ → List String} (hwf : ir.WellFormed)
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k : ℕ} {a : Option ℕ} {e : Expr}
    {lo hi : ℤ} {f : Fact} (hf : ir.ivlApplyFact fs d k a e lo hi = some f) :
    f.HoldsWith ir rd := by
  unfold ivlApplyFact at hf
  split at hf
  case h_2 => cases hf
  rename_i op x d' x' l h hk
  split_ifs at hf with hc
  obtain ⟨rfl, hx, hd, hp2⟩ := hc
  obtain rfl := Expr.eq_of_beq hx
  generalize hpub : ir.pubOf fs d' a = pub at hf
  cases hJ : opIvl ir (ir.charOf (ir.domainField d')) ⟨l, h⟩ pub op with
  | none => rw [hJ] at hf; cases hf
  | some J =>
  rw [hJ] at hf
  simp only at hf
  split_ifs at hf with hW
  cases hf
  have hfd := domainField_lt hwf hd
  have hchar := charP_field hI hfd
  have hp : (I (ir.domainField d')).spec.characteristic = ir.charOf (ir.domainField d') :=
    hI.characteristic _ hfd
  have hprime : _root_.Fact (ir.charOf (ir.domainField d')).Prime :=
    ⟨CharP.char_is_prime (I (ir.domainField d')).K _⟩
  have htn := hL.toNat_natCast _ hfd
  have hdec := hL.decode_natCast _ hfd
  have hX : Fact.HoldsWith ir rd (.ivl d' x' l h) := hfs _ (List.mem_of_getElem? hk)
  intro i hi
  rw [exprLen_apply] at hi
  have hxm : ∀ t < ir.exprLen x', ir.evalIntWith rd d' x' t ∈ (⟨l, h⟩ : Ivl) :=
    fun t ht => ⟨(hX t ht).1, (hX t ht).2.1⟩
  have hxc : ∀ t < ir.exprLen x', ((ir.evalIntWith rd d' x' t : ℤ) :
      (I (ir.domainField d')).K) = ir.evalWith rd d' x' t := fun t ht => (hX t ht).2.2
  suffices hs : ir.evalIntWith rd d' (.apply op x') i ∈ J ∧
      ((ir.evalIntWith rd d' (.apply op x') i : ℤ) : (I (ir.domainField d')).K) =
        ir.evalWith rd d' (.apply op x') i by
    exact ⟨(Ivl.mem_of_within hW hs.1).1, (Ivl.mem_of_within hW hs.1).2, hs.2⟩
  rw [evalIntWith_apply]
  change _ ∈ J ∧ _ = NamedOp.apply ir (ir.domainField d') rd op (ir.evalWith rd d' x') i
  have hA : ∀ u A', pubLeafI pub u = some A' → ∀ s < (ir.value u).size,
      ir.evalIntWith rd d' (.leaf u) s ∈ A' ∧
        ((ir.evalIntWith rd d' (.leaf u) s : ℤ) : (I (ir.domainField d')).K) = castElt (rd u s) := by
    intro u A' hu s hs
    cases pub with
    | none => cases hu
    | some vA =>
      obtain ⟨v, A⟩ := vA
      by_cases huv : u = v
      · subst huv
        simp only [pubLeafI, if_true, Option.some.injEq] at hu
        obtain rfl := hu
        obtain ⟨j, hj, -⟩ := ivlApply_pub hpub
        have hH : Fact.HoldsWith ir rd (.ivl d' (.leaf u) A.lo A.hi) :=
          hfs _ (List.mem_of_getElem? hj)
        obtain ⟨h1, h2, h3⟩ := hH s hs
        exact ⟨⟨h1, h2⟩, h3⟩
      · simp [pubLeafI, huv] at hu
  have hconst : ∀ u J' es, pubLeafI pub u = some J' → (ir.value u).kind = .constant es →
      ∀ s, ir.evalIntWith rd d' (.leaf u) s = centeredZ (ir.charOf (ir.domainField d'))
        (es.getD s 0) := by
    intro u J' es hu hk s
    cases pub with
    | none => cases hu
    | some vA =>
      obtain ⟨v, A⟩ := vA
      by_cases huv : u = v
      · subst huv
        obtain ⟨j, -, hvf⟩ := ivlApply_pub hpub
        have hvf' : ir.valueField u < ir.fields.length := hvf ▸ hfd
        change ir.intOf rd u s = _
        have hc : (ir.field (ir.valueField u)).characteristic =
            ir.charOf (ir.domainField d') := by rw [hvf]
        simp only [intOf, hk, FieldInterp.centered_eq]
        rw [hI.characteristic _ hvf', hc]
      · simp [pubLeafI, huv] at hu
  unfold opIvl at hJ
  cases hS : ir.specialIvl (ir.charOf (ir.domainField d')) ⟨l, h⟩ pub op with
  | none =>
    rw [hS] at hJ
    have hP := NamedOp.applyInt_polyIvl ir hp hchar htn rd
      (il := fun u s => ir.evalIntWith rd d' (.leaf u) s) hA hdec hconst hJ
      (x := ir.evalIntWith rd d' x') (Len := ir.exprLen x') hi
    exact ⟨hP.1 hxm, hP.2 _ hxc⟩
  | some J' =>
  rw [hS] at hJ
  cases hJ
  have hcases : (∃ B k' b, op = .batched B (.fromDigits k' b)) ∨
      (∃ hv, op = .negacyclicConv hv .coefficients) ∨
      (∃ hv psi, op = .negacyclicConv hv (.ntt psi)) := by
    unfold specialIvl at hS
    split at hS <;> simp_all
  have hJ := hS
  rcases hcases with ⟨B, k', b, rfl⟩ | ⟨hv, rfl⟩ | ⟨hv, psi, rfl⟩
  · simp only [specialIvl] at hJ
    split_ifs at hJ with hb
    cases hJ
    obtain ⟨hp0, hbp, hB⟩ := hb
    have hdb := hdec b hbp
    have hr : 0 < NamedOp.rows ir (.batched B (.fromDigits k' b)) := by
      simp [NamedOp.rows]; omega
    have hidx : ∀ l : Fin k', i / B * (B * k') + (i % B * k' + l) < ir.exprLen x' := fun l => by
      have := NamedOp.lt_of_cols ir (op := .batched B (.fromDigits k' b)) hr hi
        (t := i % B * k' + l) (by
          simp only [NamedOp.cols]
          have := Nat.mod_lt i hB
          have := l.2
          nlinarith)
      simpa [NamedOp.rows, NamedOp.cols] using this
    rw [applyInt_batched_fromDigits_mod hp hchar htn hp0 rd hB hdb]
    constructor
    · rw [Fin.sum_univ_eq_sum_range (fun l => centeredZ _ (b ^ l % _) *
        ir.evalIntWith rd d' x' (i / B * (B * k') + (i % B * k' + l))) k']
      exact groupSumIvl_mem k' _ _ fun l hl => hxm _ (hidx ⟨l, hl⟩)
    · rw [NamedOp.apply_batched_fromDigits' ir rd hB]
      push_cast
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [centeredZ_cast, ← CharP.natCast_eq_natCast_mod, hdb, Nat.cast_pow,
        hxc _ (hidx l)]
  · cases pub with
    | none => simp [specialIvl] at hJ
    | some vA =>
    obtain ⟨v, A⟩ := vA
    simp only [specialIvl] at hJ
    split_ifs at hJ with hc
    cases hJ
    obtain ⟨rfl, hA2⟩ := hc
    obtain ⟨j, hj, hvf⟩ := ivlApply_pub hpub
    have hH : Fact.HoldsWith ir rd (.ivl d' (.leaf v) A.lo A.hi) :=
      hfs _ (List.mem_of_getElem? hj)
    have hvf' : ir.valueField v < ir.fields.length := hvf ▸ hfd
    have hpoly : NamedOp.polyIvl ir (fun u => if u = v then some A else none)
        (ir.charOf (ir.domainField d')) ⟨l, h⟩ (.negacyclicConv v .coefficients) =
          some (Ivl.sym ((ir.value v).size * A.mag * (⟨l, h⟩ : Ivl).mag)) := by
      simp [NamedOp.polyIvl, formIvl, hA2]
    have hP := NamedOp.applyInt_polyIvl ir hp hchar htn rd
      (il := fun u s => ir.evalIntWith rd d' (.leaf u) s)
      (fun u A' hu s hs => by
        by_cases huv : u = v
        · subst huv
          simp only [if_true, Option.some.injEq] at hu
          subst hu
          obtain ⟨h1, h2, h3⟩ := hH s hs
          exact ⟨⟨h1, h2⟩, h3⟩
        · simp [huv] at hu)
      hdec
      (fun u J' es hu hk s => by
        by_cases huv : u = v
        · subst huv
          change ir.intOf rd u s = _
          have hc : (ir.field (ir.valueField u)).characteristic =
              ir.charOf (ir.domainField d') := by rw [hvf]
          simp only [intOf, hk, FieldInterp.centered_eq]
          rw [hI.characteristic _ hvf', hc]
        · simp [huv] at hu)
      hpoly (x := ir.evalIntWith rd d' x') (Len := ir.exprLen x') hi
    exact ⟨hP.1 hxm, hP.2 _ hxc⟩
  · simp only [specialIvl] at hJ
    split_ifs at hJ with hc
    cases hJ
    obtain ⟨hpv, hpsi⟩ := hc
    obtain ⟨⟨v, A⟩, hpub', hv⟩ := Option.map_eq_some_iff.1 hpv
    simp only at hv
    subst hv
    rw [hpub'] at hpub
    obtain ⟨j, hj, -⟩ := ivlApply_pub hpub
    have hH : Fact.HoldsWith ir rd (.ivl d' (.leaf v) A.lo A.hi) :=
      hfs _ (List.mem_of_getElem? hj)
    have hh : ∀ s < (ir.value v).size, ∃ z : ZMod (ir.charOf (ir.domainField d')),
        (castElt (rd v s) : (I (ir.domainField d')).K) =
          ZMod.castHom (dvd_refl _) (I (ir.domainField d')).K z := fun s hs => by
      refine ⟨(ir.evalIntWith rd d' (.leaf v) s : ZMod _), ?_⟩
      rw [map_intCast, (hH s hs).2.2]
      rfl
    have hψ : ∀ psi', ConvForm.ntt psi = .ntt psi' → ∃ z : ZMod (ir.charOf (ir.domainField d')),
        (I (ir.domainField d')).decode psi' =
          ZMod.castHom (dvd_refl _) (I (ir.domainField d')).K z := fun psi' hf' => by
      cases hf'
      refine ⟨(psi : ZMod _), ?_⟩
      rw [map_natCast, hdec psi hpsi]
    have hR := applyInt_of_range hp htn rd (.negacyclicConv v (.ntt psi))
      (x := ir.evalIntWith rd d' x') (y := ir.evalWith rd d' x') (M := (⟨l, h⟩ : Ivl).mag) hi
      (fun t _ => negacyclicConv_entries rd hh hψ t _)
      (fun t ht => Ivl.abs_le_mag (hxm t ht)) hxc
    refine ⟨Ivl.mem_sym.2 ?_, hR.2⟩
    exact_mod_cast hR.1

/-- **A list of expressions' integer values** are their integer readings. -/
theorem evalIntList_eq (rd : ir.Valuation I) (d : ℕ) : ∀ args : List Expr,
    Expr.evalIntList ir (ir.domainField d) rd (ir.intOf rd)
      (ir.refInt rd (ir.domainField d) ir.exprs.length) (ir.refLen ir.exprs.length) args =
      args.map fun a t => ir.evalIntWith rd d a t
  | [] => rfl
  | a :: as => by
    simp only [Expr.evalIntList, List.map_cons, evalIntList_eq rd d as]
    rfl

/-- **A list of expressions' values** are their values. -/
theorem evalList_eq (rd : ir.Valuation I) (d : ℕ) : ∀ args : List Expr,
    Expr.evalList ir (ir.domainField d) rd (ir.refVal rd ir.exprs.length (ir.domainField d))
      (ir.refLen ir.exprs.length) args = args.map fun a t => ir.evalWith rd d a t
  | [] => rfl
  | a :: as => by
    simp only [Expr.evalList, List.map_cons, evalList_eq rd d as]
    rfl

/-- **The bit premises hold** (`logicPremOk`): every argument's integer reading is `0` or `1`
below `L`, and casts to its value. -/
theorem logicPremOk_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d L : ℕ} :
    ∀ {ks : List ℕ} {args : List Expr}, ir.logicPremOk fs d L ks args = true →
      ∀ a ∈ args, ∀ t < L, (ir.evalIntWith rd d a t = 0 ∨ ir.evalIntWith rd d a t = 1) ∧
        ((ir.evalIntWith rd d a t : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d a t
  | [], [], _, a, ha => by cases ha
  | k :: ks, x :: xs, h, a, ha => by
    simp only [logicPremOk, Bool.and_eq_true] at h
    obtain ⟨h0, hrest⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · split at h0
      · rename_i d' x' lo hi hk
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
        obtain ⟨⟨⟨⟨hd, hx⟩, hlo⟩, hhi⟩, hL⟩ := h0
        subst hd
        obtain rfl := Expr.eq_of_beq hx
        have hX : Fact.HoldsWith ir rd (.ivl d' x' lo hi) := hfs _ (List.mem_of_getElem? hk)
        intro t ht
        obtain ⟨h1, h2, h3⟩ := hX t (by omega)
        exact ⟨by omega, h3⟩
      · cases h0
    · exact logicPremOk_sound hfs hrest a ha
  | [], _ :: _, h, _, _ => by simp [logicPremOk] at h
  | _ :: _, [], h, _, _ => by simp [logicPremOk] at h

/-- **`ivlLogicFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlLogicFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ} {ks : List ℕ} {e : Expr} {f : Fact}
    (hf : ir.ivlLogicFact fs d ks e = some f) : f.HoldsWith ir rd := by
  unfold ivlLogicFact at hf
  split at hf
  case h_2 => cases hf
  rename_i op w x xs
  split_ifs at hf with hc
  cases hf
  obtain ⟨hw, hok⟩ := hc
  have hP := logicPremOk_sound hfs hok
  intro i hi
  have hi' : i < ir.exprLen x / w := hi
  have hwin : ∀ t < w, i * w + t < ir.exprLen x := fun t ht => by
    have h1 : (i + 1) * w ≤ ir.exprLen x / w * w := Nat.mul_le_mul_right _ hi'
    have h2 := Nat.div_mul_le_self (ir.exprLen x) w
    nlinarith
  have hint : ir.evalIntWith rd d (.logic op w (x :: xs)) i =
      op.eval w ((x :: xs).map fun a t => ir.evalIntWith rd d a t) i := by
    change op.eval w (Expr.evalIntList ir (ir.domainField d) rd (ir.intOf rd)
      (ir.refInt rd (ir.domainField d) ir.exprs.length) (ir.refLen ir.exprs.length) (x :: xs)) i = _
    rw [evalIntList_eq]
  have hval : ir.evalWith rd d (.logic op w (x :: xs)) i =
      op.eval w ((x :: xs).map fun a t => ir.evalWith rd d a t) i := by
    change op.eval w (Expr.evalList ir (ir.domainField d) rd
      (ir.refVal rd ir.exprs.length (ir.domainField d)) (ir.refLen ir.exprs.length) (x :: xs)) i = _
    rw [evalList_eq]
  have hbool : op.eval w ((x :: xs).map fun a t => ir.evalIntWith rd d a t) i = 0 ∨
      op.eval w ((x :: xs).map fun a t => ir.evalIntWith rd d a t) i = 1 := by
    refine LogicOp.eval_bool op w i fun g hg t ht => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    exact (hP a ha _ (hwin t ht)).1
  rw [hint, hval]
  refine ⟨by rcases hbool with h | h <;> rw [h] <;> norm_num,
    by rcases hbool with h | h <;> rw [h] <;> norm_num, ?_⟩
  have hmap := LogicOp.eval_map (Int.castRingHom (I (ir.domainField d)).K) op w
    ((x :: xs).map fun a t => ir.evalIntWith rd d a t) i
  simp only [eq_intCast] at hmap
  rw [hmap, List.map_map]
  refine LogicOp.eval_congr op w i ?_
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun a ha t ht => ?_
  exact (hP a ha _ (hwin t ht)).2

end GordieHowe.RealizedProgram
