-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Basic
public import GordieHowe.Language.RealizedProgram.CellsLowering

@[expose] public section

/-!
# GordieHowe: the negacyclic transforms, for derivations

The transform instances of the linear-operator rule (`LinOpStep`), each a structured identity
at a root `ψ` and a size `n` the checker decides (`rootOkB`: `n = 2^k` below the characteristic
`p > 2`, `ψ < p`, `ψ^n ≡ −1 (mod p)`, so `ψ` is a primitive `2n`-th root of unity and `n` is
invertible, `root_facts`), proved from the transforms' lemmas (`Ops.inverseNtt_nttScheme`,
`Ops.nttScheme_inverseNtt`, `Ops.nttScheme_negacyclic`, `Ops.inverseNtt_mul_nttScheme`,
`DFT.sum_pow_mul_inv_pow_eq`), with no matrix built:

* `nttInv n ψ x`: `INTT(NTT x) = x`, block by block;
* `inttInv n ψ y`: `NTT(INTT y) = y`, block by block;
* `convNtt h ψ x`: the negacyclic product by `h` given in transform form,
  `negacyclicConv h (ntt ψ) x = INTT(h · NTT x)`, for `x` of one block;
* `convCoef h ψ x`: the convolution theorem, `NTT(negacyclicConv h x) = NTT h · NTT x`, for `x`
  of one block;
* `transposeInv n ψ ψ' x`: the transposed transform at `ψ' = ψ⁻¹` inverts the natural-order
  transform up to `n`, `nttTranspose ψ' (ntt_natural ψ x) = n · x`, block by block;
* `convBcastNtt t K ψ x` and `convMatNtt a K L ψ x`: the polynomial broadcast and matrix-vector
  products with public operands in transform form, `INTT(t_i · NTT x)` and
  `INTT(Σ_l a_{il} · NTT x_l)` per output block `i`, the operands' blocks read by index maps
  (`bcastMap`, `matPerm`) and the `L` terms summed by `sum L`;
* `adjoint n ψ y x`: the adjoint pairing of the transposed and the natural-order transforms,
  `Σ (nttTranspose ψ y) ⊙ x = Σ y ⊙ ntt_natural ψ x`, an equation of two sums, true at every
  `ψ` (`Finset.sum_comm`), so it checks only the lengths.
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **The broadcast of a block of `m` coordinates to `K` blocks**: entry `u` is `u mod m`. -/
def bcastMap (K m : ℕ) : IndexMap := List.replicate K (0, 1, m)

/-- **The terms of a polynomial matrix-vector product, grouped by output coordinate**: the
products of block `(i, l)` (`(i L + l) n + s`) reordered so that the `L` terms of output
coordinate `i n + s` are consecutive, entry `(i n + s) L + l` the term `(i L + l) n + s`. -/
def matPerm (K L n : ℕ) : IndexMap :=
  (List.range (K * n)).flatMap fun q => [(q / n * (L * n) + q % n, (n : ℤ), L)]

/-- **The root `ψ` and the size `n` of a transform check** at the characteristic `p`: `n = 2^k`
below `p > 2`, `0 < n`, `ψ < p` and `ψ^n ≡ −1 (mod p)`. -/
def rootOkB (p n psi : ℕ) : Bool :=
  decide (2 < p ∧ psi < p ∧ 0 < n ∧ n < p ∧ n = 2 ^ Nat.log2 n ∧ psi ^ n % p = p - 1)

section

variable (ir : RealizedProgram)

/-- **The transform instances of `linop`** in domain `d` of characteristic `p`. -/
def nttFact (d : ℕ) : LinOpStep → Option Fact
  | .nttInv n psi x =>
    if d < ir.domains.length ∧ rootOkB (ir.charOf (ir.domainField d)) n psi = true then
      some (.eq d (.apply (.inverseNtt n psi) (.apply (.ntt n psi .scheme) x)) x)
    else none
  | .inttInv n psi y =>
    if d < ir.domains.length ∧ rootOkB (ir.charOf (ir.domainField d)) n psi = true then
      some (.eq d (.apply (.ntt n psi .scheme) (.apply (.inverseNtt n psi) y)) y)
    else none
  | .convNtt h psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) (ir.value h).size psi = true ∧
        ir.exprLen x = (ir.value h).size then
      some (.eq d (.apply (.negacyclicConv h (.ntt psi)) x)
        (.apply (.inverseNtt (ir.value h).size psi)
          (.mul (.leaf h) (.apply (.ntt (ir.value h).size psi .scheme) x))))
    else none
  | .convCoef h psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) (ir.value h).size psi = true ∧
        ir.exprLen x = (ir.value h).size then
      some (.eq d (.apply (.ntt (ir.value h).size psi .scheme)
          (.apply (.negacyclicConv h .coefficients) x))
        (.mul (.apply (.ntt (ir.value h).size psi .scheme) (.leaf h))
          (.apply (.ntt (ir.value h).size psi .scheme) x)))
    else none
  | .transposeInv n psi psi' x =>
    if d < ir.domains.length ∧ rootOkB (ir.charOf (ir.domainField d)) n psi = true ∧
        psi' < ir.charOf (ir.domainField d) ∧ psi * psi' % ir.charOf (ir.domainField d) = 1 then
      some (.eq d (.apply (.nttTranspose n psi') (.apply (.ntt n psi .natural) x))
        (.scale (.const n) x))
    else none
  | .convBcastNtt t K psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) ((ir.value t).size / K) psi = true ∧
        (ir.value t).size = K * ((ir.value t).size / K) ∧
        ir.exprLen x = (ir.value t).size / K then
      some (.eq d (.apply (.polyBroadcast t K (.ntt psi)) x)
        (.apply (.inverseNtt ((ir.value t).size / K) psi)
          (.mul (.leaf t) (.reindex (bcastMap K ((ir.value t).size / K))
            (.apply (.ntt ((ir.value t).size / K) psi .scheme) x)))))
    else none
  | .convMatNtt a K L psi x =>
    if d < ir.domains.length ∧
        rootOkB (ir.charOf (ir.domainField d)) ((ir.value a).size / (K * L)) psi = true ∧
        (ir.value a).size = K * L * ((ir.value a).size / (K * L)) ∧ 0 < L ∧
        ir.exprLen x = L * ((ir.value a).size / (K * L)) then
      some (.eq d (.apply (.polyMatVec a K L (.ntt psi)) x)
        (.apply (.inverseNtt ((ir.value a).size / (K * L)) psi)
          (.apply (.sum L) (.reindex (matPerm K L ((ir.value a).size / (K * L)))
            (.mul (.leaf a) (.reindex (bcastMap K (L * ((ir.value a).size / (K * L))))
              (.apply (.ntt ((ir.value a).size / (K * L)) psi .scheme) x)))))))
    else none
  | .adjoint n psi y x =>
    if 0 < n ∧ ir.exprLen y = n ∧ ir.exprLen x = n then
      some (.eq d (.apply (.sum n) (.mul (.apply (.nttTranspose n psi) y) x))
        (.apply (.sum n) (.mul y (.apply (.ntt n psi .natural) x))))
    else none
  | _ => none

end

variable {ir : RealizedProgram} {I : Interp}

/-- **The root facts of a transform check** (`rootOkB`, `root_facts`): in a field of
characteristic `p` decoding the naturals below `p` to their casts, `ψ` decodes to a primitive
`2n`-th root of unity, `n` is invertible and `n = 2^k`. -/
theorem rootOkB_facts {K : Type*} [Field K] {p n psi : ℕ} [CharP K p] {dec : ℕ → K}
    (hdec : ∀ c < p, dec c = (c : K)) (h : rootOkB p n psi = true) :
    IsPrimitiveRoot (dec psi) (2 * n) ∧ (n : K) ≠ 0 ∧ n = 2 ^ Nat.log2 n ∧ 0 < n ∧
      dec psi ^ n = -1 ∧ dec psi = (psi : K) := by
  unfold rootOkB at h
  obtain ⟨hp, hpsi, hn0, hnp, hk, hpow⟩ := of_decide_eq_true h
  have hd := hdec psi hpsi
  obtain ⟨hprim, hninv⟩ := root_facts (K := K) hp hpow hk hn0 hnp
  rw [hd]
  refine ⟨hprim, hninv, hk, hn0, ?_, rfl⟩
  rw [← Nat.cast_pow, CharP.natCast_eq_natCast_mod K p, hpow, Nat.cast_sub (by omega),
    CharP.cast_eq_zero, Nat.cast_one, zero_sub]

/-- **The size of a transform check lies below the characteristic.** -/
theorem rootOkB_lt {p n psi : ℕ} (h : rootOkB p n psi = true) : n < p := by
  unfold rootOkB at h
  exact (of_decide_eq_true h).2.2.2.1

/-- **A coordinate below `n · (L / n)` in block form**: `j / n * n + t` reads block `j / n` at
`t < n`, and `(j / n * n + t) / n = j / n`, `(j / n * n + t) % n = t`. -/
theorem block_index {n j t : ℕ} (ht : t < n) :
    (j / n * n + t) / n = j / n ∧ (j / n * n + t) % n = t := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

/-- **The inverse transform of a sum is the sum of the inverse transforms.** -/
theorem inverseNtt_sum {K : Type*} [Field K] {n L : ℕ} {ψ : K} (g : Fin L → ℕ → K) (r : ℕ) :
    ∑ l : Fin L, Ops.inverseNtt n ψ (g l) r =
      Ops.inverseNtt n ψ (fun m => ∑ l : Fin L, g l m) r := by
  unfold Ops.inverseNtt
  split_ifs
  · rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
  · simp

/-- **Entry `u` of the broadcast** is `u mod m`, below `K m`. -/
theorem entry_bcastMap {K m u : ℕ} (hu : u < K * m) : (bcastMap K m).entry u = u % m := by
  unfold bcastMap
  rw [IndexMap.entry_replicate hu]
  omega

/-- **Entry `(i n + s) L + l` of the grouping** is `(i L + l) n + s`. -/
theorem entry_matPerm {K L n i s l : ℕ} (hi : i < K) (hs : s < n) (hl : l < L) :
    (matPerm K L n).entry ((i * n + s) * L + l) = (i * L + l) * n + s := by
  have hn : 0 < n := by omega
  have hq : i * n + s < K * n := IndexMap.block_lt hi hs
  unfold matPerm
  rw [IndexMap.entry_flatMap_blocks _ L (K * n) (fun b _ => by simp) _
      (IndexMap.block_lt hq hl), (IndexMap.block_div_mod hl).1, (IndexMap.block_div_mod hl).2,
    IndexMap.entry_single hl, (IndexMap.block_div_mod hs).1, (IndexMap.block_div_mod hs).2]
  have : ((((i * (L * n) + s : ℕ) : ℤ) + (n : ℤ) * (l : ℤ))).toNat = (i * L + l) * n + s := by
    rw [show (((i * (L * n) + s : ℕ) : ℤ) + (n : ℤ) * (l : ℤ)) = (((i * L + l) * n + s : ℕ) : ℤ) by
      push_cast; ring]
    exact Int.toNat_natCast _
  exact this

/-- **`nttFact_sound`**: the transform instances are sound. -/
theorem nttFact_sound {primeNodes : ℕ → List String} (hwf : ir.WellFormed)
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {d : ℕ}
    {s : LinOpStep} {f : Fact} (hf : ir.nttFact d s = some f) : f.HoldsWith ir rd := by
  cases s with
  | nttInv n psi x =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hd, hr⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar := charP_field hI hfd
    obtain ⟨hprim, hninv, hk, hn0, -, -⟩ :=
      rootOkB_facts (dec := (I (ir.domainField d)).decode)
        (fun c hc => hL.decode_natCast _ hfd c hc) hr
    intro j hj
    simp only [exprLen_apply, NamedOp.rows, NamedOp.cols] at hj
    have hjn : j % n < n := Nat.mod_lt _ hn0
    simp only [evalWith, evalE_apply, NamedOp.apply, NamedOp.rows, NamedOp.cols, NamedOp.block]
    rw [Ops.inverseNtt_congr (y := Ops.nttScheme n ((I (ir.domainField d)).decode psi)
      (fun s => ir.evalE rd (ir.domainField d) x (j / n * n + s))) (fun t ht => by
        rw [(block_index (j := j) ht).1, (block_index (j := j) ht).2])]
    rw [Ops.inverseNtt_nttScheme hk hprim hninv _ hjn, Nat.div_add_mod']
  | inttInv n psi y =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hd, hr⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar := charP_field hI hfd
    obtain ⟨hprim, hninv, hk, hn0, -, -⟩ :=
      rootOkB_facts (dec := (I (ir.domainField d)).decode)
        (fun c hc => hL.decode_natCast _ hfd c hc) hr
    intro j hj
    have hjn : j % n < n := Nat.mod_lt _ hn0
    simp only [evalWith, evalE_apply, NamedOp.apply, NamedOp.rows, NamedOp.cols, NamedOp.block]
    rw [nttScheme_congr (y := Ops.inverseNtt n ((I (ir.domainField d)).decode psi)
      (fun s => ir.evalE rd (ir.domainField d) y (j / n * n + s))) (fun t ht => by
        rw [(block_index (j := j) ht).1, (block_index (j := j) ht).2])]
    rw [Ops.nttScheme_inverseNtt hk hprim hninv _ hjn, Nat.div_add_mod']
  | convNtt h psi x =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hd, hr, hlen⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar := charP_field hI hfd
    obtain ⟨hprim, hninv, hk, hn0, -, -⟩ :=
      rootOkB_facts (dec := (I (ir.domainField d)).decode)
        (fun c hc => hL.decode_natCast _ hfd c hc) hr
    intro j hj
    simp only [exprLen_apply, NamedOp.rows, NamedOp.cols, hlen,
      Nat.div_self hn0, Nat.one_mul] at hj
    have hj0 : j / (ir.value h).size = 0 := Nat.div_eq_of_lt hj
    have hjm : j % (ir.value h).size = j := Nat.mod_eq_of_lt hj
    simp only [evalWith, evalE_apply, NamedOp.apply, NamedOp.rows, NamedOp.cols, NamedOp.block,
      NamedOp.formPoly, hj0, hjm, Nat.zero_mul, Nat.zero_add, evalE_mul, evalE_leaf]
    rw [← Ops.inverseNtt_mul_nttScheme hk hprim hninv _ _ hj]
    refine Ops.inverseNtt_congr (fun t ht => ?_) j
    rw [Ops.nttScheme_inverseNtt hk hprim hninv _ ht]
    simp only [Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, Nat.zero_mul, Nat.zero_add]
  | convCoef h psi x =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hd, hr, hlen⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar := charP_field hI hfd
    obtain ⟨-, -, hk, hn0, hneg, -⟩ :=
      rootOkB_facts (dec := (I (ir.domainField d)).decode)
        (fun c hc => hL.decode_natCast _ hfd c hc) hr
    intro j hj
    simp only [exprLen_apply, NamedOp.rows, NamedOp.cols, hlen,
      Nat.div_self hn0, Nat.one_mul] at hj
    have hj0 : j / (ir.value h).size = 0 := Nat.div_eq_of_lt hj
    have hjm : j % (ir.value h).size = j := Nat.mod_eq_of_lt hj
    simp only [evalWith, evalE_apply, evalE_mul, NamedOp.apply, NamedOp.rows, NamedOp.cols,
      NamedOp.block, NamedOp.formPoly, hj0, hjm, Nat.zero_mul, Nat.zero_add]
    rw [nttScheme_congr (y := Ops.negacyclic (ir.value h).size
      (fun s => castElt (rd h s)) (fun s => ir.evalE rd (ir.domainField d) x s)) (fun t ht => by
        simp only [Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, Nat.zero_mul, Nat.zero_add])]
    rw [Ops.nttScheme_negacyclic hk hneg _ _ hj]
    rfl
  | transposeInv n psi psi' x =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hd, hr, hpp, hinv⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar := charP_field hI hfd
    obtain ⟨hprim, hninv, -, hn0, -, hdpsi⟩ :=
      rootOkB_facts (dec := (I (ir.domainField d)).decode)
        (fun c hc => hL.decode_natCast _ hfd c hc) hr
    have hnp := rootOkB_lt hr
    have hdpsi' := hL.decode_natCast _ hfd psi' hpp
    have hdn := hL.decode_natCast _ hfd n hnp
    set ψ := (I (ir.domainField d)).decode psi with hψ
    have hψ0 : ψ ≠ 0 := hprim.ne_zero (by omega)
    have hψinv : (I (ir.domainField d)).decode psi' = ψ⁻¹ := by
      rw [hdpsi']
      refine (eq_inv_of_mul_eq_one_right ?_)
      rw [hdpsi, ← Nat.cast_mul, CharP.natCast_eq_natCast_mod _ (ir.charOf (ir.domainField d)),
        hinv, Nat.cast_one]
    have hω : IsPrimitiveRoot (ψ ^ 2) n := DFT.IsPrimitiveRoot.sq_of_two_mul hprim (by omega)
    have hsplit : ∀ b c : ℕ, ψ ^ ((2 * b + 1) * c) = ψ ^ c * (ψ ^ 2) ^ (c * b) := fun b c => by
      rw [← pow_mul, ← pow_add]
      ring_nf
    have hsplit' : ∀ b c : ℕ, ψ⁻¹ ^ ((2 * b + 1) * c) = ψ⁻¹ ^ c * (ψ ^ 2)⁻¹ ^ (b * c) :=
      fun b c => by
        rw [← inv_pow ψ 2, ← pow_mul, ← pow_add]
        ring_nf
    intro j hj
    simp only [exprLen_apply, NamedOp.rows, NamedOp.cols] at hj
    have hi : j % n < n := Nat.mod_lt _ hn0
    simp only [evalWith, evalE_apply, NamedOp.apply, NamedOp.rows, NamedOp.cols, NamedOp.block,
      Ops.nttTranspose, if_pos hi, hψinv]
    have hY : ∀ m : Fin n, Ops.nttNatural n ψ (fun s => ir.evalE rd (ir.domainField d) x
        ((j / n * n + m) / n * n + s)) ((j / n * n + m) % n) =
          ∑ k : Fin n, ir.evalE rd (ir.domainField d) x (j / n * n + k) *
            ψ ^ ((2 * (m : ℕ) + 1) * (k : ℕ)) :=
      fun m => by
        rw [(block_index (j := j) m.isLt).1, (block_index (j := j) m.isLt).2,
          Ops.nttNatural_apply _ _ _ m.isLt]
    simp only [← hψ, hY, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ k : Fin n, ∑ m : Fin n, ψ⁻¹ ^ ((2 * (m : ℕ) + 1) * (j % n)) *
        (ir.evalE rd (ir.domainField d) x (j / n * n + k) * ψ ^ ((2 * (m : ℕ) + 1) * (k : ℕ))) =
          ir.evalE rd (ir.domainField d) x (j / n * n + k) * (ψ ^ (k : ℕ) * ψ⁻¹ ^ (j % n)) *
            ∑ m : Fin n, (ψ ^ 2) ^ ((k : ℕ) * m) * (ψ ^ 2)⁻¹ ^ ((m : ℕ) * (j % n)) := by
      intro k
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hsplit, hsplit']
      ring
    simp only [hterm]
    have horth := fun k : Fin n => DFT.sum_pow_mul_inv_pow_eq hω k ⟨j % n, hi⟩
    simp only at horth
    simp only [horth, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (⟨j % n, hi⟩ : Fin n), if_pos (Finset.mem_univ _)]
    simp only
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hψ0), mul_one, Nat.div_add_mod']
    simp only [evalE_scale_const, hdn]
    ring
  | convBcastNtt t K psi x =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hd, hr, hsz, hlen⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar := charP_field hI hfd
    obtain ⟨hprim, hninv, hk, hn0, -, -⟩ :=
      rootOkB_facts (dec := (I (ir.domainField d)).decode)
        (fun c hc => hL.decode_natCast _ hfd c hc) hr
    intro j hj
    simp only [exprLen_apply, NamedOp.rows, NamedOp.cols, hlen, Nat.div_self hn0,
      Nat.one_mul] at hj
    have hjK : j < K * ((ir.value t).size / K) := by rw [← hsz]; exact hj
    have hj0 : j / (ir.value t).size = 0 := Nat.div_eq_of_lt hj
    have hjm : j % (ir.value t).size = j := Nat.mod_eq_of_lt hj
    have hjn : j % ((ir.value t).size / K) < (ir.value t).size / K := Nat.mod_lt _ hn0
    simp only [evalWith, evalE_apply, evalE_mul, evalE_leaf, evalE_reindex, NamedOp.apply,
      NamedOp.rows, NamedOp.cols, NamedOp.block, NamedOp.formPoly, hj0, hjm, Nat.zero_mul,
      Nat.zero_add, if_pos hjK]
    rw [← Ops.inverseNtt_mul_nttScheme hk hprim hninv _ _ hjn]
    refine Ops.inverseNtt_congr (fun u hu => ?_) _
    rw [Ops.nttScheme_inverseNtt hk hprim hninv _ hu]
    have hlt : j / ((ir.value t).size / K) * ((ir.value t).size / K) + u <
        K * ((ir.value t).size / K) :=
      IndexMap.block_lt ((Nat.div_lt_iff_lt_mul hn0).2 hjK) hu
    rw [entry_bcastMap hlt, (block_index (j := j) hu).2, Nat.div_eq_of_lt hu, Nat.mod_eq_of_lt hu]
    simp only [Nat.zero_mul, Nat.zero_add]
  | convMatNtt a K L psi x =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hd, hr, hsz, hL0, hlen⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar := charP_field hI hfd
    obtain ⟨hprim, hninv, hk, hn0, -, -⟩ :=
      rootOkB_facts (dec := (I (ir.domainField d)).decode)
        (fun c hc => hL.decode_natCast _ hfd c hc) hr
    set n := (ir.value a).size / (K * L) with hn
    have hLn : 0 < L * n := Nat.mul_pos hL0 hn0
    intro j hj
    simp only [exprLen_apply, NamedOp.rows, NamedOp.cols, hlen, ← hn, Nat.div_self hLn,
      Nat.one_mul] at hj
    have hj0 : j / (K * n) = 0 := Nat.div_eq_of_lt hj
    have hjm : j % (K * n) = j := Nat.mod_eq_of_lt hj
    have hjn : j % n < n := Nat.mod_lt _ hn0
    have hi : j / n < K := (Nat.div_lt_iff_lt_mul hn0).2 hj
    simp only [evalWith, evalE_apply, NamedOp.apply, NamedOp.rows, NamedOp.cols, NamedOp.block,
      NamedOp.formPoly, ← hn, hj0, hjm, Nat.zero_mul, Nat.zero_add, if_pos hj]
    have hterm : ∀ l : Fin L, Ops.negacyclic n
        (Ops.inverseNtt n ((I (ir.domainField d)).decode psi)
          fun s => castElt (rd a ((j / n * L + l) * n + s)))
        (fun s => ir.evalE rd (ir.domainField d) x (l * n + s)) (j % n) =
          Ops.inverseNtt n ((I (ir.domainField d)).decode psi)
            (fun m => castElt (rd a ((j / n * L + l) * n + m)) *
              Ops.nttScheme n ((I (ir.domainField d)).decode psi)
                (fun s => ir.evalE rd (ir.domainField d) x (l * n + s)) m) (j % n) := fun l => by
      rw [← Ops.inverseNtt_mul_nttScheme hk hprim hninv _ _ hjn]
      exact Ops.inverseNtt_congr
        (fun u hu => by rw [Ops.nttScheme_inverseNtt hk hprim hninv _ hu]) _
    rw [Finset.sum_congr rfl fun l _ => hterm l, inverseNtt_sum]
    refine Ops.inverseNtt_congr (fun u hu => ?_) _
    simp only [Ops.sum, Nat.div_one, Nat.mod_one, ite_true]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hq := (block_index (j := j) hu)
    simp only [evalE_reindex, evalE_mul, evalE_leaf, evalE_apply, NamedOp.apply, NamedOp.rows,
      NamedOp.cols, NamedOp.block]
    rw [entry_matPerm hi hu l.isLt]
    have hlt : (j / n * L + l) * n + u < K * (L * n) := by
      have := IndexMap.block_lt (IndexMap.block_lt hi l.isLt) hu
      rw [show K * (L * n) = K * L * n by ring]
      exact this
    rw [entry_bcastMap hlt]
    have hmod : ((j / n * L + l) * n + u) % (L * n) = l * n + u := by
      rw [show (j / n * L + l) * n + u = j / n * (L * n) + (l * n + u) by ring,
        Nat.add_comm, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (IndexMap.block_lt l.isLt hu)]
    rw [hmod, (IndexMap.block_div_mod (q := l) hu).1, (IndexMap.block_div_mod (q := l) hu).2]
  | adjoint n psi y x =>
    simp only [nttFact] at hf
    split_ifs at hf with hc
    cases hf
    obtain ⟨hn0, hy, hx⟩ := hc
    intro j hj
    simp only [exprLen_apply, exprLen_mul, NamedOp.rows, NamedOp.cols, hy,
      Nat.div_self hn0, Nat.one_mul] at hj
    obtain rfl : j = 0 := by omega
    simp only [evalWith, evalE_mul, evalE_apply, NamedOp.apply, NamedOp.rows,
      NamedOp.cols, NamedOp.block, Ops.sum, Nat.zero_div, Nat.div_one, Nat.mod_one, ite_true,
      Nat.zero_mul, Nat.zero_add]
    have hT : ∀ t : Fin n, Ops.nttTranspose n ((I (ir.domainField d)).decode psi)
        (fun s => ir.evalE rd (ir.domainField d) y ((t : ℕ) / n * n + s)) ((t : ℕ) % n) =
          ∑ m : Fin n, ((I (ir.domainField d)).decode psi) ^ ((2 * (m : ℕ) + 1) * t) *
            ir.evalE rd (ir.domainField d) y m := fun t => by
      rw [Nat.div_eq_of_lt t.isLt, Nat.mod_eq_of_lt t.isLt, Ops.nttTranspose, if_pos t.isLt]
      simp only [Nat.zero_mul, Nat.zero_add]
    have hN : ∀ t : Fin n, Ops.nttNatural n ((I (ir.domainField d)).decode psi)
        (fun s => ir.evalE rd (ir.domainField d) x ((t : ℕ) / n * n + s)) ((t : ℕ) % n) =
          ∑ i : Fin n, ir.evalE rd (ir.domainField d) x i *
            ((I (ir.domainField d)).decode psi) ^ ((2 * (t : ℕ) + 1) * i) := fun t => by
      rw [Nat.div_eq_of_lt t.isLt, Nat.mod_eq_of_lt t.isLt, Ops.nttNatural_apply _ _ _ t.isLt]
      simp only [Nat.zero_mul, Nat.zero_add]
    simp only [hT, hN, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun t _ => by ring
  | congr k e => simp [nttFact] at hf
  | rows op x R N => simp [nttFact] at hf
  | spectral c k => simp [nttFact] at hf

end GordieHowe.RealizedProgram
