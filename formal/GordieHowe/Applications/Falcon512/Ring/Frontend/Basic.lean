-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Norm
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Composite

@[expose] public section

/-!
# GordieHowe frontend: the native Falcon ring, the relation and the extractor

The frontend of the theorem at the realized program for the native Falcon rings (`Falcon512.Ring.Native.ROMParams` and
`Falcon512.Ring.Native.QROMParams`, export `b65a4929`), generic in the program and its interpretation at the
program facts `FalconRingPowers`, `FalconRingSelect` and `FalconRingBase` (decided per program;
the two programs agree on every source value, shared expression and predicate):

* **The challenge powers** (`powers_eval`): shared expressions `0 … 15` square and concatenate the
  challenge `γ` (`member.ring.gamma`, value `8`) into `γ^0, …, γ^511` (`member.ring.powers`).
* **The selection** (`select_top`): shared expressions `16 … 20` and `member.signer`'s multiplexer
  select, by the index bits, the digest at the signer's position (`idxOf`).
* **The digests** (`digests_eval`): the digest of key `r` is the fingerprint
  `Σ_m γ^m · NTT(h_r)_m` of its natural-order transform at `ψ = 10302`.
* **The membership** (`member_eq`, `ringEvent`, `ringEvent_bound`, `spec_eq_of_not_event`): the
  committed spectrum's fingerprint is the signer's key's; unless `γ` is a root of the nonzero
  difference polynomial (degree at most `511`, probability `511/|F|`, Schwartz–Zippel), the spectrum
  is the transform of the signer's key.
* **The signature equation** (`sig_eq`): `Ntt(c − s1) = spectrum ⊙ Ntt(s2)`.
* **The relation and the extractor** (`rel`, `proj`, `extractor`): the signer's position is below
  `64` and, at its key (`ringKey`) and the statement's challenge (`chalNat`), Falcon's algebraic
  verifier accepts the extracted `s2` and `s2` is encodable; `proj` reads the index bits and the
  centred `s2`. `mem_rel_of_source`: the spectral equation is `c − s1 = h · s2` over the field, its
  projection onto the prime field (`primeProj`) the ring algebra at the signer's key, and
  `GordieHowe.Falcon512.Ring.Native.ringAlgebra_sound` gives the relation, given the norm's advice (`NormSound`,
  discharged per program by the generic norm `FalconNorm`).
* **Round-by-round knowledge soundness of `Π_P₀`** (`rbr_of_norm`): `GordieHowe.RealizedProgram.rbr_of_events` at the
  membership's event, error `511/|F|` at `member.ring.gamma` (`ringEps`).
-/

namespace GordieHowe.Falcon512.Ring

open GordieHowe.Bits IOP
open scoped NNReal ENNReal

/-! ## The challenge powers -/

/-- **The shared expressions of the challenge powers** (decided per program): `0` is `(1, γ)`, `1`
is `γ²`, `2 m` concatenates `2 m − 2` with its products by `2 m − 1` (`m = 1 … 7`), `2 m + 1`
squares `2 m − 1` (`m = 1 … 6`), and `15` is `14`'s products by `γ^256`. -/
class FalconRingPowers (program : RealizedProgram) where
  /-- The constant `1`. -/
  one : ℕ
  /-- The challenge `γ` (`member.ring.gamma`). -/
  gamma : ℕ
  /-- The program's shared expressions read only earlier entries. -/
  refsOrdered : program.RefsOrdered
  /-- The powers' shared expressions are in the table. -/
  exprs_length : 15 < program.exprs.length
  /-- `(1, γ)`. -/
  expr0 : program.expr 0 = .reindex [(0, 1, 2)] (.concat (.leaf one) (.mul (.leaf gamma) (.leaf one)))
  /-- `γ²`. -/
  expr1 : program.expr 1 = .mul (.leaf gamma) (.leaf gamma)
  /-- The concatenations. -/
  exprEven : ∀ m ∈ List.range' 1 7, program.expr (2 * m) = .reindex [(0, 1, 2 ^ (m + 1))]
    (.concat (.ref (2 * m - 2)) (.mul (.reindex [(0, 0, 2 ^ m)] (.ref (2 * m - 1)))
      (.ref (2 * m - 2))))
  /-- The squares. -/
  exprOdd : ∀ m ∈ List.range' 1 6,
    program.expr (2 * m + 1) = .mul (.ref (2 * m - 1)) (.ref (2 * m - 1))
  /-- The upper half. -/
  expr15 : program.expr 15 = .mul (.reindex [(0, 0, 256)] (.mul (.ref 13) (.ref 13))) (.ref 14)
  /-- The constant `1` has one coordinate. -/
  size0 : (program.value one).size = 1

section Powers

variable {program : RealizedProgram} [FalconRingPowers program] {I : RealizedProgram.Interp}
  (rd : program.Valuation I) (f : ℕ)

theorem evalE_refP {k : ℕ} (hk : k ≤ 15) :
    program.evalE rd f (.ref k) = program.evalE rd f (program.expr k) :=
  RealizedProgram.evalE_ref FalconRingPowers.refsOrdered rd f
    (lt_of_le_of_lt hk FalconRingPowers.exprs_length)

theorem exprLen_refP {k : ℕ} (hk : k ≤ 15) :
    program.exprLen (.ref k) = program.exprLen (program.expr k) :=
  RealizedProgram.exprLen_ref FalconRingPowers.refsOrdered (lt_of_le_of_lt hk FalconRingPowers.exprs_length)

variable {rd f} {γ : (I f).K}

/-- **The powers' levels** (`m ≤ 7`): shared expression `2 m` has `2^(m+1)` coordinates, the
powers `γ^k`, and shared expression `2 m + 1` (for `m ≤ 6`) reads `γ^(2^(m+1))` at coordinate
`0`. -/
theorem powers_level (h1 : program.evalE rd f (.leaf (FalconRingPowers.one program)) 0 = 1)
    (hγ : program.evalE rd f (.leaf (FalconRingPowers.gamma program)) 0 = γ) :
    ∀ m ≤ 7, program.exprLen (.ref (2 * m)) = 2 ^ (m + 1) ∧
      (∀ k < 2 ^ (m + 1), program.evalE rd f (.ref (2 * m)) k = γ ^ k) ∧
      (m ≤ 6 → program.evalE rd f (.ref (2 * m + 1)) 0 = γ ^ 2 ^ (m + 1))
  | 0, _ => by
    refine ⟨?_, fun k hk => ?_, fun _ => ?_⟩
    · rw [exprLen_refP (by norm_num), FalconRingPowers.expr0, RealizedProgram.exprLen_reindex]
      rfl
    · rw [evalE_refP rd f (by norm_num), FalconRingPowers.expr0, RealizedProgram.evalE_reindex,
        RealizedProgram.IndexMap.entry_step_one (show k < 2 by simpa using hk), Nat.zero_add,
        RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf, FalconRingPowers.size0, RealizedProgram.evalE_mul]
      have hk2 : k < 2 := by simpa using hk
      interval_cases k
      · simp [h1]
      · simp [h1, hγ]
    · rw [evalE_refP rd f (by norm_num), FalconRingPowers.expr1, RealizedProgram.evalE_mul, hγ]
      ring
  | m + 1, hm => by
    obtain ⟨hlen, hval, hodd⟩ := powers_level h1 hγ m (by omega)
    have hE := FalconRingPowers.exprEven (program := program) (m + 1)
      (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
    have h3 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [h2, h3] at hE
    refine ⟨?_, fun k hk => ?_, fun hm6 => ?_⟩
    · rw [exprLen_refP (by omega), hE, RealizedProgram.exprLen_reindex]
      simp
    · rw [evalE_refP rd f (by omega), hE, RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_one hk,
        Nat.zero_add, RealizedProgram.evalE_concat, hlen]
      split_ifs with hk'
      · exact hval k hk'
      · rw [RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex,
          RealizedProgram.IndexMap.entry_step_zero (show k - 2 ^ (m + 1) < 2 ^ (m + 1) by
            rw [pow_succ] at hk; omega),
          hodd (by omega), hval _ (by rw [pow_succ] at hk; omega), ← pow_add]
        congr 1
        omega
    · have hO := FalconRingPowers.exprOdd (program := program) (m + 1)
        (List.mem_range'_1.2 ⟨by omega, by omega⟩)
      rw [h3] at hO
      rw [evalE_refP rd f (by omega), hO, RealizedProgram.evalE_mul, hodd (by omega), ← pow_add,
        ← two_mul, pow_succ 2 (m + 1)]
      ring

/-- **The upper half of the powers**: shared expression `15` reads `γ^(256 + k)` at `k < 256`. -/
theorem powers_upper (h1 : program.evalE rd f (.leaf (FalconRingPowers.one program)) 0 = 1)
    (hγ : program.evalE rd f (.leaf (FalconRingPowers.gamma program)) 0 = γ) {k : ℕ} (hk : k < 256) :
    program.evalE rd f (.ref 15) k = γ ^ (256 + k) := by
  obtain ⟨-, h13v, h13⟩ := powers_level h1 hγ 6 (by norm_num)
  obtain ⟨-, h14v, -⟩ := powers_level h1 hγ 7 (by norm_num)
  rw [evalE_refP rd f (by norm_num), FalconRingPowers.expr15, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_zero hk, RealizedProgram.evalE_mul, h13 (by norm_num),
    h14v k (by omega), ← pow_add, ← pow_add]
  norm_num

/-- **The powers**: the concatenation of shared expressions `14` and `15` reads `γ^k` at
`k < 512`. -/
theorem powers_eval (h1 : program.evalE rd f (.leaf (FalconRingPowers.one program)) 0 = 1)
    (hγ : program.evalE rd f (.leaf (FalconRingPowers.gamma program)) 0 = γ) {k : ℕ} (hk : k < 512) :
    program.evalE rd f (.concat (.ref 14) (.ref 15)) k = γ ^ k := by
  obtain ⟨hlen, h14v, -⟩ := powers_level h1 hγ 7 (by norm_num)
  rw [RealizedProgram.evalE_concat, hlen, show 2 ^ (7 + 1) = 256 by norm_num]
  split_ifs with h
  · exact h14v k (by omega)
  · rw [powers_upper h1 hγ (by omega), show 256 + (k - 256) = k by omega]

end Powers

/-! ## The selection of the signer's digest -/

/-- **The shared expressions of the selection** (decided per program): `16 + t` (`t = 0 … 4`)
selects, by bit `t` of the signer's index (value `7`), the odd or the even entries of `15 + t`
(of the digests, value `21`, for `t = 0`). -/
class FalconRingSelect (program : RealizedProgram) where
  /-- The index bits (`member.signer.index`). -/
  idx : ℕ
  /-- The digests (`member.ring.digests`). -/
  dig : ℕ
  /-- The program's shared expressions read only earlier entries. -/
  refsOrdered : program.RefsOrdered
  /-- The selection's shared expressions are in the table. -/
  exprs_length : 20 < program.exprs.length
  /-- The first level, on the digests. -/
  expr16 : program.expr 16 = .mux (.reindex [(0, 0, 32)] (.reindex [(0, 0, 1)] (.leaf idx)))
    (.reindex [(1, 2, 32)] (.leaf dig)) (.reindex [(0, 2, 32)] (.leaf dig))
  /-- The later levels. -/
  exprSel : ∀ t ∈ List.range' 1 4, program.expr (16 + t) =
    .mux (.reindex [(0, 0, 2 ^ (5 - t))] (.reindex [(t, 0, 1)] (.leaf idx)))
      (.reindex [(1, 2, 2 ^ (5 - t))] (.ref (15 + t))) (.reindex [(0, 2, 2 ^ (5 - t))] (.ref (15 + t)))

/-- **A multiplexer on a bit** selects its first operand at `1`, its second at `0`. -/
theorem mux_bit {K : Type*} [Field K] {b : ℕ} (hb : b ≤ 1) (x y : K) :
    (b : K) * x + (1 - (b : K)) * y = if b = 1 then x else y := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> simp

/-- **The low bits of an index**: `Σ_{i ≤ t} b_i 2^i`. -/
def lowBits (b : ℕ → ℕ) (t : ℕ) : ℕ := ∑ i ∈ Finset.range (t + 1), b i * 2 ^ i

theorem lowBits_succ (b : ℕ → ℕ) (t : ℕ) :
    lowBits b (t + 1) = lowBits b t + b (t + 1) * 2 ^ (t + 1) := by
  unfold lowBits
  rw [Finset.sum_range_succ]

theorem lowBits_lt {b : ℕ → ℕ} (hb : ∀ i, b i ≤ 1) : ∀ t, lowBits b t < 2 ^ (t + 1)
  | 0 => by simp [lowBits]; have := hb 0; omega
  | t + 1 => by
    rw [lowBits_succ, pow_succ 2 (t + 1)]
    have := lowBits_lt hb t
    have := hb (t + 1)
    nlinarith

section Select

variable {program : RealizedProgram} [FalconRingSelect program] {I : RealizedProgram.Interp}
  {rd : program.Valuation I} {f : ℕ} {b : ℕ → ℕ} {D : ℕ → (I f).K}

theorem evalE_refS (rd : program.Valuation I) (f : ℕ) {k : ℕ} (hk : k ≤ 20) :
    program.evalE rd f (.ref k) = program.evalE rd f (program.expr k) :=
  RealizedProgram.evalE_ref FalconRingSelect.refsOrdered rd f
    (lt_of_le_of_lt hk FalconRingSelect.exprs_length)

/-- **The selection's levels** (`t ≤ 4`): entry `j < 2^(5 − t)` of shared expression `16 + t` is
digest `2^(t+1) j + Σ_{i ≤ t} b_i 2^i`, at bits `b` of the index and digests `D`. -/
theorem select_level (hb : ∀ i, b i ≤ 1)
    (hbit : ∀ i < 6, program.evalE rd f (.leaf (FalconRingSelect.idx program)) i = (b i : (I f).K))
    (hD : ∀ r < 64, program.evalE rd f (.leaf (FalconRingSelect.dig program)) r = D r) :
    ∀ t ≤ 4, ∀ j < 2 ^ (5 - t),
      program.evalE rd f (.ref (16 + t)) j = D (2 ^ (t + 1) * j + lowBits b t)
  | 0, _, j, hj => by
    rw [evalE_refS rd f (by norm_num), FalconRingSelect.expr16, RealizedProgram.evalE_mux,
      RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
      RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_zero (show j < 32 by simpa using hj),
      RealizedProgram.IndexMap.entry_step_zero (show 0 < 1 by norm_num), hbit 0 (by norm_num),
      mux_bit (hb 0), RealizedProgram.IndexMap.entry_single (show j < 32 by simpa using hj),
      RealizedProgram.IndexMap.entry_single (show j < 32 by simpa using hj)]
    have h1 : (((1 : ℕ) : ℤ) + 2 * (j : ℤ)).toNat = 2 * j + 1 := by omega
    have h0 : (((0 : ℕ) : ℤ) + 2 * (j : ℤ)).toNat = 2 * j := by omega
    rw [h1, h0, hD _ (by simp at hj; omega), hD _ (by simp at hj; omega)]
    simp only [lowBits, Finset.sum_range_one, pow_zero, mul_one, zero_add, pow_one]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hb 0) with h | h <;> simp [h]
  | t + 1, ht, j, hj => by
    have hE := FalconRingSelect.exprSel (program := program) (t + 1)
      (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    rw [show 15 + (t + 1) = 16 + t by omega] at hE
    have hj' : j < 2 ^ (5 - (t + 1)) := hj
    have h2 : 2 ^ (5 - t) = 2 * 2 ^ (5 - (t + 1)) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [evalE_refS rd f (by omega), hE, RealizedProgram.evalE_mux, RealizedProgram.evalE_reindex,
      RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
      RealizedProgram.IndexMap.entry_step_zero hj', RealizedProgram.IndexMap.entry_step_zero (show 0 < 1 by norm_num),
      Nat.add_zero, hbit (t + 1) (by omega), mux_bit (hb (t + 1)), RealizedProgram.IndexMap.entry_single hj',
      RealizedProgram.IndexMap.entry_single hj']
    have h1 : (((1 : ℕ) : ℤ) + 2 * (j : ℤ)).toNat = 2 * j + 1 := by omega
    have h0 : (((0 : ℕ) : ℤ) + 2 * (j : ℤ)).toNat = 2 * j := by omega
    rw [h1, h0, select_level hb hbit hD t (by omega) _ (by rw [h2]; omega),
      select_level hb hbit hD t (by omega) _ (by rw [h2]; omega), lowBits_succ]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hb (t + 1)) with h | h
    · simp only [h, zero_ne_one, if_false, zero_mul, add_zero]
      congr 1
      rw [pow_succ 2 (t + 1)]
      ring
    · simp only [h, if_true, one_mul]
      congr 1
      rw [pow_succ 2 (t + 1)]
      ring

/-- **The selected digest**: the selection by bit `5` of shared expression `20`'s two entries is
digest `Σ_{i < 6} b_i 2^i`. -/
theorem select_top (hb : ∀ i, b i ≤ 1)
    (hbit : ∀ i < 6, program.evalE rd f (.leaf (FalconRingSelect.idx program)) i = (b i : (I f).K))
    (hD : ∀ r < 64, program.evalE rd f (.leaf (FalconRingSelect.dig program)) r = D r) :
    program.evalE rd f (.mux (.reindex [(5, 0, 1)] (.leaf (FalconRingSelect.idx program)))
      (.reindex [(1, 0, 1)] (.ref 20))
      (.reindex [(0, 0, 1)] (.ref 20))) 0 = D (lowBits b 5) := by
  rw [RealizedProgram.evalE_mux, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_step_zero (show 0 < 1 by norm_num), RealizedProgram.IndexMap.entry_step_zero (show 0 < 1 by norm_num),
    RealizedProgram.IndexMap.entry_step_zero (show 0 < 1 by norm_num), hbit 5 (by norm_num), mux_bit (hb 5),
    select_level hb hbit hD 4 (by norm_num) 1 (by norm_num),
    select_level hb hbit hD 4 (by norm_num) 0 (by norm_num)]
  have h5 : lowBits b 5 = lowBits b 4 + b 5 * 32 := lowBits_succ b 4
  rw [h5]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hb 5) with h | h
  · simp [h]
  · simp only [h, if_true]
    congr 1
    norm_num <;> omega

end Select

/-! ## The digests -/

/-- **The digests' expression** (`member.ring.digests`, value `21`): the rows of the ring
(value `4`, `64` keys of `512` coefficients) against the transposed natural-order transform of the
challenge powers. -/
def digestsExpr (ring psi : ℕ) : RealizedProgram.Expr :=
  .apply (.rowDot ring 64 512) (.reindex [(0, 1, 512)] (.apply (.nttTranspose 512 psi)
    (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.concat (.ref 14) (.ref 15))))))

section Digests

variable {program : RealizedProgram} [FalconRingPowers program] {I : RealizedProgram.Interp}
  {rd : program.Valuation I} {f : ℕ} {γ : (I f).K}

/-- **The digest of key `r`** is the fingerprint `Σ_m γ^m · NTT(h_r)_m` of its natural-order
transform at `ψ` (`Ops.nttNatural`), `h_r` the ring's row `r`. -/
theorem digests_eval {ring psi : ℕ} (h1 : program.evalE rd f (.leaf (FalconRingPowers.one program)) 0 = 1)
    (hγ : program.evalE rd f (.leaf (FalconRingPowers.gamma program)) 0 = γ) {r : ℕ} (hr : r < 64) :
    program.evalE rd f (digestsExpr ring psi) r = ∑ m : Fin 512, γ ^ (m : ℕ) *
      RealizedProgram.Ops.nttNatural 512 ((I f).decode psi) (fun c => program.evalE rd f (.leaf ring) (r * 512 + c))
        m := by
  have hp : ∀ m < 512, program.evalE rd f (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)]
      (.concat (.ref 14) (.ref 15)))) m = γ ^ m := fun m hm => by
    rw [RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_one hm, Nat.zero_add,
      RealizedProgram.IndexMap.entry_step_one hm, Nat.zero_add]
    exact powers_eval h1 hγ hm
  have ht : ∀ c < 512, program.evalE rd f (.reindex [(0, 1, 512)] (.apply (.nttTranspose 512 psi)
      (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.concat (.ref 14) (.ref 15)))))) c =
      ∑ m : Fin 512, (I f).decode psi ^ ((2 * (m : ℕ) + 1) * c) * γ ^ (m : ℕ) := fun c hc => by
    rw [RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_one hc, Nat.zero_add, RealizedProgram.evalE_apply]
    simp only [RealizedProgram.NamedOp.apply, RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.Ops.nttTranspose,
      Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc, zero_mul, zero_add, if_pos hc]
    exact Finset.sum_congr rfl fun m _ => by rw [hp m m.isLt]
  unfold digestsExpr
  rw [RealizedProgram.evalE_apply]
  simp only [RealizedProgram.NamedOp.apply, RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.Ops.rowDot,
    Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr, zero_mul, zero_add, if_pos hr]
  simp only [fun c : Fin 512 => ht c c.isLt]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [RealizedProgram.Ops.nttNatural_apply _ _ _ m.isLt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [RealizedProgram.evalE_leaf]
  ring

end Digests

/-! ## The membership -/

/-- **The membership's left side** (`member.signer`): `Σ_k spectrum_k γ^k` less the digest the
index bits select, at the spectrum `spec`, the powers `pow`, the index bits `idx` and the constant
`−1` (`mOne`). -/
def memberLhs (spec pow idx mOne : ℕ) : RealizedProgram.Expr :=
  .add (.apply (.sum 512) (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf spec)))
    (.reindex [(0, 1, 512)] (.leaf pow))))
    (.scale (.const mOne) (.mux (.reindex [(5, 0, 1)] (.leaf idx)) (.reindex [(1, 0, 1)] (.ref 20))
      (.reindex [(0, 0, 1)] (.ref 20))))

/-- **The signature equation's left side** (`signature.equation`) of a native ring:
`Ntt(c − s1) − spectrum ⊙ Ntt(s2)`. -/
def sigLhs : RealizedProgram.Expr :=
  .add (.apply (.ntt 512 10302 .natural) (.add (.leaf 5) (.scale (.const 12288) (.leaf 10))))
    (.scale (.const 12288) (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf 6)))
      (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.apply (.ntt 512 10302 .natural)
        (.leaf 9))))))

/-- **The field facts the membership reads** in a field interpretation: the constant `negOne`
decodes to `−1`, `0` and `1` decode to themselves and read back as `0` and `1`. -/
class RingField (FA : RealizedProgram.FieldInterp) (negOne : ℕ) : Prop where
  /-- `negOne` decodes to `−1`. -/
  decode_negOne : FA.decode negOne = -1
  /-- `0` decodes to `0`. -/
  decode_zero : FA.decode 0 = 0
  /-- `1` decodes to `1`. -/
  decode_one : FA.decode 1 = 1
  /-- `0` reads as `0`. -/
  toNat_zero : FA.toNat 0 = 0
  /-- `1` reads as `1`. -/
  toNat_one : FA.toNat 1 = 1

/-- **A native Falcon field** (`F_q^k`): `q − 1 = 12288` is `−1`. -/
instance (FA : RealizedProgram.FieldInterp) [AField FA] : RingField FA 12288 where
  decode_negOne := by
    rw [AField.decode_eq]
    have h0 : ((12289 : ℕ) : FA.K) = 0 := CharP.cast_eq_zero _ 12289
    push_cast at h0 ⊢
    linear_combination h0
  decode_zero := by rw [AField.decode_eq, Nat.cast_zero]
  decode_one := by rw [AField.decode_eq, Nat.cast_one]
  toNat_zero := AField.toNat_zero
  toNat_one := AField.toNat_one

/-- **The program facts of a Falcon ring's membership** (decided per program; the native rings and
the carrier rings number their values differently): domain `0` of field `0`; the ring
(`statement.ring`, `ring`), the spectrum (`spec`), the powers (`pow`), the zero constant (`zero`),
the transform root (`psi`) and the constant `−1` (`mOne`) of the field; the membership
`member.signer` (predicate `0`) and the index bits' type check (`idxPred`), source predicates; the
powers and the digests as public expressions; the kinds, fields and sizes of the values read; the
challenge `γ`. -/
class FalconRingMember (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
    where
  /-- `statement.ring`. -/
  ring : ℕ
  /-- `key.spectrum`. -/
  spec : ℕ
  /-- `member.ring.powers`. -/
  pow : ℕ
  /-- The zero constant of one coordinate. -/
  zero : ℕ
  /-- The transform root. -/
  psi : ℕ
  /-- The constant `−1` of the field. -/
  mOne : ℕ
  /-- `member.signer.index.boolean`. -/
  idxPred : ℕ
  /-- `statement.c`. -/
  chal : ℕ
  /-- `s2`. -/
  s2 : ℕ
  /-- Domain `0` has field `0`. -/
  domainField0 : program.domainField 0 = 0
  /-- `member.signer`: `Σ_k spectrum_k γ^k` is the selected digest. -/
  member : ∃ t, (program.predicate 0).body =
    .equal 0 (memberLhs spec pow (FalconRingSelect.idx program) mOne) (.leaf zero) t
  /-- `member.signer.index.boolean`. -/
  idxBool : ∃ t, (program.predicate idxPred).body = .equal 0
    (.mul (.leaf (FalconRingSelect.idx program)) (.leaf (FalconRingSelect.idx program)))
    (.leaf (FalconRingSelect.idx program)) t
  /-- The two predicates are source predicates. -/
  inSource : ∀ p ∈ [0, idxPred],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The challenge powers. -/
  powersKind : (program.value pow).kind =
    .pub (.expr (.reindex [(0, 1, 512)] (.concat (.ref 14) (.ref 15))))
  /-- The digests. -/
  digestsKind : (program.value (FalconRingSelect.dig program)).kind = .pub (.expr (digestsExpr ring psi))
  /-- The constants `1` and `0`. -/
  consts : program.isConstant (FalconRingPowers.one program) = true ∧
    (program.constEntries (FalconRingPowers.one program)).getD 0 0 = 1 ∧
    program.isConstant zero = true ∧ (program.constEntries zero).getD 0 0 = 0
  /-- `γ` is challenge `0`. -/
  gammaKind : (program.value (FalconRingPowers.gamma program)).kind = .challenge 0
  /-- The ring is an opaque statement value with no arguments. -/
  ringKind : (program.value ring).kind = .pub (.opaque "statement.ring" [])
  /-- The challenge is an opaque statement value with no arguments. -/
  chalKind : (program.value chal).kind = .pub (.opaque "statement.c" [])
  /-- The challenge and the ring are distinct values. -/
  chal_ne_ring : chal ≠ ring
  /-- The values read are of field `0`. -/
  fields : ∀ v ∈ [FalconRingPowers.one program, zero, ring, spec, FalconRingSelect.idx program,
    FalconRingPowers.gamma program, pow, FalconRingSelect.dig program, chal, s2],
    program.valueField v = 0
  /-- The sizes of the values read. -/
  sizes : (program.value (FalconRingSelect.idx program)).size = 6 ∧
    (program.value spec).size = 512 ∧ (program.value ring).size = 32768 ∧
    (program.value chal).size = 512 ∧ (program.value s2).size = 512
  /-- Challenge `0` is one full coordinate of field `0`. -/
  chal0 : (program.challenge 0).size = 1 ∧ (program.challenge 0).sampler = .full ∧
    program.chalField 0 = 0
  /-- The source program's one challenge is `member.ring.gamma`. -/
  isSourceChal_iff : ∀ j, program.IsSourceChal j ↔ j = 0
  /-- The program has values. -/
  values_length : 0 < program.values.length
  /-- The spectrum, the index bits and `s2` are committed. -/
  privKinds : (program.value spec).kind = .priv ∧
    (program.value (FalconRingSelect.idx program)).kind = .priv ∧ (program.value s2).kind = .priv

/-- **The program facts of a native Falcon ring outside the membership** (decided per program):
the values' numbering (`statement.ring` `4`, `statement.c` `5`, `key.spectrum` `6`, `s2` `9`,
`signature.s1` `10`), the signature equation `signature.equation` (predicate `1`), a source
predicate; the zero constant `0^512` (value `2`); the challenge's kind; the fields, sizes and types
of `s2` and `s1`. -/
class FalconRingBase (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
    [FalconRingMember program] : Prop where
  /-- The numbering of the membership's values. -/
  ids : FalconRingMember.ring program = 4 ∧ FalconRingMember.spec program = 6 ∧
    FalconRingMember.mOne program = 12288 ∧ FalconRingMember.psi program = 10302 ∧
    FalconRingSelect.idx program = 7 ∧ FalconRingMember.idxPred program = 14 ∧
    FalconRingMember.chal program = 5 ∧ FalconRingMember.s2 program = 9
  /-- `signature.equation`: `Ntt(c − s1) = spectrum ⊙ Ntt(s2)`. -/
  sig : ∃ t, (program.predicate 1).body = .equal 0 sigLhs (.leaf 2) t
  /-- The signature equation is a source predicate. -/
  inSource1 : 1 < program.predicates.length ∧ program.inSource (program.predicate 1) = true
  /-- The constant `0^512`. -/
  const2 : program.isConstant 2 = true ∧ program.constEntries 2 = List.replicate 512 0
  /-- The challenge is an opaque statement value with no arguments. -/
  chalKind : (program.value 5).kind = .pub (.opaque "statement.c" [])
  /-- The values read are of field `0`. -/
  fields : ∀ v ∈ [2, 5, 9, 10], program.valueField v = 0
  /-- The sizes of the values read. -/
  sizes : (program.value 9).size = 512 ∧ (program.value 10).size = 512 ∧
    (program.value 5).size = 512
  /-- The program has the values read. -/
  values_length : 10 < program.values.length
  /-- `s2` and `signature.s1` are prime-typed source values. -/
  primeVals : ∀ v ∈ [9, 10], program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧
    (program.value v).type = .sub "GF(p^1)"
  /-- `s2` and `s1` are committed. -/
  privKinds : (program.value 9).kind = .priv ∧ (program.value 10).kind = .priv

section Member

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp}

set_option hygiene false in
local notation "vIdx" => FalconRingSelect.idx program

/-- **An element read in an equal field identifier** is the expression's value there. -/
theorem castElt_evalE {rd : program.Valuation I} {a b : ℕ} (h : a = b) (E : RealizedProgram.Expr) (i : ℕ) :
    (RealizedProgram.castElt (program.evalE rd a E i) : (I b).K) = program.evalE rd b E i := by
  subst h
  exact RealizedProgram.castElt_self _

/-- **A public expression's leaf** reads its expression one level down. -/
theorem evalE_leaf_pubExpr (e : program.Env I) {v f : ℕ} {E : RealizedProgram.Expr}
    (hk : (program.value v).kind = .pub (.expr E)) (hf : program.valueField v = f) (i : ℕ) :
    program.evalE (program.reader e) f (.leaf v) i =
      program.evalE (program.read e program.values.length) f E i := by
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_of_pubExpr e hk, castElt_evalE hf]

/-- The program has a value. -/
theorem values_length_succ : ∃ n, program.values.length = n + 1 :=
  ⟨program.values.length - 1, by
    have := FalconRingMember.values_length (program := program)
    omega⟩

/-- **The challenge** `γ` read in field `0`. -/
def gammaOf (e : program.Env I) : (I 0).K := RealizedProgram.castElt (e.chal 0 0)

/-- **Entry `s` of the ring** (`statement.ring`) of a statement, read in field `0`. -/
def ringEntry (x : program.Valuation I) (s : ℕ) : (I 0).K :=
  RealizedProgram.castElt (x (FalconRingMember.ring program) s)

/-- **The committed spectrum** (`key.spectrum`). -/
def specOf (e : program.Env I) (t : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (FalconRingMember.spec program)) t

/-- **A field `equal` of domain `0` holds coordinatewise in field `0`.** -/
theorem holdsAt_equal0 {e : program.Env I} {lhs rhs : RealizedProgram.Expr} {t : RealizedProgram.Target}
    (h : program.HoldsAt e (.equal 0 lhs rhs t)) :
    ∀ i < program.exprLen lhs,
      program.evalE (program.reader e) 0 lhs i = program.evalE (program.reader e) 0 rhs i :=
  fun i hi => by
    have := h i hi
    unfold RealizedProgram.evalWith at this
    rwa [FalconRingMember.domainField0 (program := program)] at this

/-- **A membership predicate holds** where the source program holds. -/
theorem holdsAt_src {e : program.Env I} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [0, FalconRingMember.idxPred program]) : program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (RealizedProgram.predicate_mem (FalconRingMember.inSource p hp).1)
    (FalconRingMember.inSource p hp).2

/-- **Entry `i` of the challenge** (`statement.c`) of a statement, read in field `0`. -/
def chalEntry (x : program.Valuation I) (i : ℕ) : (I 0).K :=
  RealizedProgram.castElt (x (FalconRingMember.chal program) i)

/-- **`s2`**. -/
def s2Of (e : program.Env I) (i : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf (FalconRingMember.s2 program)) i

variable [RingField (I 0) (FalconRingMember.mOne program)]

theorem read_leaf0 (e : program.Env I) :
    program.evalE (program.read e program.values.length) 0
      (.leaf (FalconRingPowers.one program)) 0 = 1 := by
  obtain ⟨n, hn⟩ := values_length_succ (program := program)
  obtain ⟨c0, e0, -⟩ := FalconRingMember.consts (program := program)
  rw [RealizedProgram.evalE_leaf, hn, RealizedProgram.read_of_constant e (RealizedProgram.kind_of_isConstant c0)
    (by omega), RealizedProgram.castElt_decode ((FalconRingMember.fields (program := program)) _ (by simp)),
    e0, RingField.decode_one (negOne := FalconRingMember.mOne program)]

theorem read_leafGamma (e : program.Env I) :
    program.evalE (program.read e program.values.length) 0
      (.leaf (FalconRingPowers.gamma program)) 0 = gammaOf e := by
  obtain ⟨n, hn⟩ := values_length_succ (program := program)
  rw [RealizedProgram.evalE_leaf, hn, RealizedProgram.read_of_challenge e FalconRingMember.gammaKind (by omega),
    RealizedProgram.castElt_castElt_eq, if_pos (by rw [(FalconRingMember.chal0 (program := program)).2.2,
      (FalconRingMember.fields (program := program)) _ (by simp)])]
  rfl

theorem read_leafRing (e : program.Env I) (s : ℕ) :
    program.evalE (program.read e program.values.length) 0 (.leaf (FalconRingMember.ring program)) s =
      ringEntry e.stmt s := by
  obtain ⟨n, hn⟩ := values_length_succ (program := program)
  rw [RealizedProgram.evalE_leaf, hn]
  simp only [RealizedProgram.read, FalconRingMember.ringKind (program := program), if_true]
  rfl

/-- **The index bits** (`member.signer.index`) as naturals, `0` past the sixth. -/
def bitsOf (e : program.Env I) (i : ℕ) : ℕ :=
  if i < 6 then (I 0).toNat (program.evalE (program.reader e) 0 (.leaf vIdx) i) else 0

/-- **The signer's position**: the index bits read as a natural. -/
def idxOf (e : program.Env I) : ℕ := lowBits (bitsOf e) 5

/-- **The index bits are bits** where the source program holds (`member.signer.index.boolean`). -/
theorem bitsOf_spec {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 6) :
    bitsOf e i ≤ 1 ∧ program.evalE (program.reader e) 0 (.leaf vIdx) i = (bitsOf e i : (I 0).K) := by
  obtain ⟨t, hb⟩ := FalconRingMember.idxBool (program := program)
  have h := holdsAt_src hs (p := FalconRingMember.idxPred program) (by simp)
  rw [hb] at h
  have hx := holdsAt_equal0 h i (by
    rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_leaf, (FalconRingMember.sizes (program := program)).1]
    exact hi)
  rw [RealizedProgram.evalE_mul] at hx
  unfold bitsOf
  rw [if_pos hi]
  rcases eq_zero_or_one_of_sq_eq_self ((sq _).trans hx) with h0 | h1
  · rw [h0, RingField.toNat_zero (negOne := FalconRingMember.mOne program), Nat.cast_zero]
    exact ⟨by norm_num, rfl⟩
  · rw [h1, RingField.toNat_one (negOne := FalconRingMember.mOne program), Nat.cast_one]
    exact ⟨le_rfl, rfl⟩

theorem bitsOf_le (e : program.Env I) (hs : program.SourceSatAt e) (i : ℕ) : bitsOf e i ≤ 1 := by
  by_cases hi : i < 6
  · exact (bitsOf_spec hs hi).1
  · simp [bitsOf, hi]

/-- **The signer's position is below `64`.** -/
theorem idxOf_lt (e : program.Env I) (hs : program.SourceSatAt e) : idxOf e < 64 :=
  lowBits_lt (bitsOf_le e hs) 5

theorem decode_mOne : (I 0).decode (FalconRingMember.mOne program) = -1 :=
  RingField.decode_negOne

theorem exprLen_memberLhs (spec pow idx mOne : ℕ) : program.exprLen (memberLhs spec pow idx mOne) = 1 := by
  unfold memberLhs
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_apply, RealizedProgram.exprLen_mul, RealizedProgram.exprLen_reindex]
  simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols]

/-- **The membership's left side**, at index bits that are bits: the fingerprint
`Σ_k spectrum_k γ^k` of the committed spectrum less the fingerprint of the natural-order transform
of the ring's row at the position the bits name (`idxOf`). -/
theorem evalE_memberLhs (e : program.Env I)
    (hb : ∀ i < 6, bitsOf e i ≤ 1 ∧
      program.evalE (program.reader e) 0 (.leaf vIdx) i = (bitsOf e i : (I 0).K)) :
    program.evalE (program.reader e) 0 (memberLhs (FalconRingMember.spec program)
        (FalconRingMember.pow program) vIdx (FalconRingMember.mOne program)) 0 =
      ∑ t : Fin 512, specOf e t * gammaOf e ^ (t : ℕ) - ∑ m : Fin 512, gammaOf e ^ (m : ℕ) *
        RealizedProgram.Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program))
          (fun c => ringEntry e.stmt (idxOf e * 512 + c)) m := by
  have hle : ∀ i, bitsOf e i ≤ 1 := fun i => by
    by_cases hi : i < 6
    · exact (hb i hi).1
    · simp [bitsOf, hi]
  have hidx : idxOf e < 64 := lowBits_lt hle 5
  rw [memberLhs, RealizedProgram.evalE_add, RealizedProgram.evalE_apply_sum, RealizedProgram.evalE_scale_const, decode_mOne]
  have hpow : ∀ k : Fin 512, program.evalE (program.reader e) 0
      (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf (FalconRingMember.spec program))))
        (.reindex [(0, 1, 512)] (.leaf (FalconRingMember.pow program)))) (0 * 512 + k) =
        specOf e k * gammaOf e ^ (k : ℕ) := by
    intro k
    rw [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex,
      RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_one k.isLt,
      Nat.zero_add, RealizedProgram.IndexMap.entry_step_one k.isLt, Nat.zero_add,
      evalE_leaf_pubExpr e FalconRingMember.powersKind
        ((FalconRingMember.fields (program := program)) _ (by simp)),
      RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_one k.isLt, Nat.zero_add,
      powers_eval (read_leaf0 e) (read_leafGamma e) k.isLt]
    rfl
  have hsel := select_top (rd := program.reader e) (f := 0) (b := bitsOf e)
    (D := fun r => program.evalE (program.reader e) 0 (.leaf (FalconRingSelect.dig program)) r) hle
    (fun i hi => (hb i hi).2) (fun _ _ => rfl)
  simp only [hpow]
  rw [hsel, evalE_leaf_pubExpr e FalconRingMember.digestsKind
      ((FalconRingMember.fields (program := program)) _ (by simp)),
    digests_eval (r := lowBits (bitsOf e) 5) (read_leaf0 e) (read_leafGamma e) hidx]
  simp only [read_leafRing]
  unfold idxOf
  ring

/-- The zero constant reads `0` in field `0`. -/
theorem evalE_zero (e : program.Env I) :
    program.evalE (program.reader e) 0 (.leaf (FalconRingMember.zero program)) 0 = 0 := by
  obtain ⟨-, -, c1, e1⟩ := FalconRingMember.consts (program := program)
  rw [RealizedProgram.evalE_leaf_of_isConstant e c1, RealizedProgram.constRead_of_valueField
    ((FalconRingMember.fields (program := program)) _ (by simp)), e1,
    RingField.decode_zero (negOne := FalconRingMember.mOne program)]

/-- **The membership's equation** (`member.signer`): where the source program holds, the
fingerprint `Σ_k spectrum_k γ^k` of the committed spectrum is the fingerprint of the natural-order
transform of the ring's row at the signer's position (`idxOf`). -/
theorem member_eq {e : program.Env I} (hs : program.SourceSatAt e) :
    ∑ t : Fin 512, specOf e t * gammaOf e ^ (t : ℕ) = ∑ m : Fin 512, gammaOf e ^ (m : ℕ) *
      RealizedProgram.Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program))
        (fun c => ringEntry e.stmt (idxOf e * 512 + c)) m := by
  obtain ⟨t, hb⟩ := FalconRingMember.member (program := program)
  have h := holdsAt_src hs (p := 0) (by simp)
  rw [hb] at h
  have hx := holdsAt_equal0 h 0 (by rw [exprLen_memberLhs]; norm_num)
  rw [evalE_zero, evalE_memberLhs e fun i hi => bitsOf_spec hs hi] at hx
  exact sub_eq_zero.1 hx

end Member

/-! ## The membership's event -/

section Event

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp}

/-- **The transform of the signer's row** of the ring, at frequency `m`. -/
def keySpec (e : program.Env I) (m : ℕ) : (I 0).K :=
  RealizedProgram.Ops.nttNatural 512 ((I 0).decode (FalconRingMember.psi program)) (fun c => ringEntry e.stmt (idxOf e * 512 + c)) m

/-- **The polynomial of `n` coefficients** `Σ_{m < n} a_m X^m`. -/
@[irreducible] noncomputable def coeffPoly {K : Type*} [Field K] (n : ℕ) (a : ℕ → K) : Polynomial K :=
  ∑ m ∈ Finset.range n, Polynomial.C (a m) * Polynomial.X ^ m

theorem coeffPoly_natDegree {K : Type*} [Field K] (n : ℕ) (a : ℕ → K) :
    (coeffPoly n a).natDegree ≤ n - 1 := by
  unfold coeffPoly
  exact Polynomial.natDegree_sum_le_of_forall_le (Finset.range n) _ fun m hm =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by
      have := Finset.mem_range.1 hm
      omega)

theorem coeffPoly_eval {K : Type*} [Field K] (n : ℕ) (a : ℕ → K) (x : K) :
    (coeffPoly n a).eval x = ∑ m ∈ Finset.range n, a m * x ^ m := by
  rw [coeffPoly, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem coeffPoly_coeff {K : Type*} [Field K] {n : ℕ} (a : ℕ → K) {m : ℕ} (hm : m < n) :
    (coeffPoly n a).coeff m = a m := by
  rw [coeffPoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_range.2 hm) h

/-- **The fingerprint's polynomial**: `Σ_m (spectrum_m − NTT(h)_m) X^m`, `h` the signer's row. -/
noncomputable def fpPoly (e : program.Env I) : Polynomial (I 0).K :=
  coeffPoly 512 fun m => specOf e m - keySpec e m

/-- **The membership's event**: `γ` is a root of the fingerprint's polynomial, which is nonzero
(degree at most `511`). -/
noncomputable def fpEvent (e : program.Env I) : ChallengeEvent (I 0).K :=
  ⟨fpPoly e, 511, le_trans (coeffPoly_natDegree _ _) (by norm_num)⟩

theorem fpEvent_poly (e : program.Env I) : (fpEvent e).poly = fpPoly e := rfl

/-- **The source program's event** at `member.ring.gamma` (challenge `0`). -/
def ringEvent (j : ℕ) (e : program.Env I) : Prop := j = 0 ∧ (fpEvent e).BadAt (gammaOf e)

theorem specOf_congr {e e' : program.Env I} (ha : e.asg = e'.asg) : specOf e = specOf e' := by
  funext t
  unfold specOf
  rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).1,
    RealizedProgram.reader_of_priv e' (FalconRingMember.privKinds (program := program)).1, ha]

theorem bitsOf_congr {e e' : program.Env I} (ha : e.asg = e'.asg) : bitsOf e = bitsOf e' := by
  funext t
  unfold bitsOf
  rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).2.1,
    RealizedProgram.reader_of_priv e' (FalconRingMember.privKinds (program := program)).2.1, ha]

theorem fpEvent_congr {e e' : program.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    fpEvent e = fpEvent e' := by
  have h1 := specOf_congr ha
  have h2 : idxOf e = idxOf e' := by unfold idxOf; rw [bitsOf_congr ha]
  have hk : keySpec e = keySpec e' := by
    funext m
    unfold keySpec ringEntry
    rw [h2, hs]
  have hp : fpPoly e = fpPoly e' := by
    unfold fpPoly
    rw [h1, hk]
  simp only [fpEvent, hp]

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): the event reads the statement, the
committed assignment and its challenge. -/
theorem ringEvent_use : RealizedProgram.ChallengeUseAt program I ringEvent := by
  intro j e e' h
  unfold ringEvent
  rw [fpEvent_congr h.stmt h.asg]
  by_cases hj0 : j = 0
  · subst hj0
    unfold gammaOf
    rw [h.chal 0 (Or.inr ⟨rfl, le_refl 0⟩)]
  · simp [hj0]

/-- **The event's errors**: `511/|F|` at `member.ring.gamma`, `0` elsewhere. -/
noncomputable def ringEps (I : RealizedProgram.Interp) (j : ℕ) : NNReal :=
  if j = 0 then 511 / Fintype.card (I 0).K else 0

/-- **The event's probability** (`RealizedProgram.rbr_of_events`' `hbound`): at most `511/|F|` at
`member.ring.gamma` (`RealizedProgram.probUniform_badAt_setChal_le`, Schwartz–Zippel). -/
theorem ringEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env I,
    Pr[c ← program.ChalVal I j : ringEvent j (e.setChal j c)] ≤ (ringEps I j : ENNReal) := by
  intro j hj e
  obtain rfl := (FalconRingMember.isSourceChal_iff (program := program) j).1 hj
  have hset : ∀ c, ringEvent 0 (e.setChal 0 c) ↔
      (fpEvent e).BadAt (RealizedProgram.castElt ((e.setChal 0 c).chal 0 0)) := fun c => by
    simp only [ringEvent, true_and]
    rw [fpEvent_congr (e := e.setChal 0 c) (e' := e) rfl rfl]
    rfl
  simp only [hset]
  obtain ⟨hsz, hsm, hf⟩ := FalconRingMember.chal0 (program := program)
  refine (RealizedProgram.probUniform_badAt_setChal_le hsz hsm hf (fpEvent e) e).trans ?_
  simp [ringEps, fpEvent]

variable [RingField (I 0) (FalconRingMember.mOne program)]

/-- **Without the event, the spectrum is the transform of the signer's row**: the fingerprints
agree (`member_eq`), so `γ` is a root of the fingerprint's polynomial, which is then `0`. -/
theorem spec_eq_of_not_event {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ ringEvent 0 e) (m : Fin 512) : specOf e m = keySpec e m := by
  have heval : (fpPoly e).eval (gammaOf e) = 0 := by
    rw [fpPoly, coeffPoly_eval, ← Fin.sum_univ_eq_sum_range
      (fun m => (specOf e m - keySpec e m) * gammaOf e ^ m) 512]
    have := member_eq hs
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [this, sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => _root_.mul_comm _ _
  have hz : fpPoly e = 0 := by
    by_contra hne
    apply hev
    refine ⟨rfl, ?_, ?_⟩
    · rw [fpEvent_poly]
      exact hne
    · rw [fpEvent_poly]
      exact heval
  have := coeffPoly_coeff (fun m => specOf e m - keySpec e m) m.isLt
  rw [← fpPoly, hz, Polynomial.coeff_zero] at this
  exact sub_eq_zero.1 this.symm

end Event

/-! ## The transforms -/

section Ntt

variable {program : RealizedProgram} {I : RealizedProgram.Interp}

/-- **A natural-order transform of `512` coordinates** at the root `ψ`, read at coordinate
`k < 512` of its named operator. -/
theorem evalE_apply_ntt (rd : program.Valuation I) (ψ : ℕ) (E : RealizedProgram.Expr) {k : ℕ} (hk : k < 512) :
    program.evalE rd 0 (.apply (.ntt 512 ψ .natural) E) k =
      RealizedProgram.Ops.nttNatural 512 ((I 0).decode ψ) (program.evalE rd 0 E) k := by
  rw [RealizedProgram.evalE_apply]
  simp only [RealizedProgram.NamedOp.apply, RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, Nat.mod_eq_of_lt hk,
    Nat.div_eq_of_lt hk, zero_mul, zero_add]

end Ntt

/-! ## The relation and the extractor -/

section Relation

open Emulated (PublicKey)
open Native (CoreWit)

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] {I : RealizedProgram.Interp}

/-- **The challenge's coefficients** of a statement (`statement.c`), read as naturals below `q`. -/
def chalNat (x : program.Valuation I) (i : Fin falcon512.n) : ℕ :=
  (I 0).toNat (chalEntry x i)

/-- **Key `r` of the ring** of a statement (row `r` of `statement.ring`), its coefficients read as
naturals below `q`. -/
def ringKey (x : program.Valuation I) (r : ℕ) : PublicKey :=
  ⟨Falcon512.ofCoeff fun c => ((I 0).toNat (ringEntry x (r * 512 + c)) : _root_.Falcon.Coeff)⟩

/-- **The relation of the theorem at a Falcon ring's realized program** at the statement's ring and
challenge `c`: the signer's position is below `64` and, at its key, Falcon's algebraic verifier
accepts `s2` on `c` (`c − s2·h` and `s2` within the norm bound) and `s2` is encodable. -/
def rel : Set (program.Valuation I × CoreWit) :=
  {p | p.2.idx < 64 ∧
    Falcon512.algebraOk falcon512 (ringKey p.1 p.2.idx).h
      (Falcon512.ofCoeff fun i => (chalNat p.1 i : _root_.Falcon.Coeff)) p.2.s2.toRq ∧
    Falcon512.EncodingBounds falcon512 p.2.s2}

/-- **The witness read off the committed values**: the index bits read as the position, and the
centred `s2` (`Emulated.decodeS2Int`).

Running time: `6` bits and `512` coefficients read, lifted and centred.
This running time is argued here, not proved in Lean. -/
-- spec-side
def proj (_x : program.Valuation I) (a : program.Assignment I) : CoreWit :=
  ⟨lowBits (fun i => if i < 6 then (I 0).toNat (RealizedProgram.castElt (a.val (FalconRingSelect.idx program) i)) else 0) 5,
    Emulated.decodeS2Int fun i => (RealizedProgram.castElt (a.val (FalconRingMember.s2 program) i) : (I 0).K)⟩

/-- **The extractor of `Π_P₀`** (`RealizedProgram.sourceExtractor` at `proj`).

Running time: the source extractor's reading of the committed values, then one call of `proj`
(`6` bits and `512` coefficients read, lifted and centred).
This running time is argued here, not proved in Lean. -/
def extractor :
    Extractor (program.sourceSpec I) (program.Valuation I) CoreWit :=
  program.sourceExtractor I proj

theorem proj_idx (e : program.Env I) : (proj e.stmt e.asg).idx = idxOf e := by
  simp only [proj, idxOf]
  congr 1
  funext i
  simp only [bitsOf, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).2.1]

theorem proj_s2 (e : program.Env I) :
    (proj e.stmt e.asg).s2 = Emulated.decodeS2Int fun i => s2Of e i := by
  simp only [proj, s2Of, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_priv e (FalconRingMember.privKinds (program := program)).2.2]
  rfl

end Relation

/-! ## The signature equation -/

section Signature

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingBase program] {I : RealizedProgram.Interp}


/-- **`signature.s1`** (value `10`). -/
def s1Of (e : program.Env I) (i : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf 10) i


variable [AField (I 0)]

theorem decode_q1 : (I 0).decode 12288 = -1 := RingField.decode_negOne

/-- **The signature equation's left side** at frequency `k < 512`:
`Ntt(c − s1)_k − spectrum_k · Ntt(s2)_k`. -/
theorem evalE_sigLhs (e : program.Env I) {k : ℕ} (hk : k < 512) :
    program.evalE (program.reader e) 0 sigLhs k =
      RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302) (fun i => chalEntry e.stmt i - s1Of e i) k -
        specOf e k * RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302) (s2Of e) k := by
  rw [sigLhs, RealizedProgram.evalE_add, evalE_apply_ntt _ 10302 _ hk, RealizedProgram.evalE_scale_const, decode_q1,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_one hk, Nat.zero_add,
    RealizedProgram.IndexMap.entry_step_one hk, Nat.zero_add, evalE_apply_ntt _ 10302 _ hk]
  have hc : RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302)
      (program.evalE (program.reader e) 0 (.add (.leaf 5) (.scale (.const 12288) (.leaf 10)))) k =
      RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302) (fun i => chalEntry e.stmt i - s1Of e i) k := by
    refine RealizedProgram.NamedOp.nttNatural_congr (fun i _ => ?_) k
    rw [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, decode_q1, RealizedProgram.evalE_leaf,
      RealizedProgram.reader_of_opaque_nil e (FalconRingBase.chalKind (program := program))]
    unfold chalEntry s1Of
    rw [(FalconRingBase.ids (program := program)).2.2.2.2.2.2.1]
    ring
  rw [hc]
  unfold specOf s2Of
  rw [(FalconRingBase.ids (program := program)).2.1,
    (FalconRingBase.ids (program := program)).2.2.2.2.2.2.2]
  ring

theorem exprLen_sigLhs : program.exprLen sigLhs = 512 := by
  rw [sigLhs, RealizedProgram.exprLen_add, RealizedProgram.exprLen_apply, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf,
    (FalconRingBase.sizes (program := program)).2.2]
  simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols]

/-- The zero constant `2` reads `0` in field `0`. -/
theorem evalE_leaf2 (e : program.Env I) {k : ℕ} (hk : k < 512) :
    program.evalE (program.reader e) 0 (.leaf 2) k = 0 := by
  obtain ⟨c2, e2⟩ := FalconRingBase.const2 (program := program)
  rw [RealizedProgram.evalE_leaf_of_isConstant e c2, RealizedProgram.constRead_of_valueField
    ((FalconRingBase.fields (program := program)) 2 (by simp)), e2, List.getD_eq_getElem?_getD,
    List.getElem?_replicate, if_pos hk, Option.getD_some, AField.decode_eq, Nat.cast_zero]

/-- **The signature equation** (`signature.equation`): where the source program holds,
`Ntt(c − s1)_k = spectrum_k · Ntt(s2)_k` at every frequency `k < 512`. -/
theorem sig_eq {e : program.Env I} (hs : program.SourceSatAt e) {k : ℕ} (hk : k < 512) :
    RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302) (fun i => chalEntry e.stmt i - s1Of e i) k =
      specOf e k * RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302) (s2Of e) k := by
  obtain ⟨t, hb⟩ := FalconRingBase.sig (program := program)
  have h := hs.preds _ (RealizedProgram.predicate_mem (FalconRingBase.inSource1 (program := program)).1)
    (FalconRingBase.inSource1 (program := program)).2
  rw [hb] at h
  have hx := holdsAt_equal0 h k (by rw [exprLen_sigLhs]; exact hk)
  rw [evalE_leaf2 e hk, evalE_sigLhs e hk] at hx
  exact sub_eq_zero.1 hx

end Signature

/-! ## The relation and the extractor -/

/-- **A node element read in an equal field identifier** stays in the node. -/
theorem castElt_mem_node_of_eq {I : RealizedProgram.Interp} {a b : ℕ} (h : a = b) {s : String} {x : (I a).K}
    (hx : x ∈ (I a).node s) : (RealizedProgram.castElt x : (I b).K) ∈ (I b).node s := by
  subst h
  rwa [RealizedProgram.castElt_self]

section Extract

open Emulated (PublicKey)
open Native (CoreWit keyRecord psiF RingAlgebra SpectralRows)
open Falcon512.Native (Committed AlgRequests)
open AField (φq φq_apply coord0_φq_mul)

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingBase program] {I : RealizedProgram.Interp} [AField (I 0)]

/-- **A native ring's field facts at its constant `−1`** (`12288`). -/
theorem ringField_base : RingField (I 0) (FalconRingMember.mOne program) := by
  rw [(FalconRingBase.ids (program := program)).2.2.1]
  infer_instance

attribute [local instance] ringField_base

/-- **A prime-typed source value is in the prime subfield** where the source program holds. -/
theorem prime_of_mem {e : program.Env I} (hs : program.SourceSatAt e) {v : ℕ} (hv : v ∈ [9, 10])
    {j : ℕ} (hj : j < 512) :
    program.evalE (program.reader e) 0 (.leaf v) j ∈ (I 0).node "GF(p^1)" := by
  obtain ⟨hsrc, hts, hty⟩ := FalconRingBase.primeVals (program := program) v hv
  have hsz : (program.value v).size = 512 := by
    rcases List.mem_pair.1 hv with rfl | rfl
    · exact (FalconRingBase.sizes (program := program)).1
    · exact (FalconRingBase.sizes (program := program)).2.1
  have hvl : v < program.values.length := by
    have := FalconRingBase.values_length (program := program)
    rcases List.mem_pair.1 hv with rfl | rfl <;> omega
  have hmem := hs.types v hvl hsrc hts j (by rw [hsz]; exact hj)
  rw [hty] at hmem
  exact castElt_mem_node_of_eq ((FalconRingBase.fields (program := program)) v (by
    rcases List.mem_pair.1 hv with rfl | rfl <;> simp)) hmem

theorem prime_s2 {e : program.Env I} (hs : program.SourceSatAt e) (j : Fin falcon512.n) :
    s2Of e j ∈ (I 0).node "GF(p^1)" := by
  unfold s2Of
  rw [(FalconRingBase.ids (program := program)).2.2.2.2.2.2.2]
  exact prime_of_mem hs (v := 9) (by simp) j.isLt

theorem prime_s1 {e : program.Env I} (hs : program.SourceSatAt e) (j : Fin falcon512.n) :
    s1Of e j ∈ (I 0).node "GF(p^1)" := prime_of_mem hs (v := 10) (by simp) j.isLt

/-- **The coefficients of a ring key** are the ring's entries read as naturals. -/
theorem keyCoeffs_ringKey (x : program.Valuation I) (r : ℕ) (j : Fin falcon512.n) :
    EmulatedAlgebraCircuit.keyCoeffs (ringKey x r).h j = (I 0).toNat (ringEntry x (r * 512 + j)) := by
  simp only [ringKey, EmulatedAlgebraCircuit.keyCoeffs, Falcon512.coeff_ofCoeff, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (AField.toNat_lt _)

/-- **The norm's obligation** (discharged per program by the generic norm, `FalconNorm`): advice
whose `s1` is `signature.s1`, at which the native norm and the encoding's checks hold on `s1 ‖ s2`
and the range requests hold. -/
def NormAdvice (e : program.Env I) : Prop :=
  ∃ alg : Committed (I 0).K, (∀ i, alg.s1 i = s1Of e i) ∧
    NativeNorm.Holds (Native.normInputs (fun i => s2Of e i) alg) alg.norm ∧
    NativeEncoding.BitsHold alg.norm ∧ AlgRequests alg

/-- **The norm's obligation wherever the source program holds.** -/
def NormSound : Prop := ∀ e : program.Env I, program.SourceSatAt e → NormAdvice e

/-- **The projection onto the prime field**: `x ↦ (toNat x : K)`, additive. -/
def primeProj : (I 0).K →+ (I 0).K :=
  (φq (FA := I 0)).toAddMonoidHom.comp (AField.coord0 (FA := I 0))

theorem primeProj_apply (x : (I 0).K) : primeProj x = (((I 0).toNat x : ℕ) : (I 0).K) := by
  simp only [primeProj, AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, φq_apply, AField.toNat_eq]

theorem primeProj_mul_prime (a s : (I 0).K) (hs : (((I 0).toNat s : ℕ) : (I 0).K) = s) :
    primeProj (a * s) = primeProj a * s := by
  have hs' : φq (AField.coord0 s) = s := by
    rw [φq_apply, ← AField.toNat_eq, hs]
  simp only [primeProj, AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  conv_lhs => rw [← hs', _root_.mul_comm, coord0_φq_mul]
  rw [map_mul, hs', _root_.mul_comm]

/-- **A prime-subfield element's projection** is itself. -/
theorem primeProj_prime {s : (I 0).K} (hs : (((I 0).toNat s : ℕ) : (I 0).K) = s) :
    primeProj s = s := by
  rw [primeProj_apply, hs]

theorem primeProj_negacyclic (h s2 : Fin falcon512.n → (I 0).K)
    (hs : ∀ j, (((I 0).toNat (s2 j) : ℕ) : (I 0).K) = s2 j) (k : Fin falcon512.n) :
    primeProj (LatticeCrypto.negacyclicConvCoeff h s2 k) =
      LatticeCrypto.negacyclicConvCoeff (fun j => primeProj (h j)) s2 k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs
  · exact primeProj_mul_prime _ _ (hs _)
  · rw [map_neg, primeProj_mul_prime _ _ (hs _)]
  · exact map_zero _

theorem decode_psi : (I 0).decode 10302 = psiF (I 0).K := by
  rw [AField.decode_eq]
  rfl

theorem nttNatural_eq_negSpectrum (x : ℕ → (I 0).K) (k : Fin falcon512.n) :
    RealizedProgram.Ops.nttNatural 512 ((I 0).decode 10302) x k =
      DFT.negSpectrum (psiF (I 0).K) (fun j : Fin falcon512.n => x j) k := by
  rw [RealizedProgram.Ops.nttNatural_apply 512 _ _ k.isLt, decode_psi, DFT.negSpectrum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.mul_comm]

/-- **The relation from the source program without the event** (`RealizedProgram.rbr_of_events`'
`hsound`), given the norm's obligation: the spectrum is the transform of the signer's row
(`spec_eq_of_not_event`), so the signature equation is `c − s1 = h · s2` over the field; its
projection onto the prime field is the ring's algebra at the signer's key (`RingAlgebra` at
`ringKey`), and `Native.ringAlgebra_sound` gives the relation. -/
theorem mem_rel_of_source (hN : NormSound (program := program) (I := I)) {e : program.Env I}
    (hs : program.SourceSatAt e) (hev : ¬ ringEvent 0 e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  obtain ⟨alg, hs1, hnorm, henc, hreq⟩ := hN e hs
  set pk := ringKey e.stmt (idxOf e) with hpk
  have hψ := Native.isPrimitiveRoot_psiF (I 0).K
  have hn0 := Native.natCast_n_ne_zero (I 0).K
  -- the signature equation over the field
  have hsig : (fun i : Fin falcon512.n => chalEntry e.stmt i - s1Of e i) =
      LatticeCrypto.negacyclicConvCoeff (fun j : Fin falcon512.n =>
        ringEntry e.stmt (idxOf e * 512 + j)) (fun i => s2Of e i) := by
    apply DFT.negSpectrum_injective hψ hn0
    rw [DFT.negSpectrum_negacyclicConvCoeff (Native.psiF_pow _)]
    funext k
    have h := sig_eq hs k.isLt
    rw [spec_eq_of_not_event hs hev k, keySpec, (FalconRingBase.ids (program := program)).2.2.2.1,
      nttNatural_eq_negSpectrum,
      nttNatural_eq_negSpectrum, nttNatural_eq_negSpectrum] at h
    exact h
  -- s1 and s2 are in the prime field
  have hs2p : ∀ j : Fin falcon512.n, (((I 0).toNat (s2Of e j) : ℕ) : (I 0).K) = s2Of e j :=
    fun j => AField.natCast_toNat (prime_s2 hs j)
  have hs1p : ∀ j : Fin falcon512.n, (((I 0).toNat (s1Of e j) : ℕ) : (I 0).K) = s1Of e j :=
    fun j => AField.natCast_toNat (prime_s1 hs j)
  -- its projection onto the prime field
  have hproj : (fun i : Fin falcon512.n => ((chalNat e.stmt i : ℕ) : (I 0).K) - alg.s1 i) =
      LatticeCrypto.negacyclicConvCoeff (fun j : Fin falcon512.n =>
        ((EmulatedAlgebraCircuit.keyCoeffs pk.h j : ℕ) : (I 0).K)) (fun i => s2Of e i) := by
    funext i
    have h := congrArg (fun f => primeProj (f i)) hsig
    simp only at h
    rw [map_sub, primeProj_prime (hs1p i), primeProj_negacyclic _ _ hs2p] at h
    rw [hs1, chalNat, ← primeProj_apply, h]
    congr 1
    funext j
    rw [primeProj_apply, hpk, keyCoeffs_ringKey]
  have halg : RingAlgebra (fun i => (chalNat e.stmt i : (I 0).K)) (keyRecord pk)
      (fun i => s2Of e i) alg := by
    refine ⟨fun k => ?_, hnorm, henc⟩
    have := congrArg (fun f => DFT.negSpectrum (psiF (I 0).K) f k) hproj
    rw [DFT.negSpectrum_negacyclicConvCoeff (Native.psiF_pow _)] at this
    exact this
  have hq : ∀ i, chalNat e.stmt i < 2 ^ falconSampleBits := fun i =>
    (AField.toNat_lt _).trans (by norm_num [falconSampleBits])
  obtain ⟨hok, hbd⟩ := Native.ringAlgebra_sound hq halg hreq
  refine ⟨by rw [proj_idx]; exact idxOf_lt e hs, ?_, ?_⟩
  · show Falcon512.algebraOk falcon512 (ringKey e.stmt (proj e.stmt e.asg).idx).h _
      (proj e.stmt e.asg).s2.toRq
    rw [proj_idx, proj_s2]
    have h2 := Emulated.decodeS2Int_toRq (fun i : Fin falcon512.n => s2Of e i)
    erw [h2]
    exact hok
  · show Falcon512.EncodingBounds falcon512 (proj e.stmt e.asg).s2
    rw [proj_s2]
    exact hbd

end Extract

/-! ## Round-by-round knowledge soundness of `Π_P₀` -/

section Rbr

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconRingBase program] {I : RealizedProgram.Interp} [AField (I 0)]

/-- **The relation from the source program without the event** (`RealizedProgram.rbr_of_events`'
`hsound`), given the norm's obligation. -/
theorem sound_of_norm (hN : NormSound (program := program) (I := I)) :
    ∀ e : program.Env I, program.StatementOk I e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ ringEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ _ hs hno =>
    mem_rel_of_source hN hs (hno 0 ((FalconRingMember.isSourceChal_iff (program := program) 0).2 rfl))

/-- **Round-by-round knowledge soundness of `Π_P₀` for a native Falcon ring**
(`RealizedProgram.rbr_of_events`), given the norm's obligation (`NormSound`, discharged per program by the
generic norm): the relation `rel`, the extractor `extractor`, the error `511/|F|` at
`member.ring.gamma` and `0` elsewhere (`ringEps`). -/
theorem rbr_of_norm (hN : NormSound (program := program) (I := I)) :
    rbrKnowledgeSoundness rel (program.sourceVerifier I) extractor
      (program.eventState I rel proj ringEvent ringEvent_use (sound_of_norm hN))
      (program.roundError I (ringEps I)) :=
  program.rbr_of_events I rel proj ringEvent (ringEps I) ringEvent_use ringEvent_bound
    (sound_of_norm hN)

end Rbr

end GordieHowe.Falcon512.Ring
