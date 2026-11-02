-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.OpRows
public import GordieHoweNative.Language.Realizations.Circuit.NttPure

@[expose] public section

/-!
# GordieHowe: the staged NTT networks on values

A staged negacyclic transform of length `n = 2^L` runs `L` butterfly stages on a working array
(`bflyF`, `stagesF`): stage `s` pairs positions `q` and `q + h_s` of each block of `2h_s` with a
twiddle `ψ^e` per pair. The two orders differ only in their input, half-sizes and twiddle exponents
(`nttInF`, `nttHalf`, `nttTwIdx`):

* **Natural order** (`ntt_gadget::transform`, `lib/circuits/ntt/ntt_gadget.h`): the input twisted
  (`x_i ↦ ψ^i x_i`) and bit-reversed, `h_s = 2^s`, twiddle `step^j` at offset `j`. A stage merges
  the blocks' polynomials by parity (`natStageF_inv`, the radix-2 decimation in time;
  `hornerEval_parity`), the bit reversal reads the parts of the full parity split
  (`getD_splitParity`), and after the stages position `m` holds the twisted input's polynomial at
  `ω^m`, `ω = ψ²` (`natStagesF_inv`, `nttNatural_of_stages`).
* **Scheme order** (`StagedNtt::forward`, `lib/gordiehowe/ops/operators.h`; FIPS 204 Algorithm 41):
  the input as is, `h_s = 2^(L−1−s)`, twiddle `ψ^br_L(2^s + g)` for block `g`. After `s` stages,
  block `g` agrees with the input polynomial wherever `z^(2^(L−s)) = ψ^(2^(L−s)(2·br_s(g)+1))`
  (`SchInv`, `schStage_inv`, `schStages_inv`), so position `m` ends at `ψ^(2·br_L(m)+1)`
  (`nttScheme_of_stagesF`).

`nttBy_of_stagesF` states both: the schedule of order `o` computes `ntt n ψ o`.

The definitions are in `GordieHoweNative/Language/Realizations/Circuit/NttPure.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open OpList

section Pure

variable {F : Type*} [CommRing F]

/-- **One natural-order stage** of half-size `h` on position values, twiddle `w j` at offset `j`:
in each block of `2h`, position `j` becomes `A j + w j · A (j + h)` and position `j + h` becomes
`A j − w j · A (j + h)`. -/
def natStageF (h : ℕ) (w : ℕ → F) (A : ℕ → F) (p : ℕ) : F :=
  if p % (2 * h) < h then A p + w (p % (2 * h)) * A (p + h)
  else A (p - h) - w (p % (2 * h) - h) * A p

/-- **The stage invariant**: position `g · len + t` holds part `g`'s polynomial at `ρ^t`. -/
def NatInv (Q : List (List F)) (len : ℕ) (ρ : F) (A : ℕ → F) : Prop :=
  ∀ g < Q.length, ∀ t < len, A (g * len + t) = hornerEval (Q.getD g []) (ρ ^ t)

theorem getD_flatMap_pair {α β : Type*} (f g : α → β) (d : β) (da : α) :
    ∀ (l : List α) (i : ℕ), i < l.length →
      (l.flatMap fun x => [f x, g x]).getD (2 * i) d = f (l.getD i da) ∧
        (l.flatMap fun x => [f x, g x]).getD (2 * i + 1) d = g (l.getD i da)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: l, 0, _ => by simp
  | x :: l, i + 1, h => by
    have ih := getD_flatMap_pair f g d da l i (by simpa using h)
    simp only [List.flatMap_cons, List.getD_cons_succ]
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by ring]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right] using ih

/-- **A stage merges the parity halves**: where the parts of `P` split by parity sit at half-size
`h` at powers of `ρ`, the stage with twiddles `ρ₂^j` (`ρ₂² = ρ`, `ρ₂^h = −1`) puts the parts of
`P` at size `2h` at powers of `ρ₂`. -/
theorem natStageF_inv {P : List (List F)} {h : ℕ} {ρ ρ₂ : F} (hρ : ρ₂ ^ 2 = ρ)
    (hh : ρ₂ ^ h = -1) {A : ℕ → F}
    (hA : NatInv (P.flatMap fun Q => [evenPart Q, oddPart Q]) h ρ A) :
    NatInv P (2 * h) ρ₂ (natStageF h (fun j => ρ₂ ^ j) A) := by
  intro g hg t ht
  have hlen : (P.flatMap fun Q => [evenPart Q, oddPart Q]).length = 2 * P.length := by
    rw [length_flatMap_pair]
  obtain ⟨he, ho⟩ := getD_flatMap_pair evenPart oddPart [] [] P g hg
  have m1 : g * (2 * h) = 2 * g * h := by ring
  have m2 : (2 * g + 1) * h = 2 * g * h + h := by ring
  have hmod : (g * (2 * h) + t) % (2 * h) = t := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
  unfold natStageF
  rw [hmod]
  by_cases hth : t < h
  · simp only [hth, ↓reduceIte]
    have e1 := hA (2 * g) (by omega) t hth
    have e2 := hA (2 * g + 1) (by omega) t hth
    rw [show 2 * g * h + t = g * (2 * h) + t by ring, he] at e1
    rw [show (2 * g + 1) * h + t = g * (2 * h) + t + h by ring, ho] at e2
    rw [e1, e2, hornerEval_parity (P.getD g []) (ρ₂ ^ t), ← pow_mul, mul_comm t 2, pow_mul, hρ]
  · simp only [hth, ↓reduceIte]
    have t' : t - h < h := by omega
    have e1 := hA (2 * g) (by omega) (t - h) t'
    have e2 := hA (2 * g + 1) (by omega) (t - h) t'
    rw [show 2 * g * h + (t - h) = g * (2 * h) + t - h by omega, he] at e1
    rw [show (2 * g + 1) * h + (t - h) = g * (2 * h) + t by omega, ho] at e2
    rw [e1, e2, hornerEval_parity (P.getD g []) (ρ₂ ^ t)]
    have hsplit : ρ₂ ^ t = ρ₂ ^ h * ρ₂ ^ (t - h) := by rw [← pow_add]; congr 1; omega
    have hsq : (ρ₂ ^ t) ^ 2 = ρ ^ (t - h) := by
      rw [hsplit, mul_pow, hh, ← pow_mul, mul_comm (t - h) 2, pow_mul, hρ]
      ring
    rw [hsq, hsplit, hh]
    ring

/-- **The parts of a parity split**: entry `t` of part `g` of a list of length `2^L · M` split `L`
times is the entry at `t · 2^L + br_L(g)`, each part of length `M`. -/
theorem getD_splitParity :
    ∀ (L : ℕ) {M : ℕ} {l : List F}, l.length = 2 ^ L * M → ∀ g < 2 ^ L,
      ((splitParity L l).getD g []).length = M ∧ ∀ t < M,
        ((splitParity L l).getD g []).getD t 0 = l.getD (t * 2 ^ L + bitRevNat L g) 0
  | 0, M, l, h, g, hg => by
    obtain rfl : g = 0 := by omega
    refine ⟨by simpa [splitParity] using h, fun t _ => ?_⟩
    simp [splitParity, bitRevNat]
  | L + 1, M, l, h, g, hg => by
    obtain ⟨i, hi⟩ : ∃ i, g = 2 * i + g % 2 := ⟨g / 2, by omega⟩
    have hi' : i < 2 ^ L := by rw [pow_succ] at hg; omega
    have ih := getD_splitParity L (M := 2 * M) (l := l) (by rw [h, pow_succ]; ring) i hi'
    have hlen : (splitParity L l).length = 2 ^ L := length_splitParity L l
    obtain ⟨he, ho⟩ := getD_flatMap_pair evenPart oddPart [] [] (splitParity L l) i
      (by rw [hlen]; exact hi')
    have hbr : bitRevNat (L + 1) g = g % 2 * 2 ^ L + bitRevNat L i := by
      show g % 2 * 2 ^ L + bitRevNat L (g / 2) = _
      congr 2
      omega
    rcases Nat.mod_two_eq_zero_or_one g with h2 | h2
    · rw [h2, add_zero] at hi
      have hpart : (splitParity (L + 1) l).getD g [] =
          evenPart ((splitParity L l).getD i []) := by rw [hi]; exact he
      refine ⟨by rw [hpart, length_evenPart, ih.1]; omega, fun t ht => ?_⟩
      rw [hpart, getD_evenPart, ih.2 _ (by omega), hbr, h2]
      congr 1
      rw [pow_succ]
      ring
    · rw [h2] at hi
      have hpart : (splitParity (L + 1) l).getD g [] =
          oddPart ((splitParity L l).getD i []) := by rw [hi]; exact ho
      refine ⟨by rw [hpart, length_oddPart, ih.1]; omega, fun t ht => ?_⟩
      rw [hpart, getD_oddPart, ih.2 _ (by omega), hbr, h2]
      congr 1
      rw [pow_succ]
      ring

/-- **The stages of the natural-order network** on position values: `r` stages left, half-size
`h`, the stage's twiddle base `step r` (`ω^(2^(r−1))` for the stage of half-size `2^(L−r)`). -/
def natStagesF (step : ℕ → F) : ℕ → ℕ → (ℕ → F) → ℕ → F
  | 0, _, A => A
  | r + 1, h, A => natStagesF step r (2 * h) (natStageF h (fun j => step (r + 1) ^ j) A)

/-- **The network keeps the invariant**: from the parts of the split `r` levels deep at
half-size `h`, at powers of `ω^(2^r)`, the remaining stages give the whole list at powers of
`ω`, where `ω^(2^(r−1) · h) = −1` at each stage. -/
theorem natStagesF_inv {ω : F} {n : ℕ}
    (hω : ∀ r h, 2 ^ r * h = n → 0 < r → (ω ^ 2 ^ (r - 1)) ^ h = -1)
    {y : List F} :
    ∀ (r h : ℕ) {A : ℕ → F}, 2 ^ r * h = n →
      NatInv (splitParity r y) h (ω ^ 2 ^ r) A →
      NatInv [y] n ω (natStagesF (fun r => ω ^ 2 ^ (r - 1)) r h A)
  | 0, h, A, hn, hA => by
    rw [pow_zero, one_mul] at hn
    subst hn
    simpa [splitParity, natStagesF] using hA
  | r + 1, h, A, hn, hA => by
    have hρ : (ω ^ 2 ^ r) ^ 2 = ω ^ 2 ^ (r + 1) := by rw [← pow_mul, pow_succ]
    have hh : (ω ^ 2 ^ r) ^ h = -1 := by simpa using hω (r + 1) h hn (by omega)
    have h1 := natStageF_inv hρ hh (P := splitParity r y) (by simpa [splitParity] using hA)
    exact natStagesF_inv hω r (2 * h) (by rw [← hn, pow_succ]; ring) (by simpa using h1)

/-! ### The common stage and the schedules -/

/-- **One butterfly stage** of half-size `h` on position values, twiddle `τ q` at the upper
position `q` of each pair: in each block of `2h`, positions `q` and `q + h` become
`A q + τ q · A (q + h)` and `A q − τ q · A (q + h)`. -/
def bflyF (h : ℕ) (τ : ℕ → F) (A : ℕ → F) (p : ℕ) : F :=
  if p % (2 * h) < h then A p + τ p * A (p + h) else A (p - h) - τ (p - h) * A p

/-- **Stages by a schedule**: from stage `s`, `r` stages left, stage `s` of half-size `(σ s).1`
with twiddles `(σ s).2`. -/
def stagesF (σ : ℕ → ℕ × (ℕ → F)) : ℕ → ℕ → (ℕ → F) → ℕ → F
  | 0, _, A => A
  | r + 1, s, A => stagesF σ r (s + 1) (bflyF (σ s).1 (σ s).2 A)

/-- **The schedule of a staged transform** of length `n = 2^L` at `ψ`, in order `o`. -/
def nttSchedF (n L : ℕ) (ψ : F) (o : NttOrder) (s : ℕ) : ℕ × (ℕ → F) :=
  (nttHalf L o s, fun q => ψ ^ nttTwIdx n L o s q)

/-- **The input of a staged transform**: natural order twists by `ψ^i` and reverses the bits;
scheme order reads the coefficients as they are. -/
def nttInF (L : ℕ) (ψ : F) (x : ℕ → F) : NttOrder → ℕ → F
  | .natural => fun p => ψ ^ bitRevNat L p * x (bitRevNat L p)
  | .scheme => x

theorem mod_two_mul_sub {p h : ℕ} (hh : h ≤ p % (2 * h)) :
    (p - h) % (2 * h) = p % (2 * h) - h := by
  rcases Nat.eq_zero_or_pos h with rfl | h0
  · simp
  have hd := Nat.div_add_mod p (2 * h)
  have hlt := Nat.mod_lt p (show 0 < 2 * h by omega)
  have hp : p - h = p % (2 * h) - h + p / (2 * h) * (2 * h) := by
    rw [Nat.mul_comm (p / (2 * h))]
    omega
  rw [hp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- **The natural-order stage is a butterfly stage**, its twiddle read at the offset. -/
theorem natStageF_eq_bflyF (h : ℕ) (w : ℕ → F) (A : ℕ → F) :
    natStageF h w A = bflyF h (fun q => w (q % (2 * h))) A := by
  funext p
  unfold natStageF bflyF
  split_ifs with hp
  · rfl
  · beta_reduce
    rw [mod_two_mul_sub (by omega)]

/-- **The natural-order schedule runs the natural-order stages.** -/
theorem stagesF_natural {ψ : F} {L : ℕ} :
    ∀ (r s : ℕ) (A : ℕ → F), s + r = L →
      stagesF (nttSchedF (2 ^ L) L ψ .natural) r s A =
        natStagesF (fun r => (ψ ^ 2) ^ 2 ^ (r - 1)) r (2 ^ s) A
  | 0, _, _, _ => rfl
  | r + 1, s, A, hL => by
    rw [stagesF, natStagesF, ← pow_succ', stagesF_natural r (s + 1) _ (by omega),
      natStageF_eq_bflyF]
    congr 1
    simp only [nttSchedF, nttHalf, nttTwIdx, Nat.add_sub_cancel]
    congr 1
    funext q
    have h2 : 2 ^ L / 2 ^ s = 2 * 2 ^ r := by
      rw [← hL, pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos s), pow_succ']
    rw [h2, ← pow_mul, ← pow_mul, mul_assoc]

/-! ### The scheme-order network -/

/-- **The scheme-order stage invariant**: `G` blocks of `m`; block `g` agrees with `a` wherever
`z^m = γ g`, read as the polynomial of its `m` positions. -/
def SchInv (G m : ℕ) (γ : ℕ → F) (a : F → F) (A : ℕ → F) : Prop :=
  ∀ g < G, ∀ z : F, z ^ m = γ g → ∑ t ∈ Finset.range m, A (g * m + t) * z ^ t = a z

theorem blk_div_mod {h g r : ℕ} (hr : r < 2 * h) :
    (g * (2 * h) + r) / (2 * h) = g ∧ (g * (2 * h) + r) % (2 * h) = r := by
  have h0 : 0 < 2 * h := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ h0, Nat.div_eq_of_lt hr, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- **A scheme-order stage splits each block**: where block `g` of `2h` agrees with `a` at
`z^(2h) = γ g` and `β g² = γ g`, the stage with twiddle `β` of the block puts at block `2g` the
polynomial agreeing with `a` at `z^h = β g`, and at block `2g + 1` at `z^h = −β g`. -/
theorem schStage_inv {G h : ℕ} (hh : 0 < h) {γ β : ℕ → F} {a : F → F} {A : ℕ → F}
    (hβ : ∀ g < G, β g ^ 2 = γ g) (hA : SchInv G (2 * h) γ a A) :
    SchInv (2 * G) h (fun g => if g % 2 = 0 then β (g / 2) else -β (g / 2)) a
      (bflyF h (fun q => β (q / (2 * h))) A) := by
  intro g' hg' z hz
  obtain ⟨g, b, hb, rfl⟩ : ∃ g b, b < 2 ∧ g' = 2 * g + b :=
    ⟨g' / 2, g' % 2, Nat.mod_lt _ (by norm_num), by omega⟩
  have hg : g < G := by omega
  have hdiv : (2 * g + b) / 2 = g := by omega
  have hmod : (2 * g + b) % 2 = b := by omega
  simp only [hdiv, hmod] at hz
  have hzh : z ^ h = β g ∨ z ^ h = -β g := by
    split_ifs at hz
    · exact Or.inl hz
    · exact Or.inr hz
  have hz2 : z ^ (2 * h) = γ g := by
    rw [mul_comm, pow_mul, ← hβ g hg]
    rcases hzh with e | e <;> rw [e]
    ring
  have key := hA g hg z hz2
  have hsplit : ∑ t ∈ Finset.range (2 * h), A (g * (2 * h) + t) * z ^ t =
      ∑ t ∈ Finset.range h, (A (g * (2 * h) + t) + z ^ h * A (g * (2 * h) + h + t)) * z ^ t := by
    rw [show Finset.range (2 * h) = Finset.range (h + h) by rw [two_mul], Finset.sum_range_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_add, ← add_assoc]
    ring
  rw [← key, hsplit]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · have hz : z ^ h = β g := by simpa using hz
    obtain ⟨hd, hm⟩ := blk_div_mod (g := g) (show t < 2 * h by omega)
    rw [show (2 * g + 0) * h + t = g * (2 * h) + t by ring]
    unfold bflyF
    simp only [hm, ht, ↓reduceIte]
    rw [hd, hz, show g * (2 * h) + t + h = g * (2 * h) + h + t by ring]
  · have hz : z ^ h = -β g := by simpa using hz
    obtain ⟨hd, hm⟩ := blk_div_mod (g := g) (show h + t < 2 * h by omega)
    obtain ⟨hd', -⟩ := blk_div_mod (g := g) (show t < 2 * h by omega)
    have hnt : ¬h + t < h := by omega
    rw [show (2 * g + 1) * h + t = g * (2 * h) + (h + t) by ring]
    unfold bflyF
    simp only [hm, hnt, ↓reduceIte]
    rw [show g * (2 * h) + (h + t) - h = g * (2 * h) + t by omega, hd', hz, ← add_assoc]
    ring

/-- **The block constraint after `s` scheme-order stages, `r` left**: block `g` at
`z^(2^r) = ψ^(2^r · (2·br_s(g) + 1))`. -/
def schGamma (ψ : F) (s r g : ℕ) : F := ψ ^ (2 ^ r * (2 * bitRevNat s g + 1))

theorem bitRevNat_zero_right : ∀ m, bitRevNat m 0 = 0
  | 0 => rfl
  | m + 1 => by simp [bitRevNat, bitRevNat_zero_right m]

/-- **The scheme-order twiddle's exponent**: `br_(s+1+d)(2^s + g) = 2^d · (2·br_s(g) + 1)` for
`g < 2^s`. -/
theorem bitRevNat_two_pow_add : ∀ (s d g : ℕ), g < 2 ^ s →
    bitRevNat (s + 1 + d) (2 ^ s + g) = 2 ^ d * (2 * bitRevNat s g + 1)
  | 0, d, g, hg => by
    obtain rfl : g = 0 := by simpa using hg
    rw [show 0 + 1 + d = d + 1 by omega]
    simp [bitRevNat, bitRevNat_zero_right]
  | s + 1, d, g, hg => by
    rw [show s + 1 + 1 + d = (s + 1 + d) + 1 by omega,
      show bitRevNat (s + 1 + d + 1) (2 ^ (s + 1) + g) =
        (2 ^ (s + 1) + g) % 2 * 2 ^ (s + 1 + d) + bitRevNat (s + 1 + d) ((2 ^ (s + 1) + g) / 2)
        from rfl]
    have h1 : (2 ^ (s + 1) + g) % 2 = g % 2 := by rw [pow_succ]; omega
    have h2 : (2 ^ (s + 1) + g) / 2 = 2 ^ s + g / 2 := by rw [pow_succ]; omega
    rw [h1, h2, bitRevNat_two_pow_add s d (g / 2) (by rw [pow_succ] at hg; omega),
      show bitRevNat (s + 1) g = g % 2 * 2 ^ s + bitRevNat s (g / 2) from rfl]
    ring

theorem schGamma_succ {ψ : F} {s r L : ℕ} (hL : s + 1 + r = L) (hψ : ψ ^ 2 ^ L = -1) {g : ℕ}
    (hg : g < 2 ^ (s + 1)) :
    schGamma ψ (s + 1) r g = if g % 2 = 0 then ψ ^ bitRevNat L (2 ^ s + g / 2)
      else -ψ ^ bitRevNat L (2 ^ s + g / 2) := by
  subst hL
  rw [bitRevNat_two_pow_add s r (g / 2) (by rw [pow_succ] at hg; omega)]
  unfold schGamma
  rw [show bitRevNat (s + 1) g = g % 2 * 2 ^ s + bitRevNat s (g / 2) from rfl]
  rcases Nat.mod_two_eq_zero_or_one g with h | h
  · simp only [h, eq_self, ↓reduceIte]
    congr 1
    ring
  · simp only [h, one_ne_zero, ↓reduceIte]
    rw [show 2 ^ r * (2 * (1 * 2 ^ s + bitRevNat s (g / 2)) + 1) =
      2 ^ r * (2 * bitRevNat s (g / 2) + 1) + 2 ^ (s + 1 + r) by ring, pow_add, hψ]
    ring

/-- **The scheme-order stages keep the invariant**: from the blocks after `s` stages, `r` left,
the remaining stages leave position `g` agreeing with `a` at `ψ^(2·br_L(g) + 1)`. -/
theorem schStages_inv {ψ : F} {L : ℕ} (hψ : ψ ^ 2 ^ L = -1) {a : F → F} :
    ∀ (r s : ℕ) {A : ℕ → F}, s + r = L → SchInv (2 ^ s) (2 ^ r) (schGamma ψ s r) a A →
      SchInv (2 ^ L) 1 (schGamma ψ L 0) a (stagesF (nttSchedF (2 ^ L) L ψ .scheme) r s A)
  | 0, s, A, hL, hA => by
    obtain rfl : L = s := by omega
    rw [pow_zero] at hA
    exact hA
  | r + 1, s, A, hL, hA => by
    have hr : L - s - 1 = r := by omega
    have hβ : ∀ g < 2 ^ s, (ψ ^ bitRevNat L (2 ^ s + g)) ^ 2 = schGamma ψ s (r + 1) g := by
      intro g hg
      rw [show L = s + 1 + r by omega, bitRevNat_two_pow_add s r g hg, schGamma, ← pow_mul]
      congr 1
      ring
    have h1 := schStage_inv (G := 2 ^ s) (h := 2 ^ r) (β := fun g => ψ ^ bitRevNat L (2 ^ s + g))
      (γ := schGamma ψ s (r + 1)) (Nat.two_pow_pos r) hβ (by rw [← pow_succ']; exact hA)
    have hσ : nttSchedF (2 ^ L) L ψ .scheme s =
        (2 ^ r, fun q => ψ ^ bitRevNat L (2 ^ s + q / (2 * 2 ^ r))) := by
      simp only [nttSchedF, nttHalf, nttTwIdx, hr]
    rw [stagesF, hσ]
    refine schStages_inv hψ r (s + 1) (by omega) fun g hg z hz =>
      h1 g (by rw [← pow_succ']; exact hg) z ?_
    rw [hz, schGamma_succ (by omega) hψ hg]

end Pure

section Field

variable {K : Type*} [Field K]

/-- **The natural-order network computes the transform**: twist by `ψ^i`, bit reversal on
`L` bits, the `L` stages with `ω = ψ²`, for `n = 2^L` and `ψ^n = −1`. -/
theorem nttNatural_of_stages {L n : ℕ} (hn : 2 ^ L = n) {ψ : K} (hψ : ψ ^ n = -1) (x : ℕ → K)
    {m : ℕ} (hm : m < n) :
    natStagesF (fun r => (ψ ^ 2) ^ 2 ^ (r - 1)) L 1
        (fun p => ψ ^ bitRevNat L p * x (bitRevNat L p)) m = Ops.nttNatural n ψ x m := by
  set y : List K := (List.range n).map fun i => ψ ^ i * x i with hy
  have hyl : y.length = 2 ^ L * 1 := by simp [hy, hn]
  have h0 : NatInv (splitParity L y) 1 ((ψ ^ 2) ^ 2 ^ L)
      (fun p => ψ ^ bitRevNat L p * x (bitRevNat L p)) := by
    intro g hg t ht
    obtain rfl : t = 0 := by omega
    rw [length_splitParity] at hg
    obtain ⟨hl, hv⟩ := getD_splitParity L hyl g hg
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.1 hl
    have := hv 0 (by omega)
    rw [hz] at this ⊢
    simp only [List.getD_cons_zero, zero_mul, zero_add] at this
    have hb := bitRevNat_lt L g
    rw [this, hy, List.getD_eq_getElem _ _ (by simp [hn] at hb ⊢; omega)]
    simp [hornerEval_singleton]
  have hω : ∀ r h, 2 ^ r * h = n → 0 < r → ((ψ ^ 2) ^ 2 ^ (r - 1)) ^ h = -1 := by
    intro r h hrh hr
    rw [← pow_mul, ← pow_mul, ← hψ, ← hrh]
    congr 1
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hI := natStagesF_inv hω L 1 (by rw [mul_one, hn]) h0
  have hv := hI 0 (by simp) m hm
  rw [zero_mul, zero_add] at hv
  rw [hv, Ops.nttNatural_apply n _ _ hm]
  simp only [List.getD_cons_zero]
  rw [hornerEval_eq_sum, Finset.sum_range]
  have hyl' : y.length = n := by simpa [hn] using hyl
  rw [hyl']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy, List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_map, List.getElem_range,
    ← pow_mul, ← pow_mul]
  rw [show (2 * m + 1) * (i : ℕ) = i + 2 * m * i by ring, pow_add]
  ring_nf

/-- **The natural-order schedule computes the natural-order transform.** -/
theorem nttNatural_of_stagesF {L n : ℕ} (hn : 2 ^ L = n) {ψ : K} (hψ : ψ ^ n = -1) (x : ℕ → K)
    {m : ℕ} (hm : m < n) :
    stagesF (nttSchedF n L ψ .natural) L 0 (nttInF L ψ x .natural) m = Ops.nttNatural n ψ x m := by
  subst hn
  rw [stagesF_natural L 0 _ (by omega), pow_zero]
  exact nttNatural_of_stages rfl hψ x hm

/-- **The scheme-order network computes the scheme-order transform** (`StagedNtt::forward`,
`kScheme`): the `L` stages of half-sizes `2^(L−1)`, …, `1`, block `g` of stage `s` at twiddle
`ψ^br_L(2^s + g)`, for `n = 2^L` and `ψ^n = −1`. -/
theorem nttScheme_of_stagesF {L n : ℕ} (hn : 2 ^ L = n) {ψ : K} (hψ : ψ ^ n = -1) (x : ℕ → K)
    {m : ℕ} (hm : m < n) :
    stagesF (nttSchedF n L ψ .scheme) L 0 (nttInF L ψ x .scheme) m = Ops.nttScheme n ψ x m := by
  subst hn
  have h0 : SchInv (2 ^ 0) (2 ^ L) (schGamma ψ 0 L)
      (fun z => ∑ t ∈ Finset.range (2 ^ L), x t * z ^ t) x := by
    intro g hg z _
    obtain rfl : g = 0 := by simpa using hg
    simp
  have hI := schStages_inv hψ L 0 (by omega) h0 m hm (schGamma ψ L 0 m) (pow_one _)
  simp only [Finset.sum_range_one, mul_one, add_zero, pow_zero] at hI
  show stagesF _ L 0 x m = _
  rw [hI, Ops.nttScheme_apply rfl ψ x hm, schGamma, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_zero, one_mul, ← pow_mul]

/-- **The negacyclic transform in order `o`** (`NamedOp.block` of `ntt n ψ o`). -/
def nttBy (o : NttOrder) (n : ℕ) (ψ : K) (x : ℕ → K) : ℕ → K :=
  match o with
  | .scheme => Ops.nttScheme n ψ x
  | .natural => Ops.nttNatural n ψ x

/-- **A staged transform's schedule computes its transform**, in either order. -/
theorem nttBy_of_stagesF (o : NttOrder) {L n : ℕ} (hn : 2 ^ L = n) {ψ : K} (hψ : ψ ^ n = -1)
    (x : ℕ → K) {m : ℕ} (hm : m < n) :
    stagesF (nttSchedF n L ψ o) L 0 (nttInF L ψ x o) m = nttBy o n ψ x m := by
  cases o
  · exact nttScheme_of_stagesF hn hψ x hm
  · exact nttNatural_of_stagesF hn hψ x hm

theorem nttNatural_congr_fun {n : ℕ} {ψ : K} {f g : ℕ → K} (h : ∀ t < n, f t = g t) :
    Ops.nttNatural n ψ f = Ops.nttNatural n ψ g := by
  have : Ops.toFin n f = Ops.toFin n g := funext fun i => h i i.isLt
  unfold Ops.nttNatural
  rw [this]

/-- **The transform reads its operand below `n`.** -/
theorem nttBy_congr (o : NttOrder) {n : ℕ} {ψ : K} {f g : ℕ → K} (h : ∀ t < n, f t = g t) :
    nttBy o n ψ f = nttBy o n ψ g := by
  cases o
  · funext m
    simp only [nttBy, Ops.nttScheme, nttNatural_congr_fun h]
  · exact nttNatural_congr_fun h

end Field

end GordieHowe.RealizedProgram
