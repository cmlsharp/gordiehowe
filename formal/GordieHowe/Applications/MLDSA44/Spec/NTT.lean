-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.MLDSA.Concrete.NTT
import all LatticeCrypto.MLDSA.Concrete.NTT

/-!
# The vendored ML-DSA NTT is evaluation at the odd powers of `ζ`

`MLDSA.Concrete.ntt` (FIPS 204 Algorithm 41, vendored in
`Vendor/LatticeCrypto/MLDSA/Concrete/NTT.lean`) is built from eight butterfly stages whose
`k`-th twiddle is `ζ^brv8(k)`, `ζ = 1753`. This file proves that its output coefficient `k` is
the evaluation of the input polynomial at `ζ^(2·brv8(k) + 1)` (`ntt_get`). The native ML-DSA A
circuit gives `Â` to `native_linear::Relation` in this form (`PublicForm::kNtt`,
`lib/circuits/ntt/native_linear.h`: "NTT inputs are evaluations at `root^(2*bitreverse(k)+1)`").

This is a Lean module so that it can `import all` the vendored file: its stage definitions
(`nttStage`, `nttCoeffs`, `layerLayout`, `getZ_zetaTable`) are private there.

Proof: after `s` stages, the block `g` of length `B = 256 / 2^s` holds the coefficients of a
polynomial that agrees with the input at every `x` with `x^B = ζ^(r s g)`, where
`r 0 0 = 256` and `r (s+1) g = brv8(2^s + g/2) + 256·(g mod 2)`. A butterfly with twiddle
`z` splits the block into its values at `x^(B/2) = z` and `x^(B/2) = -z`. After eight stages
the blocks have length one and `r 8 g ≡ 2·brv8(g) + 1 (mod 512)`.
-/

namespace GordieHowe.MLDSA44.NTTEval

open _root_.MLDSA _root_.MLDSA.Concrete

/-- The exponent of the block condition `x^B = ζ^(r s g)` after `s` stages. -/
def blockExp (s g : ℕ) : ℕ :=
  if s = 0 then 256 else bitRev8 (2 ^ (s - 1) + g / 2) + 256 * (g % 2)

/-- Each twiddle squares to its block's condition: `ζ^(2·brv8(2^s + g)) = ζ^(r s g)`. -/
theorem two_mul_bitRev8_mod (s : Fin 8) (g : Fin (2 ^ s.val)) :
    (2 * bitRev8 (2 ^ s.val + g.val)) % 512 = blockExp s.val g.val % 512 := by
  revert s g
  decide +kernel

/-- After eight stages the block conditions are the odd powers `ζ^(2·brv8(g) + 1)`. -/
theorem blockExp_eight_mod (g : Fin 256) :
    blockExp 8 g.val % 512 = (2 * bitRev8 g.val + 1) % 512 := by
  revert g
  decide +kernel

theorem zeta_pow_512 : (zeta : Coeff) ^ 512 = 1 := zeta_isPrimitiveRoot.pow_eq_one

theorem zeta_pow_eq_of_mod {a b : ℕ} (h : a % 512 = b % 512) :
    (zeta : Coeff) ^ a = zeta ^ b := by
  rw [← Nat.mod_add_div a 512, ← Nat.mod_add_div b 512, pow_add, pow_add, pow_mul, pow_mul,
    zeta_pow_512, one_pow, one_pow, h]

theorem zeta_pow_256 : (zeta : Coeff) ^ 256 = -1 := by
  change (1753 : ZMod 8380417) ^ 256 = -1
  reduce_mod_char

/-- A coefficient function read at a natural index, zero past the end. -/
def ext (v : Fin polyBackend.degree → Coeff) (i : ℕ) : Coeff := if h : i < 256 then v ⟨i, h⟩ else 0

/-- The polynomial held in positions `[base, base + len)`, evaluated at `x`. -/
def ev (v : Fin polyBackend.degree → Coeff) (base len : ℕ) (x : Coeff) : Coeff :=
  ∑ i ∈ Finset.range len, ext v (base + i) * x ^ i

theorem ext_of_val {v : Fin polyBackend.degree → Coeff} {c : Fin polyBackend.degree} {i : ℕ} (h : c.val = i) :
    ext v i = v c := by
  subst h
  have hc : (c : ℕ) < 256 := c.isLt
  rw [ext, dite_eq_left_of_eq_true (eq_true hc)]

/-- A block splits into its two halves. -/
theorem ev_split (v : Fin polyBackend.degree → Coeff) (base L : ℕ) (x : Coeff) :
    ev v base (2 * L) x = ev v base L x + x ^ L * ev v (base + L) L x := by
  unfold ev
  rw [two_mul, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add, ← add_assoc]
  ring

theorem layerLayout_left_val (s : Fin 8) (g : Fin (2 ^ s.val))
    (o : Fin (128 / 2 ^ s.val)) :
    ((layerLayout s).equiv ((g, o), false)).val = g.val * (2 * (128 / 2 ^ s.val)) + o.val := by
  simp [layerLayout]

theorem layerLayout_right_val (s : Fin 8) (g : Fin (2 ^ s.val))
    (o : Fin (128 / 2 ^ s.val)) :
    ((layerLayout s).equiv ((g, o), true)).val =
      g.val * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + o.val := by
  simp [layerLayout]

theorem stage_left (s : Fin 8) (v : Fin polyBackend.degree → Coeff) (g : Fin (2 ^ s.val))
    (o : Fin (128 / 2 ^ s.val)) :
    (nttStage s).forward v ((layerLayout s).equiv ((g, o), false)) =
      v ((layerLayout s).equiv ((g, o), false)) +
        zeta ^ bitRev8 (2 ^ s.val + g.val) * v ((layerLayout s).equiv ((g, o), true)) := by
  have hz := getZ_zetaTable (2 ^ s.val + g.val) (layer_twiddle_index_bounds s g).1
  simp [nttStage, LatticeCrypto.NTTCert.butterflyStage, LatticeCrypto.NTTCert.forwardStage,
    LatticeCrypto.NTTCert.forwardButterfly, hz]

theorem stage_right (s : Fin 8) (v : Fin polyBackend.degree → Coeff) (g : Fin (2 ^ s.val))
    (o : Fin (128 / 2 ^ s.val)) :
    (nttStage s).forward v ((layerLayout s).equiv ((g, o), true)) =
      v ((layerLayout s).equiv ((g, o), false)) -
        zeta ^ bitRev8 (2 ^ s.val + g.val) * v ((layerLayout s).equiv ((g, o), true)) := by
  have hz := getZ_zetaTable (2 ^ s.val + g.val) (layer_twiddle_index_bounds s g).1
  simp [nttStage, LatticeCrypto.NTTCert.butterflyStage, LatticeCrypto.NTTCert.forwardStage,
    LatticeCrypto.NTTCert.forwardButterfly, hz]

/-- The left half after stage `s`: `u + z·v`. -/
theorem ev_stage_left (s : Fin 8) (v : Fin polyBackend.degree → Coeff) {g : ℕ} (hg : g < 2 ^ s.val)
    (x : Coeff) :
    ev ((nttStage s).forward v) (g * (2 * (128 / 2 ^ s.val))) (128 / 2 ^ s.val) x =
      ev v (g * (2 * (128 / 2 ^ s.val))) (128 / 2 ^ s.val) x +
        zeta ^ bitRev8 (2 ^ s.val + g) *
          ev v (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val) (128 / 2 ^ s.val) x := by
  unfold ev
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o ho => ?_
  have ho' : o < 128 / 2 ^ s.val := Finset.mem_range.mp ho
  have hl : ((layerLayout s).equiv ((⟨g, hg⟩, ⟨o, ho'⟩), false)).val =
      g * (2 * (128 / 2 ^ s.val)) + o := layerLayout_left_val s ⟨g, hg⟩ ⟨o, ho'⟩
  have hr : ((layerLayout s).equiv ((⟨g, hg⟩, ⟨o, ho'⟩), true)).val =
      g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + o := layerLayout_right_val s ⟨g, hg⟩ ⟨o, ho'⟩
  rw [ext_of_val hl, ext_of_val hl, ext_of_val hr, stage_left s v ⟨g, hg⟩ ⟨o, ho'⟩]
  ring

/-- The right half after stage `s`: `u - z·v`. -/
theorem ev_stage_right (s : Fin 8) (v : Fin polyBackend.degree → Coeff) {g : ℕ} (hg : g < 2 ^ s.val)
    (x : Coeff) :
    ev ((nttStage s).forward v) (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val)
        (128 / 2 ^ s.val) x =
      ev v (g * (2 * (128 / 2 ^ s.val))) (128 / 2 ^ s.val) x -
        zeta ^ bitRev8 (2 ^ s.val + g) *
          ev v (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val) (128 / 2 ^ s.val) x := by
  unfold ev
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun o ho => ?_
  have ho' : o < 128 / 2 ^ s.val := Finset.mem_range.mp ho
  have hl : ((layerLayout s).equiv ((⟨g, hg⟩, ⟨o, ho'⟩), false)).val =
      g * (2 * (128 / 2 ^ s.val)) + o := layerLayout_left_val s ⟨g, hg⟩ ⟨o, ho'⟩
  have hr : ((layerLayout s).equiv ((⟨g, hg⟩, ⟨o, ho'⟩), true)).val =
      g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + o := layerLayout_right_val s ⟨g, hg⟩ ⟨o, ho'⟩
  rw [ext_of_val hl, ext_of_val hr, ext_of_val hr, stage_right s v ⟨g, hg⟩ ⟨o, ho'⟩]
  ring

/-- The block invariant after `s` stages. -/
def Inv (f : Fin polyBackend.degree → Coeff) (s : ℕ) (v : Fin polyBackend.degree → Coeff) : Prop :=
  ∀ g < 2 ^ s, ∀ x : Coeff, x ^ (256 / 2 ^ s) = zeta ^ blockExp s g →
    ev v (g * (256 / 2 ^ s)) (256 / 2 ^ s) x = ev f 0 256 x

theorem inv_zero (f : Fin polyBackend.degree → Coeff) : Inv f 0 f := by
  intro g hg x _
  have : g = 0 := by simpa using hg
  subst this
  simp

theorem half_eq (s : Fin 8) : 256 / 2 ^ s.val = 2 * (128 / 2 ^ s.val) := by
  revert s
  decide

theorem half_succ_eq (s : Fin 8) : 256 / 2 ^ (s.val + 1) = 128 / 2 ^ s.val := by
  revert s
  decide

theorem inv_succ (f : Fin polyBackend.degree → Coeff) (s : Fin 8) {v : Fin polyBackend.degree → Coeff}
    (hv : Inv f s.val v) : Inv f (s.val + 1) ((nttStage s).forward v) := by
  intro g' hg' x hx
  set L := 128 / 2 ^ s.val with hL
  have hg : g' / 2 < 2 ^ s.val := by
    rw [pow_succ] at hg'
    omega
  have hexp : blockExp (s.val + 1) g' = bitRev8 (2 ^ s.val + g' / 2) + 256 * (g' % 2) := by
    simp [blockExp]
  rw [half_succ_eq, hexp] at hx
  rw [half_succ_eq]
  -- the parent block's condition
  have hparent : x ^ (256 / 2 ^ s.val) = zeta ^ blockExp s.val (g' / 2) := by
    rw [half_eq, mul_comm, pow_mul, hx, ← pow_mul,
      zeta_pow_eq_of_mod (b := 2 * bitRev8 (2 ^ s.val + g' / 2))]
    · exact zeta_pow_eq_of_mod (two_mul_bitRev8_mod s ⟨g' / 2, hg⟩)
    · rcases Nat.mod_two_eq_zero_or_one g' with h | h <;> rw [h] <;> omega
  have hsplit := hv (g' / 2) hg x hparent
  rw [half_eq, ev_split] at hsplit
  have hdecomp : g' * L = g' / 2 * (2 * L) + g' % 2 * L := by
    conv_lhs => rw [← Nat.div_add_mod g' 2]
    ring
  rcases Nat.mod_two_eq_zero_or_one g' with h | h
  · rw [h, zero_mul, add_zero] at hdecomp
    rw [h, mul_zero, add_zero] at hx
    rw [hdecomp, ev_stage_left s v hg, ← hx, hsplit]
  · rw [h, one_mul] at hdecomp
    rw [h, mul_one, pow_add, zeta_pow_256] at hx
    rw [hdecomp, ev_stage_right s v hg, ← hsplit]
    have hz : zeta ^ bitRev8 (2 ^ s.val + g' / 2) = -x ^ L := by
      rw [hx]; ring
    rw [hz]
    ring

/-- The invariant after all eight stages. -/
theorem inv_nttCoeffs (f : Fin polyBackend.degree → Coeff) : Inv f 8 (nttCoeffs f) :=
  inv_succ f 7 <| inv_succ f 6 <| inv_succ f 5 <| inv_succ f 4 <| inv_succ f 3 <|
    inv_succ f 2 <| inv_succ f 1 <| inv_succ f 0 <| inv_zero f

/-- **The vendored ML-DSA NTT is evaluation at odd powers of `ζ`.** Coefficient `k` of
`ntt f` is `Σ_j f_j · ζ^((2·brv8(k) + 1)·j)`, the value of `f` at `ζ^(2·brv8(k) + 1)`. -/
public theorem ntt_get (f : Rq) (k : Fin ringDegree) :
    (ntt f).coeffs.get k = ∑ j : Fin ringDegree, f.get j * zeta ^ ((2 * bitRev8 k + 1) * j) := by
  have hc : (ntt f).coeffs.get k = nttCoeffs (fun i => f.get i) k := by
    change (Vector.ofFn (nttCoeffs (fun i => f.get i))).get k = _
    exact Vector.get_ofFn _ k
  rw [hc]
  have h := inv_nttCoeffs (fun i => f.get i) k.val k.isLt (zeta ^ blockExp 8 k.val)
    (by simp)
  have h1 : (256 / 2 ^ 8 : ℕ) = 1 := by norm_num
  rw [h1] at h
  simp only [ev, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, mul_one,
    add_zero, zero_add] at h
  rw [ext_of_val (c := k) rfl] at h
  rw [h, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ext_of_val (c := j) rfl, ← pow_mul]
  rw [zeta_pow_eq_of_mod (b := (2 * bitRev8 k + 1) * j)
    (by rw [Nat.mul_mod, blockExp_eight_mod k, ← Nat.mul_mod])]

end GordieHowe.MLDSA44.NTTEval
