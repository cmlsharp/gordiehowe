-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Spec.KeyNTT
public import GordieHowe.Applications.MLDSA44.Spec.NTT
public import Mathlib.Tactic.ReduceModChar
import all LatticeCrypto.MLDSA.Concrete.NTT
import all LatticeCrypto.MLDSA.Params

@[expose] public section

/-!
# ML-DSA public-key decoding in the emulated arm

The emulated ML-DSA-44 arm (`signature_relation` in `lib/gordiehowe/examples/mldsa/mldsa_emulated.h`)
reads `ExpandA(ρ)` in coefficient form: `mldsa_key_of` with `ops::Form::kCoefficients` computes
`expand_a_coefficients` (`lib/gordiehowe/examples/mldsa/mldsa_gadgets.h`), which applies `intt` to each
NTT-form entry `Â_ij`, given as naturals below `q`. `intt` is the compile-time-modulus
`falcon_intt_ref<kQ>` (`lib/schemes/falcon/falcon_ntt.h`) with the twiddle table
`ml_dsa::kZetas`, the same loops as the runtime `falcon_intt_ref` (`falcon_ntt.h:93-110`).

So the decode is public preprocessing, on the host, over naturals below `q = 8380417`: each C++
assignment stores `x % q`. The Goldilocks carrier field enters only afterwards, when the decoded
naturals are embedded with `of_scalar`. It is modelled here.

## Transcription

`falcon_intt_ref` is transcribed once, generically, as `GordieHowe.Falcon512.KeyNTT.intt` over `ZMod q` (see
that file for the loop-by-loop reading). The ML-DSA arguments are `n = a.size() = 256 = 2 ^ 8`, the
twiddle table `ml_dsa::kZetas` (`lib/circuits/tests/pq/ml_dsa/ml_dsa_shared.h`) and
`ninv = 256⁻¹ mod q`, which `falcon_intt_ref<kQ>` computes as `q - (q - 1) / 256`
(`falcon_ntt.h:157`) and the runtime loop as `falcon_powmod(256 % q, q - 2, q)` (`falcon_ntt.h:108`,
`GordieHowe.Falcon512.KeyNTT.falconNinv`). The inverse reads `zetas[255]` down to `zetas[1]`;
`kZetas[i] = 1753 ^ brv8(i) mod q`, which is the vendored `zetaTable`.

## Results

`GordieHowe.Falcon512.KeyNTT.ntt_apply_eq_sum` states that the C++ forward loop `falcon_ntt_ref`, for any
twiddle table, returns at index `g` the input polynomial's value at every point on the path
`IsNode` of block `g`. With the ML-DSA table the point for index `k` is `ζ ^ (2·brv8(k) + 1)`,
which is where `GordieHowe.MLDSA44.NTTEval.ntt_get` puts the vendored `ntt`'s coefficient `k`. The naturals
the C++ holds are the canonical representatives `vals` (`vals_lt`).

## Conventions

The C++ forward and inverse loops are FIPS 204 Algorithms 41 and 42: the inverse's
`z = q - zetas[--k]` with `k` from `256` is Algorithm 42's `z ← −zetas[m]` after `m ← m − 1`,
and the final scaling multiplies by `256⁻¹ mod q`. The decoded vector is in natural
coefficient order and the input in the vendored bit-reversed NTT order; there is no further
permutation or Montgomery factor.
-/

namespace GordieHowe.Falcon512.KeyNTT

/-! ## The forward loop is evaluation -/

section Eval

variable {R : Type*} [CommRing R]

/-- The polynomial held in positions `[base, base + len)` of a working array, evaluated
at `x`. -/
def blockEval (a : ℕ → R) (base len : ℕ) (x : R) : R :=
  ∑ i ∈ Finset.range len, a (base + i) * x ^ i

/-- A block of length `2 · len` is its low half plus `x ^ len` times its high half. -/
theorem blockEval_two_mul (a : ℕ → R) (base len : ℕ) (x : R) :
    blockEval a base (2 * len) x =
      blockEval a base len x + x ^ len * blockEval a (base + len) len x := by
  unfold blockEval
  rw [two_mul, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add, ← add_assoc]
  ring

theorem blockEval_one (a : ℕ → R) (base : ℕ) (x : R) : blockEval a base 1 x = a base := by
  simp [blockEval]

/-- The low half of block `b` after a forward stage: `u + z·v`. -/
theorem blockEval_fwd_low {ζ : ℕ → R} {len m k b : ℕ} (hb : b < m) (a : ℕ → R) (x : R) :
    blockEval (blockLoop ζ (· + 1) fwdF fwdG len k 0 m a) (2 * len * b) len x =
      blockEval a (2 * len * b) len x + ζ (k + b) * blockEval a (2 * len * b + len) len x := by
  unfold blockEval
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [blockLoop_low_zero hb hr, iterate_add_one, fwdF,
    show 2 * len * b + len + r = 2 * len * b + r + len by omega]
  ring

/-- The high half of block `b` after a forward stage: `u - z·v`. -/
theorem blockEval_fwd_high {ζ : ℕ → R} {len m k b : ℕ} (hb : b < m) (a : ℕ → R) (x : R) :
    blockEval (blockLoop ζ (· + 1) fwdF fwdG len k 0 m a) (2 * len * b + len) len x =
      blockEval a (2 * len * b) len x - ζ (k + b) * blockEval a (2 * len * b + len) len x := by
  unfold blockEval
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [show 2 * len * b + len + r = 2 * len * b + r + len by omega, blockLoop_high_zero hb hr,
    iterate_add_one, fwdG]
  ring

/-- The points at which block `g` holds the input polynomial's value after `s` forward stages
of a transform of length `2 ^ L`. Stage `s` splits block `g / 2` with the twiddle
`ζ (2 ^ s + g / 2)`; its low half (`g` even) keeps the points with
`x ^ (2 ^ (L - 1 - s)) = ζ (2 ^ s + g / 2)` and its high half those with
`x ^ (2 ^ (L - 1 - s)) = -ζ (2 ^ s + g / 2)`. -/
def IsNode (ζ : ℕ → R) (L : ℕ) : ℕ → ℕ → R → Prop
  | 0, _, _ => True
  | s + 1, g, x =>
    x ^ 2 ^ (L - 1 - s) = (-1) ^ (g % 2) * ζ (2 ^ s + g / 2) ∧ IsNode ζ L s (g / 2) x

/-- The invariant of the forward loop after `s` stages: every block holds, at each of its
points, the value of the input polynomial. -/
def EvalInv (ζ : ℕ → R) (L : ℕ) (a : ℕ → R) (s : ℕ) (v : ℕ → R) : Prop :=
  ∀ g < 2 ^ s, ∀ x, IsNode ζ L s g x →
    blockEval v (g * 2 ^ (L - s)) (2 ^ (L - s)) x = blockEval a 0 (2 ^ L) x

theorem evalInv_zero (ζ : ℕ → R) (L : ℕ) (a : ℕ → R) : EvalInv ζ L a 0 a := by
  intro g hg x _
  obtain rfl : g = 0 := by simpa using hg
  simp

theorem EvalInv.fwdStage {ζ : ℕ → R} {L : ℕ} {a : ℕ → R} {s : ℕ} (hs : s < L) {v : ℕ → R}
    (hv : EvalInv ζ L a s v) : EvalInv ζ L a (s + 1) (KeyNTT.fwdStage ζ L (L - 1 - s) v) := by
  intro g hg x hx
  obtain ⟨hpt, hnode⟩ := hx
  set len := 2 ^ (L - 1 - s) with hlen
  have hb : g / 2 < 2 ^ s := by
    rw [pow_succ] at hg
    omega
  have hL : 2 ^ (L - s) = 2 * len := by
    rw [hlen, ← pow_succ', show L - 1 - s + 1 = L - s by omega]
  have hparent := hv (g / 2) hb x hnode
  rw [hL, _root_.mul_comm (g / 2), blockEval_two_mul] at hparent
  rw [Falcon512.KeyNTT.fwdStage, show L - 1 - (L - 1 - s) = s by omega,
    show L - (s + 1) = L - 1 - s by omega, ← hlen]
  have hdecomp : g * len = 2 * len * (g / 2) + g % 2 * len := by
    conv_lhs => rw [← Nat.div_add_mod g 2]
    ring
  rcases Nat.mod_two_eq_zero_or_one g with h | h
  · rw [h, pow_zero, one_mul] at hpt
    rw [hdecomp, h, zero_mul, add_zero, blockEval_fwd_low hb, ← hparent, hpt]
  · rw [h, pow_one, neg_one_mul] at hpt
    rw [hdecomp, h, one_mul, blockEval_fwd_high hb, ← hparent, hpt]
    ring

theorem evalInv_fwdRange (ζ : ℕ → R) (L : ℕ) (a : ℕ → R) :
    ∀ c ≤ L, EvalInv ζ L a c (fwdRange ζ L (L - c) c a)
  | 0, _ => by
    rw [Nat.sub_zero]
    exact evalInv_zero ζ L a
  | c + 1, hc => by
    rw [fwdRange_succ', show L - (c + 1) + 1 = L - c by omega,
      show L - (c + 1) = L - 1 - c by omega]
    exact (evalInv_fwdRange ζ L a c (by omega)).fwdStage (by omega)

/-- **The forward loop is evaluation.** For any twiddle table `ζ`, entry `g` of
`falcon_ntt_ref` (`falcon_ntt.h:74-91`) on an input of length `2 ^ L` is the input
polynomial's value at every point `x` on block `g`'s path `IsNode ζ L L g`. -/
theorem ntt_apply_eq_sum {ζ : ℕ → R} {L g : ℕ} (hg : g < 2 ^ L) {x : R}
    (hx : IsNode ζ L L g x) (a : ℕ → R) :
    ntt ζ (2 ^ L) a g = ∑ i ∈ Finset.range (2 ^ L), a i * x ^ i := by
  have h := evalInv_fwdRange ζ L a L le_rfl g hg x hx
  rw [Nat.sub_self, pow_zero, mul_one, blockEval_one] at h
  rw [ntt_eq, h]
  simp [blockEval]

end Eval

end GordieHowe.Falcon512.KeyNTT

namespace GordieHowe.MLDSA44.KeyNTT

open _root_.MLDSA _root_.MLDSA.Concrete

/-! ## Canonical representatives -/

/-- The canonical representatives in `[0, q)` of a vendored polynomial's coefficients: the
naturals the C++ holds. -/
def vals (f : Rq) : Fin 256 → ℕ := fun i => (f.get i).val

theorem vals_lt (f : Rq) (i : Fin 256) : vals f i < modulus := ZMod.val_lt _

end GordieHowe.MLDSA44.KeyNTT
