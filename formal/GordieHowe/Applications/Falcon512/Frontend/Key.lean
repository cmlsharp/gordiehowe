-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Spec.KeyNTT
public import GordieHowe.Language.RealizedProgram.Ops
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9

@[expose] public section

/-!
# The Falcon key's transform is the program's scheme-order transform

The statement of a Falcon program holds the key's transform `key_hat` (`GordieHowe.Falcon512.KeyNTT.keyHat`, the
C++ forward loop `falcon_ntt_ref` with the table `falcon_ntt_zetas(512, 12289)`), and the program's
`signature.equation` reads the key through the program's inverse transform at `ψ = 10302`
(`negacyclicConv h (ntt 10302)`: `Ops.inverseNtt 512 ψ`). This file connects the two, in
`ZMod 12289`:

* the C++ forward loop at index `m` is the input polynomial's value at `ψ^(2·br₉(m) + 1)`
  (`ntt512_eq_nttScheme`: `GordieHowe.Falcon512.KeyNTT.ntt_apply_eq_sum` at the nodes of the Falcon table,
  `isNode_of_nodeExp512`, decided per index), that is the program's scheme-order transform
  `Ops.nttScheme 512 ψ` (`ofFin_falconNttRef512`);
* so the program's inverse transform of `key_hat` is the key's coefficient vector
  (`inverseNtt_keyHat`, by `Ops.inverseNtt_nttScheme`).
-/

open GordieHowe
namespace GordieHowe.Falcon512.KeyNTT
open GordieHowe.RealizedProgram

/-- **The flagship root** `ψ = 10302` in `ZMod 12289` (`falconRoot2n_512`). -/
abbrev psi512 : ZMod 12289 := 10302

/-- `ψ` is a primitive `1024`-th root of unity. -/
theorem psi512_isPrimitiveRoot : IsPrimitiveRoot psi512 (2 * 512) := by
  have h := falconRoot2n_512_isPrimitiveRoot
  rw [falconRoot2n_512] at h
  exact h

/-- `ψ^512 = −1`. -/
theorem psi512_pow_512 : psi512 ^ 512 = -1 := by
  have h := falconRoot2n_512_pow
  rw [show (2 ^ 9 : ℕ) = 512 by norm_num, falconRoot2n_512] at h
  exact h

/-- Powers of `ψ` depend on the exponent mod `1024`. -/
theorem psi512_pow_eq_of_mod {a b : ℕ} (h : a % 1024 = b % 1024) : psi512 ^ a = psi512 ^ b := by
  rw [← Nat.mod_add_div a 1024, ← Nat.mod_add_div b 1024, pow_add, pow_add, pow_mul, pow_mul,
    psi512_isPrimitiveRoot.pow_eq_one, one_pow, one_pow, h]

/-- **The Falcon table** at index `i` is `ψ^br₉(i)`. -/
theorem falconZeta512_eq {i : ℕ} : falconZeta (2 ^ 9) 12289 i = psi512 ^ falconBrv i 9 := by
  rw [falconZeta_eq, falconLog2_two_pow, show (2 ^ 9 : ℕ) = 512 by norm_num, falconRoot2n_512]
  rfl

/-- The exponent form of `IsNode (falconZeta 512 12289) 9 s g (ψ ^ E)`: at each stage the
exponents agree mod `1024`. -/
def nodeExp512 (E : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | s + 1, g =>
    decide (E * 2 ^ (9 - 1 - s) % 1024 = (512 * (g % 2) + falconBrv (2 ^ s + g / 2) 9) % 1024) &&
      nodeExp512 E s (g / 2)

/-- The exponent form gives the node. -/
theorem isNode_of_nodeExp512 {E : ℕ} :
    ∀ s g, nodeExp512 E s g = true → IsNode (falconZeta (2 ^ 9) 12289) 9 s g (psi512 ^ E)
  | 0, _, _ => trivial
  | s + 1, g, h => by
    simp only [nodeExp512, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hexp, hrest⟩ := h
    refine ⟨?_, isNode_of_nodeExp512 s (g / 2) hrest⟩
    rw [← pow_mul, falconZeta512_eq, ← psi512_pow_512, ← pow_mul, ← pow_add]
    exact psi512_pow_eq_of_mod hexp

/-- Index `k` of the C++ forward loop with the Falcon table sits at `ψ^(2·br₉(k) + 1)`. -/
theorem nodeExp512_spec : ∀ k < 512, nodeExp512 (2 * bitRevNat 9 k + 1) 9 k = true := by
  decide +kernel

/-- **The C++ forward loop is the program's scheme-order transform** at `ψ`, below `512`. -/
theorem ntt512_eq_nttScheme (c : Fin 512 → ℕ) {m : ℕ} (hm : m < 512) :
    ntt (falconZeta (2 ^ 9) 12289) (2 ^ 9) (extend 12289 c) m =
      Ops.nttScheme 512 psi512 (Ops.ofFin fun i => (c i : ZMod 12289)) m := by
  rw [ntt_apply_eq_sum (show m < 2 ^ 9 by norm_num; exact hm)
    (isNode_of_nodeExp512 9 m (nodeExp512_spec m hm)),
    Ops.nttScheme_apply (k := 9) (by norm_num) _ _ hm,
    show (2 ^ 9 : ℕ) = 512 by norm_num, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [extend, dite_eq_left i.isLt, Ops.ofFin_of_lt _ i.isLt, ← pow_mul]


/-- **`falcon_ntt_ref` is the program's scheme-order transform** at `ψ`, read in `ZMod 12289`. -/
theorem ofFin_falconNttRef512 (c : Fin 512 → ℕ) :
    Ops.ofFin (fun i => (falconNttRef 512 12289 c i : ZMod 12289)) =
      Ops.nttScheme 512 psi512 (Ops.ofFin fun i => (c i : ZMod 12289)) := by
  funext m
  by_cases hm : m < 512
  · rw [Ops.ofFin_of_lt _ hm, falconNttRef, ZMod.natCast_zmod_val]
    exact ntt512_eq_nttScheme c hm
  · rw [Ops.ofFin, dite_eq_right hm, Ops.nttScheme, ite_eq_right hm]

/-- **The program's inverse transform inverts `falcon_ntt_ref`.** -/
theorem inverseNtt_falconNttRef512 (c : Fin 512 → ℕ) {i : ℕ} (hi : i < 512) :
    Ops.inverseNtt 512 psi512 (Ops.ofFin fun j => (falconNttRef 512 12289 c j : ZMod 12289)) i =
      (c ⟨i, hi⟩ : ZMod 12289) := by
  rw [ofFin_falconNttRef512, Ops.inverseNtt_nttScheme (k := 9) (by norm_num) psi512_isPrimitiveRoot
    (by decide) _ hi, Ops.ofFin_of_lt _ hi]

/-- **The program's inverse transform of `key_hat` is the key** (`signature.equation`'s spectrum
`ntt 10302` at the statement `keyHat pk`). -/
theorem inverseNtt_keyHat (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512) {i : ℕ}
    (hi : i < 512) :
    Ops.inverseNtt 512 psi512 (Ops.ofFin fun j => (keyHat pk j : ZMod 12289)) i =
      Falcon512.coeff pk.h ⟨i, hi⟩ := by
  rw [keyHat, inverseNtt_falconNttRef512 _ hi]
  exact ZMod.natCast_zmod_val (n := 12289) _

end GordieHowe.Falcon512.KeyNTT
