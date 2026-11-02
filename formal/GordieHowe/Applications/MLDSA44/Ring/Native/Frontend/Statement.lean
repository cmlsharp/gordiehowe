-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Scheme
public import GordieHowe.Applications.MLDSA44.Native.Rows
public import GordieHowe.Language.Library.Eval

@[expose] public section

/-!
# GordieHowe frontend: the statement of the native ML-DSA-44 ring programs

The statement values of the native ML-DSA-44 ring programs (`ring_rows` in
`lib/gordiehowe/examples/rings/mldsa_ring.h`, `ring_host::native_key_row` and
`ring_host::mu_limbs` in `lib/gordiehowe/examples/rings/mldsa_ring_host.h`) as functions of a ring
statement `(R, M′, ())` (`GordieHowe.MLDSA44.Ring.RStmt`): each is an opaque statement value of
no argument, supplied by the verifier's statement map.

* **A key's row** (`keyEntry`, `5120` naturals below `q`): `Â = ExpandA(ρ)` in FIPS 204's NTT
  order (`(i, j, k)` row-major, the bounded `MLDSA44.expandABounded`, `aHatNat`), then
  `NTT(2^d · t1_i)` (`t1HatNat`).
* **A member's `μ` limbs** (`muLimb`, `24` naturals below `2^22`): bit `i` of `μ` (bit `i mod 8`
  of byte `⌊i/8⌋`, `muBitNat`) is bit `i mod 22` of limb `⌊i/22⌋`, the last limb zero-extended,
  with `μ = H(tr ‖ M′)` (FIPS 204 Algorithm 7, line 6, `muOf`).
* **The program's statement** (`stmtOf`): row `j` of `ring.keys` the row of the key at position
  `j` (`RingStmt.keyAt`, the default key past the ring's end), row `j` of `ring.mu` its `μ`
  limbs, every other coordinate `0`. `ring.tr` (the members' `tr`, domain `H`, which the
  verifier's map fills with `tr_j`) is left `0`: the frontend's relation reads the statement only
  through `ring.keys` and `ring.mu` (`RowsOf`).
* **The statement holds a ring's rows** (`RowsOf`), the hypothesis of the frontend's relation;
  `rowsOf_stmtOf`: the program's statement holds them.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Ring

/-! ## A key's row and a member's `μ` -/

/-- **Entry `(i, j, k)` of `Â`** of a key, `ExpandA(ρ)` within the byte budget
(`MLDSA44.expandABounded`, the C++ `expand_a_fast`), as a natural below `q`. -/
def aHatNat (pk : PublicKey) (i j : Fin 4) (k : Fin 256) : ℕ :=
  ((((MLDSA44.expandABounded _root_.MLDSA.mldsa44 pk.rho).get i).get j).coeffs.get k).val

/-- **Entry `(i, k)` of `NTT(2^d · t1)`** of a key (FIPS 204 Algorithm 8, line 9's
`NTT(t1 · 2^d)`), as a natural below `q`. -/
def t1HatNat (pk : PublicKey) (i : Fin 4) (k : Fin 256) : ℕ :=
  ((_root_.MLDSA.Concrete.ntt (Native.Rows.prims.power2RoundShift (pk.t1.get i))).coeffs.get k).val

/-- **Entry `s` of a key's row** (`ring_host::native_key_row`): `Â` at `s = (4 i + j) · 256 + k`,
then `NTT(2^d · t1)` at `s = 4096 + 256 i + k`, `0` past `5120`. -/
def keyEntry (pk : PublicKey) (s : ℕ) : ℕ :=
  if h : s < 4096 then aHatNat pk ⟨s / 1024, by omega⟩ ⟨s / 256 % 4, by omega⟩ ⟨s % 256, by omega⟩
  else if h' : s < 5120 then t1HatNat pk ⟨(s - 4096) / 256, by omega⟩ ⟨(s - 4096) % 256, by omega⟩
  else 0

theorem keyEntry_aHat (pk : PublicKey) (i j : Fin 4) (k : Fin 256) :
    keyEntry pk (((i : ℕ) * 4 + j) * 256 + k) = aHatNat pk i j k := by
  have hi := i.isLt; have hj := j.isLt; have hk := k.isLt
  unfold keyEntry
  rw [dif_pos (by omega)]
  congr 1 <;> apply Fin.ext <;> simp only <;> omega

theorem keyEntry_t1 (pk : PublicKey) (i : Fin 4) (k : Fin 256) :
    keyEntry pk (4096 + ((i : ℕ) * 256 + k)) = t1HatNat pk i k := by
  have hi := i.isLt; have hk := k.isLt
  unfold keyEntry
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg₂ (t1HatNat pk) (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

/-- **A key's row lies below `q`.** -/
theorem keyEntry_lt (pk : PublicKey) (s : ℕ) : keyEntry pk s < 8380417 := by
  unfold keyEntry aHatNat t1HatNat
  split_ifs
  · exact lt_of_lt_of_eq (ZMod.val_lt _) rfl
  · exact lt_of_lt_of_eq (ZMod.val_lt _) rfl
  · exact Nat.zero_lt_succ _

/-- **`μ` of a key and a message representative** (FIPS 204 Algorithm 7, line 6, and
Algorithm 8, line 7): `H(H(pk) ‖ M′, 64)`, `H(pk)` the vendored `hashPublicKey` of `(ρ, t1)`. -/
def muOf {len : ℕ} (pk : PublicKey) (m : _root_.MLDSA.Bytes len) : _root_.MLDSA.Bytes 64 :=
  _root_.MLDSA.Concrete.hashMessage (Native.Rows.prims.hashPublicKey pk.rho pk.t1) m.toList

/-- **Bit `t` of `μ`** (bit `t mod 8` of byte `⌊t/8⌋`, the C++ `mu_limbs`' order), `0` past
`512`. -/
def muBitNat (mu : _root_.MLDSA.Bytes 64) (t : ℕ) : ℕ :=
  if h : t < 512 then (mu.get ⟨t / 8, by omega⟩).toNat / 2 ^ (t % 8) % 2 else 0

theorem muBitNat_le (mu : _root_.MLDSA.Bytes 64) (t : ℕ) : muBitNat mu t ≤ 1 := by
  unfold muBitNat
  split_ifs
  · exact Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  · norm_num

/-- **Limb `l` of `μ`** (`ring_host::mu_limbs`, `22` bits, least significant first). -/
def muLimb (mu : _root_.MLDSA.Bytes 64) (l : ℕ) : ℕ :=
  ∑ b : Fin 22, muBitNat mu (22 * l + b) * 2 ^ (b : ℕ)

/-- **A sum of bits weighted by powers of two** lies below `2^n`. -/
theorem sum_bits_lt : ∀ {n : ℕ} (a : Fin n → ℕ), (∀ b, a b ≤ 1) →
    ∑ b : Fin n, a b * 2 ^ (b : ℕ) < 2 ^ n
  | 0, _, _ => by simp
  | n + 1, a, ha => by
    rw [Fin.sum_univ_castSucc]
    have ih := sum_bits_lt (fun b : Fin n => a b.castSucc) fun b => ha _
    have hl := ha (Fin.last n)
    simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
    have : a (Fin.last n) * 2 ^ n ≤ 2 ^ n := by
      simpa using Nat.mul_le_mul_right (2 ^ n) hl
    rw [pow_succ]
    omega

/-- **A limb lies below `2^22`.** -/
theorem muLimb_lt (mu : _root_.MLDSA.Bytes 64) (l : ℕ) : muLimb mu l < 2 ^ 22 :=
  sum_bits_lt _ fun _ => muBitNat_le _ _

/-! ## The program's statement -/

/-- **The statement values of a native ML-DSA-44 ring program** (decided per program):
`ring.keys` and `ring.mu`, opaque statement values of no argument of field `0`. -/
class MldsaRingStmt (program : RealizedProgram) where
  /-- `ring.keys`. -/
  keys : ℕ
  /-- `ring.mu`. -/
  mu : ℕ
  /-- `ring.keys` is an opaque statement value of no argument. -/
  keysKind : (program.value keys).kind = .pub (.opaque "ring.keys" [])
  /-- `ring.mu` is an opaque statement value of no argument. -/
  muKind : (program.value mu).kind = .pub (.opaque "ring.mu" [])
  /-- Both are of field `0`. -/
  fields : program.valueField keys = 0 ∧ program.valueField mu = 0
  /-- They differ. -/
  keys_ne : keys ≠ mu

variable {program : RealizedProgram} [MldsaRingStmt program] {I : RealizedProgram.Interp}
  {len : ℕ}

set_option hygiene false in
local notation "vK" => MldsaRingStmt.keys program

set_option hygiene false in
local notation "vM" => MldsaRingStmt.mu program

/-- **The program's statement of a ring statement**: coordinate `5120 j + s` of `ring.keys` is
entry `s` of the row of the key at position `j`, coordinate `24 j + l` of `ring.mu` limb `l` of
its `μ`, every other coordinate `0` (`ring.tr` included). -/
def stmtOf (x : RStmt len) : program.Valuation I := fun v i =>
  if v = vK then
    RealizedProgram.castElt (a := 0) ((keyEntry (x.keyAt (i / 5120)) (i % 5120) : ℕ) : (I 0).K)
  else if v = vM then
    RealizedProgram.castElt (a := 0)
      ((muLimb (muOf (x.keyAt (i / 24)) x.msg) (i % 24) : ℕ) : (I 0).K)
  else 0

/-- **A statement holds the rows of a ring statement**: read in field `0`, row `j` of `ring.keys`
is the row of the key at position `j`, row `j` of `ring.mu` its `μ` limbs, for `j < 64`. -/
structure RowsOf (x : RStmt len) (v : program.Valuation I) : Prop where
  /-- `ring.keys` holds the keys' rows. -/
  keys : ∀ j < 64, ∀ s < 5120, (RealizedProgram.castElt (v vK (j * 5120 + s)) : (I 0).K) =
    ((keyEntry (x.keyAt j) s : ℕ) : (I 0).K)
  /-- `ring.mu` holds the members' `μ` limbs. -/
  mu : ∀ j < 64, ∀ l < 24, (RealizedProgram.castElt (v vM (j * 24 + l)) : (I 0).K) =
    ((muLimb (muOf (x.keyAt j) x.msg) l : ℕ) : (I 0).K)

omit [MldsaRingStmt program] in
theorem castElt_castElt_field0 {v : ℕ} (hv : program.valueField v = 0) (y : (I 0).K) :
    (RealizedProgram.castElt (RealizedProgram.castElt (a := 0) (b := program.valueField v) y) :
      (I 0).K) = y := by
  rw [RealizedProgram.castElt_castElt_eq, if_pos hv.symm]
  exact RealizedProgram.castElt_self _

/-- **The program's statement holds the ring's rows.** -/
theorem rowsOf_stmtOf (x : RStmt len) : RowsOf x (stmtOf (program := program) (I := I) x) where
  keys j _ s hs := by
    unfold stmtOf
    rw [if_pos rfl, castElt_castElt_field0 MldsaRingStmt.fields.1,
      show (j * 5120 + s) / 5120 = j by omega, show (j * 5120 + s) % 5120 = s by omega]
  mu j _ l hl := by
    unfold stmtOf
    rw [if_neg MldsaRingStmt.keys_ne.symm, if_pos rfl,
      castElt_castElt_field0 MldsaRingStmt.fields.2,
      show (j * 24 + l) / 24 = j by omega, show (j * 24 + l) % 24 = l by omega]

end GordieHowe.MLDSA44.Ring.Native
