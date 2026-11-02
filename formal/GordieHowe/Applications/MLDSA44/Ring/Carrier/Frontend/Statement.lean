-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Statement
public import GordieHowe.Applications.MLDSA44.Emulated.Rows

@[expose] public section

/-!
# GordieHowe frontend: the statement of the ML-DSA-44 ring carriers

The statement values of the ML-DSA-44 ring carriers (`ring_rows` in
`lib/gordiehowe/examples/rings/mldsa_ring.h` with `ring_host::carrier_key_row` and
`ring_host::mu_limbs` in `lib/gordiehowe/examples/rings/mldsa_ring_host.h`) as functions of a ring
statement `(R, M′, ())`: each is an opaque statement value of no argument, supplied by the
verifier's statement map. The `μ` limbs are the native rings' (`Native.muLimb`, `Native.muOf`).

* **A key's carrier row** (`keyEntry`, `5120` naturals below `q`): `A = NTT⁻¹(Â)`'s coefficients
  (`(i, j, k)` row-major, `Â = ExpandA(ρ)` within the byte budget, `MLDSA44.expandABounded`,
  `aNat`), then the coefficients of `2^d · t1_i` (`tNat`, `Emulated.Rows.tKeyOf`).
* **The program's statement** (`stmtOf`): row `j` of `ring.keys` the carrier row of the key at
  position `j`, row `j` of `ring.mu` its `μ` limbs, every other coordinate `0` (`ring.tr`, which
  the relation does not read, included).
* **The statement holds a ring's rows** (`RowsOf`); `rowsOf_stmtOf`.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Ring
open Native (MldsaRingStmt muLimb muOf)

/-- **Coefficient `k` of `A_ij = NTT⁻¹(Â_ij)`** of a key, `Â` within the byte budget
(`MLDSA44.expandABounded`), as a natural below `q`. -/
def aNat (pk : PublicKey) (i j : Fin 4) (k : Fin 256) : ℕ :=
  MLDSA44.KeyNTT.vals (_root_.MLDSA.Concrete.invNTT
    (((MLDSA44.expandABounded _root_.MLDSA.mldsa44 pk.rho).get i).get j)) k

/-- **Coefficient `k` of `2^d · t1_i`** of a key, as a natural below `q`
(`Emulated.Rows.tKeyOf`). -/
def tNat (pk : PublicKey) (i : Fin 4) (k : Fin 256) : ℕ :=
  Emulated.Rows.tKeyOf pk i k

/-- **Entry `s` of a key's carrier row** (`ring_host::carrier_key_row`): `A` at
`s = (4 i + j) · 256 + k`, then `2^d · t1` at `s = 4096 + 256 i + k`, `0` past `5120`. -/
def keyEntry (pk : PublicKey) (s : ℕ) : ℕ :=
  if h : s < 4096 then aNat pk ⟨s / 1024, by omega⟩ ⟨s / 256 % 4, by omega⟩ ⟨s % 256, by omega⟩
  else if h' : s < 5120 then tNat pk ⟨(s - 4096) / 256, by omega⟩ ⟨(s - 4096) % 256, by omega⟩
  else 0

theorem keyEntry_a (pk : PublicKey) (i j : Fin 4) (k : Fin 256) :
    keyEntry pk (((i : ℕ) * 4 + j) * 256 + k) = aNat pk i j k := by
  have hi := i.isLt; have hj := j.isLt; have hk := k.isLt
  unfold keyEntry
  rw [dif_pos (by omega)]
  congr 1 <;> apply Fin.ext <;> simp only <;> omega

theorem keyEntry_t (pk : PublicKey) (i : Fin 4) (k : Fin 256) :
    keyEntry pk (4096 + ((i : ℕ) * 256 + k)) = tNat pk i k := by
  have hi := i.isLt; have hk := k.isLt
  unfold keyEntry
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg₂ (tNat pk) (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

/-- **A key's carrier row lies below `q`.** -/
theorem keyEntry_lt (pk : PublicKey) (s : ℕ) : keyEntry pk s < 8380417 := by
  unfold keyEntry aNat tNat Emulated.Rows.tKeyOf
  split_ifs
  · exact lt_of_lt_of_eq (MLDSA44.KeyNTT.vals_lt _ _) rfl
  · exact lt_of_lt_of_eq (MLDSA44.KeyNTT.vals_lt _ _) rfl
  · exact Nat.zero_lt_succ _

variable {program : RealizedProgram} [MldsaRingStmt program] {I : RealizedProgram.Interp}
  {len : ℕ}

set_option hygiene false in
local notation "vK" => MldsaRingStmt.keys program

set_option hygiene false in
local notation "vM" => MldsaRingStmt.mu program

/-- **The program's statement of a ring statement**: coordinate `5120 j + s` of `ring.keys` is
entry `s` of the carrier row of the key at position `j`, coordinate `24 j + l` of `ring.mu` limb
`l` of its `μ`, every other coordinate `0`. -/
def stmtOf (x : RStmt len) : program.Valuation I := fun v i =>
  if v = vK then
    RealizedProgram.castElt (a := 0) ((keyEntry (x.keyAt (i / 5120)) (i % 5120) : ℕ) : (I 0).K)
  else if v = vM then
    RealizedProgram.castElt (a := 0)
      ((muLimb (muOf (x.keyAt (i / 24)) x.msg) (i % 24) : ℕ) : (I 0).K)
  else 0

/-- **A statement holds the carrier rows of a ring statement**: read in field `0`, row `j` of
`ring.keys` is the carrier row of the key at position `j`, row `j` of `ring.mu` its `μ` limbs, for
`j < 64`. -/
structure RowsOf (x : RStmt len) (v : program.Valuation I) : Prop where
  /-- `ring.keys` holds the keys' carrier rows. -/
  keys : ∀ j < 64, ∀ s < 5120, (RealizedProgram.castElt (v vK (j * 5120 + s)) : (I 0).K) =
    ((keyEntry (x.keyAt j) s : ℕ) : (I 0).K)
  /-- `ring.mu` holds the members' `μ` limbs. -/
  mu : ∀ j < 64, ∀ l < 24, (RealizedProgram.castElt (v vM (j * 24 + l)) : (I 0).K) =
    ((muLimb (muOf (x.keyAt j) x.msg) l : ℕ) : (I 0).K)

/-- **The program's statement holds the ring's carrier rows.** -/
theorem rowsOf_stmtOf (x : RStmt len) : RowsOf x (stmtOf (program := program) (I := I) x) where
  keys j _ s hs := by
    unfold stmtOf
    rw [if_pos rfl, Native.castElt_castElt_field0 MldsaRingStmt.fields.1,
      show (j * 5120 + s) / 5120 = j by omega, show (j * 5120 + s) % 5120 = s by omega]
  mu j _ l hl := by
    unfold stmtOf
    rw [if_neg MldsaRingStmt.keys_ne.symm, if_pos rfl,
      Native.castElt_castElt_field0 MldsaRingStmt.fields.2,
      show (j * 24 + l) / 24 = j by omega, show (j * 24 + l) % 24 = l by omega]

end GordieHowe.MLDSA44.Ring.Carrier
