-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Model

@[expose] public section

/-!
# Circuits of the core

A circuit on a finite basis `ι` is a sequence of Kraus maps and queries (`Quantum.Circuit`). Its run with a
query permutation `π` applies them in order (`Quantum.Circuit.run`), each query being `E_π(ρ) = UρU*` for
`U = permOp π`. Circuits concatenate (`Quantum.Circuit.append`, `Quantum.Circuit.run_append`), which is how the
constructions on the core (`GordieHowe/Model/Quantum/Interactive/Basic.lean`) are written.

`Quantum.Circuit.toAlg` compiles a circuit on `QueryReg V 1 X Y` with an initial state and an output map into
a core algorithm (`Alg`, HU25 Definition 6.3): the Kraus maps between two queries are composed
into one Kraus map (`KrausMap.comp`, HU25 p. 245: "their functional composition E ∘ F is a Kraus
map with operators {E_i · F_j}"), and the query depth is the number of queries
(`Quantum.Circuit.toAlg_depth`). The final state of the compiled algorithm is the run of the circuit
(`Quantum.Circuit.toAlg_final`).
-/

open Finset Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace GordieHowe.Quantum

namespace KrausMap

variable {R₁ R₂ ι : Type*} [Fintype R₁] [Fintype R₂] [Fintype ι] [DecidableEq ι]

/-- **Composition of Kraus maps** (HU25 p. 245): `K₂ ∘ K₁`, with operators `K₂.op r₂ * K₁.op r₁`. -/
def comp (K₂ : KrausMap R₂ ι ι) (K₁ : KrausMap R₁ ι ι) : KrausMap (R₁ × R₂) ι ι where
  op p := K₂.op p.2 * K₁.op p.1
  sum_le := by
    rw [Fintype.sum_prod_type]
    have h : ∀ r₁, ∑ r₂, (K₂.op r₂ * K₁.op r₁)ᴴ * (K₂.op r₂ * K₁.op r₁) =
        (K₁.op r₁)ᴴ * (∑ r₂, (K₂.op r₂)ᴴ * K₂.op r₂) * K₁.op r₁ := fun r₁ => by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r₂ _ => ?_
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simp only [h]
    refine le_trans ?_ K₁.sum_le
    rw [Matrix.le_iff, ← Finset.sum_sub_distrib]
    refine Matrix.posSemidef_sum _ fun r₁ _ => ?_
    have : (K₁.op r₁)ᴴ * K₁.op r₁ - (K₁.op r₁)ᴴ * (∑ r₂, (K₂.op r₂)ᴴ * K₂.op r₂) * K₁.op r₁ =
        (K₁.op r₁)ᴴ * (1 - ∑ r₂, (K₂.op r₂)ᴴ * K₂.op r₂) * K₁.op r₁ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [this]
    exact (Matrix.le_iff.1 K₂.sum_le).conjTranspose_mul_mul_same _

theorem comp_apply (K₂ : KrausMap R₂ ι ι) (K₁ : KrausMap R₁ ι ι) (ρ : Matrix ι ι ℂ) :
    (K₂.comp K₁) ρ = K₂ (K₁ ρ) := by
  simp only [apply, comp, Fintype.sum_prod_type, conjTranspose_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r₂ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  simp only [Matrix.mul_assoc]

/-- A Kraus map moved along a basis equivalence: operators `(K.op r).submatrix e.symm e.symm`. -/
def reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (K : KrausMap R₁ ι ι) :
    KrausMap R₁ κ κ where
  op r := (K.op r).submatrix e.symm e.symm
  sum_le := by
    have h : ∑ r, ((K.op r).submatrix e.symm e.symm)ᴴ * (K.op r).submatrix e.symm e.symm =
        (∑ r, (K.op r)ᴴ * K.op r).submatrix e.symm e.symm := by
      rw [submatrix_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_submatrix, submatrix_mul_equiv]
    rw [h, Matrix.le_iff, ← submatrix_one_equiv e.symm]
    exact (Matrix.le_iff.1 K.sum_le).submatrix _

theorem reindex_apply {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (K : KrausMap R₁ ι ι)
    (ρ : Matrix κ κ ℂ) :
    (K.reindex e) ρ = (K (ρ.submatrix e e)).submatrix e.symm e.symm := by
  rw [apply, apply, submatrix_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hρ : ρ = (ρ.submatrix e e).submatrix e.symm e.symm := by
    rw [submatrix_submatrix]
    simp
  simp only [reindex]
  conv_lhs => rw [hρ]
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

end KrausMap

/-! ### Kraus maps with their index type -/

/-- A Kraus map on `ι` together with its finite index type. -/
structure IndexedKrausMap (ι : Type) [Fintype ι] [DecidableEq ι] : Type 1 where
  /-- The index type. -/
  R : Type
  [instFintype : Fintype R]
  /-- The Kraus map. -/
  K : KrausMap R ι ι

attribute [instance] IndexedKrausMap.instFintype

namespace KrausMap

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Kraus map number `k` of a family, as a Kraus map with index set `Σ k, R k`: zero
operators outside the component `k`. -/
def sigmaEmbed {n : ℕ} (F : Fin n → IndexedKrausMap ι) (k : Fin n) : KrausMap (Σ j, (F j).R) ι ι where
  op p := if h : p.1 = k then (F k).K.op (cast (congrArg (fun j => (F j).R) h) p.2) else 0
  sum_le := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · simpa using (F k).K.sum_le
    · intro j _ hj
      simp [hj]
    · simp

theorem sigmaEmbed_apply {n : ℕ} (F : Fin n → IndexedKrausMap ι) (k : Fin n) (ρ : Matrix ι ι ℂ) :
    (sigmaEmbed F k) ρ = (F k).K ρ := by
  rw [apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [sigmaEmbed, apply]
  · intro j _ hj
    simp [sigmaEmbed, hj]
  · simp

/-- The front decomposition of a run: the first Kraus map, the query, then the run of the
remaining Kraus maps. -/
theorem run_succ' {R : Type*} [Fintype R] {d : ℕ} (step : Fin (d + 1 + 1) → KrausMap R ι ι)
    (π : Equiv.Perm ι) (ρ : Matrix ι ι ℂ) (k : ℕ) :
    run step π ρ (k + 1) =
      run (fun j : Fin (d + 1) => step j.succ) π ((stepAt step 0 ρ).submatrix π.symm π.symm) k := by
  have hs : ∀ j (σ : Matrix ι ι ℂ), stepAt step (j + 1) σ =
      stepAt (fun j : Fin (d + 1) => step j.succ) j σ := fun j σ => by
    unfold stepAt
    by_cases h : j < d + 1
    · rw [dif_pos (by omega), dif_pos h]
      rfl
    · rw [dif_neg (by omega), dif_neg h]
  induction k with
  | zero => rw [run_succ, run_zero, run_zero, hs]
  | succ k ih => rw [run_succ, ih, run_succ, hs]

end KrausMap

/-! ### Circuits -/

/-- **A circuit of the core** on the basis `ι`: Kraus maps and queries in sequence. -/
inductive Circuit (ι : Type) [Fintype ι] [DecidableEq ι] : Type 1 where
  /-- The empty circuit. -/
  | nil : Circuit ι
  /-- A Kraus map, then the rest. -/
  | kraus {R : Type} [Fintype R] (K : KrausMap R ι ι) (c : Circuit ι) : Circuit ι
  /-- A query, then the rest. -/
  | query (c : Circuit ι) : Circuit ι

namespace Circuit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The run of a circuit** with query permutation `π`: the Kraus maps and the queries
`ρ ↦ ρ.submatrix π.symm π.symm` in order. -/
def run (π : Equiv.Perm ι) : Circuit ι → Matrix ι ι ℂ → Matrix ι ι ℂ
  | nil, ρ => ρ
  | kraus K c, ρ => run π c (K ρ)
  | query c, ρ => run π c (ρ.submatrix π.symm π.symm)

/-- The number of queries of a circuit. -/
def queries : Circuit ι → ℕ
  | nil => 0
  | kraus _ c => queries c
  | query c => queries c + 1

/-- Concatenation of circuits. -/
def append : Circuit ι → Circuit ι → Circuit ι
  | nil, d => d
  | kraus K c, d => kraus K (append c d)
  | query c, d => query (append c d)

instance : Append (Circuit ι) :=
  ⟨append⟩

@[simp] theorem nil_append (d : Circuit ι) : (nil : Circuit ι) ++ d = d := rfl
@[simp] theorem kraus_append {R : Type} [Fintype R] (K : KrausMap R ι ι) (c d : Circuit ι) :
    kraus K c ++ d = kraus K (c ++ d) := rfl
@[simp] theorem query_append (c d : Circuit ι) : query c ++ d = query (c ++ d) := rfl

theorem run_append (π : Equiv.Perm ι) (c d : Circuit ι) (ρ : Matrix ι ι ℂ) :
    (c ++ d).run π ρ = d.run π (c.run π ρ) := by
  induction c generalizing ρ with
  | nil => rfl
  | kraus K c ih => exact ih _
  | query c ih => exact ih _

theorem queries_append (c d : Circuit ι) : (c ++ d).queries = c.queries + d.queries := by
  induction c with
  | nil => simp [queries]
  | kraus K c ih => simpa [queries] using ih
  | query c ih =>
    simp only [query_append, queries, ih]
    omega

theorem posSemidef_run (π : Equiv.Perm ι) (c : Circuit ι) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    (c.run π ρ).PosSemidef := by
  induction c generalizing ρ with
  | nil => exact hρ
  | kraus K c ih => exact ih (K.posSemidef_apply hρ)
  | query c ih => exact ih (hρ.submatrix _)

theorem re_trace_run_le (π : Equiv.Perm ι) (c : Circuit ι) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    (c.run π ρ).trace.re ≤ ρ.trace.re := by
  induction c generalizing ρ with
  | nil => exact le_rfl
  | kraus K c ih => exact (ih (K.posSemidef_apply hρ)).trans (K.re_trace_apply_le hρ)
  | query c ih =>
    refine (ih (hρ.submatrix _)).trans ?_
    rw [trace_submatrix_equiv]

/-! #### Compilation into one Kraus map per query interval -/

/-- The Kraus maps before the first query, composed (the identity if there are none). -/
def head : Circuit ι → IndexedKrausMap ι
  | nil => ⟨Unit, KrausMap.identity ι⟩
  | kraus K c => ⟨_, (head c).K.comp K⟩
  | query _ => ⟨Unit, KrausMap.identity ι⟩

/-- The circuit after the first query (empty if there is none). -/
def tail : Circuit ι → Circuit ι
  | nil => nil
  | kraus _ c => tail c
  | query c => c

/-- The `k`-th query interval's composed Kraus map. -/
def seg : Circuit ι → ℕ → IndexedKrausMap ι
  | c, 0 => head c
  | c, k + 1 => seg (tail c) k

theorem queries_tail (c : Circuit ι) (h : 0 < c.queries) : (tail c).queries + 1 = c.queries := by
  induction c with
  | nil => simp [queries] at h
  | kraus K c ih => exact ih h
  | query c _ => rfl

/-- The run of a circuit without queries is its composed Kraus map. -/
theorem run_of_queries_eq_zero (π : Equiv.Perm ι) (c : Circuit ι) (h : c.queries = 0)
    (ρ : Matrix ι ι ℂ) : c.run π ρ = (head c).K ρ := by
  induction c generalizing ρ with
  | nil => exact (KrausMap.id_apply (ι := ι) ρ).symm
  | kraus K c ih => rw [run, ih h, head, KrausMap.comp_apply]
  | query c _ => simp [queries] at h

/-- The run of a circuit with a query: the composed Kraus maps before it, the query, and the run
of the rest. -/
theorem run_of_pos (π : Equiv.Perm ι) (c : Circuit ι) (h : 0 < c.queries) (ρ : Matrix ι ι ℂ) :
    c.run π ρ = (tail c).run π (((head c).K ρ).submatrix π.symm π.symm) := by
  induction c generalizing ρ with
  | nil => simp [queries] at h
  | kraus K c ih => rw [run, ih h, head, KrausMap.comp_apply]; rfl
  | query c _ => rw [run, tail, head]; exact congrArg _ (by rw [KrausMap.id_apply])

end Circuit

namespace Circuit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Maps alternating with a basis permutation, indexed by `ℕ` (the shape of `KrausMap.run`). -/
def runN (f : ℕ → Matrix ι ι ℂ → Matrix ι ι ℂ) (π : Equiv.Perm ι) (ρ : Matrix ι ι ℂ) :
    ℕ → Matrix ι ι ℂ
  | 0 => f 0 ρ
  | k + 1 => f (k + 1) ((runN f π ρ k).submatrix π.symm π.symm)

theorem runN_succ' (f : ℕ → Matrix ι ι ℂ → Matrix ι ι ℂ) (π : Equiv.Perm ι) (ρ : Matrix ι ι ℂ)
    (k : ℕ) : runN f π ρ (k + 1) =
      runN (fun j => f (j + 1)) π ((f 0 ρ).submatrix π.symm π.symm) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runN, ih]; rfl

theorem run_eq_runN {R : Type*} [Fintype R] {d : ℕ} (step : Fin (d + 1) → KrausMap R ι ι)
    (π : Equiv.Perm ι) (ρ : Matrix ι ι ℂ) (k : ℕ) :
    KrausMap.run step π ρ k = runN (KrausMap.stepAt step) π ρ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [KrausMap.run_succ, ih]; rfl

/-- **A circuit is the alternation of its composed query intervals.** -/
theorem run_eq_runN_seg (π : Equiv.Perm ι) (c : Circuit ι) (ρ : Matrix ι ι ℂ) :
    c.run π ρ = runN (fun k => (seg c k).K.apply) π ρ c.queries := by
  induction h : c.queries generalizing c ρ with
  | zero => rw [run_of_queries_eq_zero π c h]; rfl
  | succ n ih =>
    rw [run_of_pos π c (by omega), runN_succ']
    exact ih (tail c) _ (by have := queries_tail c (by omega); omega)

end Circuit

/-- **A circuit compiled into a core algorithm**: on `QueryReg V 1 X Y`, with an initial state
and an output map; the Kraus map number `k` is the composition of the Kraus maps of the `k`-th
query interval (`Quantum.Circuit.seg`), and the query depth is the number of queries. -/
abbrev Circuit.toAlg {V X Y O : Type} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] (c : Circuit (QueryReg V 1 X Y))
    (init : MState (QueryReg V 1 X Y)) (out : V → O) : Alg X Y O where
  V := V
  depth := c.queries
  R := Σ k : Fin (c.queries + 1), (c.seg k).R
  init := init
  step := KrausMap.sigmaEmbed fun k => c.seg k
  out := out

theorem Circuit.toAlg_depth {V X Y O : Type} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] (c : Circuit (QueryReg V 1 X Y))
    (init : MState (QueryReg V 1 X Y)) (out : V → O) : (c.toAlg init out).depth = c.queries :=
  rfl

/-- **The compiled algorithm runs the circuit**: its final state with oracle `H` is the run of the
circuit with the query `queryPerm H`. -/
theorem Circuit.toAlg_final {V X Y O : Type} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] (c : Circuit (QueryReg V 1 X Y))
    (init : MState (QueryReg V 1 X Y)) (out : V → O) (H : X → Y) :
    (c.toAlg init out).final H = c.run (queryPerm H) init.mat := by
  rw [Circuit.run_eq_runN_seg, Alg.final, Alg.stage, Circuit.run_eq_runN]
  have h : ∀ k ≤ c.queries, ∀ ρ, KrausMap.stepAt (c.toAlg init out).step k ρ =
      (c.seg k).K ρ := fun k hk ρ => by
    rw [KrausMap.stepAt_of_lt _ (Nat.lt_succ_of_le hk), KrausMap.sigmaEmbed_apply]
  have key : ∀ n ≤ c.queries, Circuit.runN (KrausMap.stepAt (c.toAlg init out).step)
      (queryPerm H) init.mat n = Circuit.runN (fun k => (c.seg k).K.apply) (queryPerm H) init.mat n := by
    intro n hn
    induction n with
    | zero => exact h 0 (Nat.zero_le _) _
    | succ n ih =>
      simp only [Circuit.runN]
      rw [ih (by omega), h _ hn]
  exact key _ le_rfl

end GordieHowe.Quantum
