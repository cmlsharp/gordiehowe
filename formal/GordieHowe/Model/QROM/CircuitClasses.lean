-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.BridgeClasses
public import GordieHowe.Model.Quantum.Interactive.Test

@[expose] public section

/-!
# Circuits whose Kraus maps keep a function of the basis state

A Kraus map keeps a function `F` of the basis state (`KrausMap.Keeps F`) when it is trace
preserving and its operators join only basis states with the same value of `F`. This file proves
that the property is closed under the constructions of the core (composition, basis permutations
that fix `F`, relabelling, `⊗ 1`, padding of the index set), and that a circuit whose Kraus maps
after its first `s` queries all keep `F` compiles into a core algorithm whose maps after step `s`
keep `F` (`Circuit.stepsKeep_toAlg`), the hypothesis of `Alg.keepsClasses_toQueryAlgCoh`. Circuits
with reprogrammed queries (`ReprogrammedCircuit`) compile with this property when their own Kraus
maps keep a function of the work register: the reprogramming sub-circuit changes only the query
register and the ancilla (`ReprogrammedCircuit.allKeep_toCircuit`).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

namespace KrausMap

variable {R R₁ R₂ Γ : Type*} {ι : Type} [Fintype R] [Fintype R₁] [Fintype R₂] [Fintype ι] [DecidableEq ι]

/-- **A Kraus map keeps a function `F` of the basis state**: it is trace preserving and its
operators join only basis states with the same value of `F`. -/
structure Keeps (F : ι → Γ) (K : KrausMap R ι ι) : Prop where
  /-- Trace preservation. -/
  tp : ∑ r, (K.op r)ᴴ * K.op r = 1
  /-- The classes of `F` are kept. -/
  keeps : ∀ r i' i, K.op r i' i ≠ 0 → F i' = F i

variable {F : ι → Γ}

theorem keeps_identity (F : ι → Γ) : (KrausMap.identity ι).Keeps F where
  tp := by simp [KrausMap.identity]
  keeps r i' i h := by
    simp only [KrausMap.identity, Matrix.one_apply] at h
    split_ifs at h with hh
    · rw [hh]
    · exact absurd rfl h

theorem Keeps.comp {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι} (h₂ : K₂.Keeps F) (h₁ : K₁.Keeps F) :
    (K₂.comp K₁).Keeps F where
  tp := by
    show ∑ p : R₁ × R₂, (K₂.op p.2 * K₁.op p.1)ᴴ * (K₂.op p.2 * K₁.op p.1) = 1
    rw [Fintype.sum_prod_type]
    have : ∀ r₁, ∑ r₂, (K₂.op r₂ * K₁.op r₁)ᴴ * (K₂.op r₂ * K₁.op r₁) =
        (K₁.op r₁)ᴴ * K₁.op r₁ := fun r₁ => by
      have e : ∀ r₂, (K₂.op r₂ * K₁.op r₁)ᴴ * (K₂.op r₂ * K₁.op r₁) =
          (K₁.op r₁)ᴴ * ((K₂.op r₂)ᴴ * K₂.op r₂) * K₁.op r₁ := fun r₂ => by
        rw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      simp_rw [e]
      rw [← Finset.sum_mul, ← Finset.mul_sum, h₂.tp, Matrix.mul_one]
    simp_rw [this]
    exact h₁.tp
  keeps r i' i h := by
    change (K₂.op r.2 * K₁.op r.1) i' i ≠ 0 at h
    rw [Matrix.mul_apply] at h
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h2 : K₂.op r.2 i' m ≠ 0 := left_ne_zero_of_mul hm
    have h1 : K₁.op r.1 m i ≠ 0 := right_ne_zero_of_mul hm
    exact (h₂.keeps _ _ _ h2).trans (h₁.keeps _ _ _ h1)

theorem Keeps.permConj {K : KrausMap R ι ι} (h : K.Keeps F) {σ τ : Equiv.Perm ι}
    (hσ : ∀ i, F (σ i) = F i) (hτ : ∀ i, F (τ i) = F i) : (K.permConj σ τ).Keeps F where
  tp := by
    have hs : ∑ r, ((K.op r).submatrix τ.symm σ)ᴴ * (K.op r).submatrix τ.symm σ =
        (∑ r, (K.op r)ᴴ * K.op r).submatrix σ σ := by
      rw [submatrix_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_submatrix, submatrix_mul_equiv]
    show ∑ r, ((K.op r).submatrix τ.symm σ)ᴴ * (K.op r).submatrix τ.symm σ = 1
    rw [hs, h.tp, submatrix_one_equiv]
  keeps r i' i hne := by
    have := h.keeps r (τ.symm i') (σ i) hne
    rw [hσ] at this
    rw [← this, ← hτ (τ.symm i'), Equiv.apply_symm_apply]

theorem keeps_ofPerm {π : Equiv.Perm ι} (hπ : ∀ i, F (π i) = F i) : (KrausMap.ofPerm π).Keeps F :=
  (keeps_identity F).permConj (fun _ => rfl) hπ

theorem Keeps.reindex {κ : Type} [Fintype κ] [DecidableEq κ] {K : KrausMap R ι ι} (h : K.Keeps F)
    (e : ι ≃ κ) {F' : κ → Γ} (hF : ∀ i, F' (e i) = F i) : (K.reindex e).Keeps F' where
  tp := by
    have hs : ∑ r, ((K.op r).submatrix e.symm e.symm)ᴴ * (K.op r).submatrix e.symm e.symm =
        (∑ r, (K.op r)ᴴ * K.op r).submatrix e.symm e.symm := by
      rw [submatrix_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_submatrix, submatrix_mul_equiv]
    show ∑ r, ((K.op r).submatrix e.symm e.symm)ᴴ * (K.op r).submatrix e.symm e.symm = 1
    rw [hs, h.tp, submatrix_one_equiv]
  keeps r i' i hne := by
    have := h.keeps r (e.symm i') (e.symm i) hne
    rw [← hF, ← hF, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this

theorem Keeps.tensorId {A : Type} [Fintype A] [DecidableEq A] {K : KrausMap R ι ι} (h : K.Keeps F) :
    (K.tensorId A).Keeps fun p : ι × A => F p.1 where
  tp := by
    show ∑ r, (K.op r ⊗ₖ (1 : Matrix A A ℂ))ᴴ * (K.op r ⊗ₖ (1 : Matrix A A ℂ)) = 1
    rw [show ∑ r, (K.op r ⊗ₖ (1 : Matrix A A ℂ))ᴴ * (K.op r ⊗ₖ (1 : Matrix A A ℂ)) =
        (∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix A A ℂ) by
      rw [sum_kronecker]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul],
      h.tp, one_kronecker_one]
  keeps r p' p hne := by
    simp only [KrausMap.tensorId, kroneckerMap_apply] at hne
    exact h.keeps r p'.1 p.1 (left_ne_zero_of_mul hne)

/-- A Kraus map that keeps `F` keeps every function of `F`. -/
theorem Keeps.map {Γ' : Type*} {K : KrausMap R ι ι} (h : K.Keeps F) (φ : Γ → Γ') :
    K.Keeps (φ ∘ F) where
  tp := h.tp
  keeps r i' i hne := by
    simp only [Function.comp_apply]
    rw [h.keeps r i' i hne]

/-- `K ⊗ 1` keeps `F` on the first factor together with the second factor. -/
theorem Keeps.tensorId_prod {A : Type} [Fintype A] [DecidableEq A] {K : KrausMap R ι ι}
    (h : K.Keeps F) : (K.tensorId A).Keeps fun p : ι × A => (F p.1, p.2) where
  tp := h.tensorId.tp
  keeps r p' p hne := by
    simp only [KrausMap.tensorId, kroneckerMap_apply, Matrix.one_apply] at hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    split_ifs at h2 with h3
    · rw [h.keeps r p'.1 p.1 h1, h3]
    · exact absurd rfl h2

theorem Keeps.embedIdx {R' : Type*} [Fintype R'] {K : KrausMap R ι ι} (h : K.Keeps F) (f : R ↪ R') :
    (K.embedIdx f).Keeps F where
  tp := by
    classical
    have hop : ∀ r, (K.embedIdx f).op (f r) = K.op r := fun r => by
      change (if hh : ∃ r₀, f r₀ = f r then K.op hh.choose else 0) = K.op r
      rw [dif_pos ⟨r, rfl⟩]
      congr 1
      exact f.injective (Exists.choose_spec (⟨r, rfl⟩ : ∃ r₀, f r₀ = f r))
    have hzero : ∀ r', r' ∉ univ.map f → (K.embedIdx f).op r' = 0 := fun r' hr' => by
      change (if hh : ∃ r, f r = r' then K.op hh.choose else 0) = 0
      rw [dif_neg fun ⟨r, hr⟩ => hr' (Finset.mem_map.2 ⟨r, Finset.mem_univ _, hr⟩)]
    rw [← Finset.sum_subset (Finset.subset_univ (univ.map f)) fun r' _ hr' => by
      rw [hzero r' hr']
      simp, Finset.sum_map]
    simp_rw [hop]
    exact h.tp
  keeps r' i' i hne := by
    classical
    change (if hh : ∃ r, f r = r' then K.op hh.choose else 0) i' i ≠ 0 at hne
    split_ifs at hne with hh
    · exact h.keeps _ _ _ hne
    · exact absurd rfl hne

theorem keeps_sigmaEmbed {n : ℕ} {G : Fin n → IndexedKrausMap ι} {k : Fin n} (h : (G k).K.Keeps F) :
    (KrausMap.sigmaEmbed G k).Keeps F where
  tp := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single k]
    · simpa [sigmaEmbed] using h.tp
    · intro j _ hj
      simp [sigmaEmbed, hj]
    · simp
  keeps p i' i hne := by
    simp only [sigmaEmbed] at hne
    split_ifs at hne with hh
    · exact h.keeps _ _ _ hne
    · exact absurd rfl hne

end KrausMap

/-- A trace-preserving family as a Kraus map keeps the classes it keeps. -/
theorem KrausChannel.keeps_toKrausMap {R Γ : Type*} {ι : Type} [Fintype R] [Fintype ι] [DecidableEq ι]
    {K : KrausChannel R ι ι} {F : ι → Γ} (h : K.KeepsFn F) : K.toKrausMap.Keeps F where
  tp := K.sum_conjTranspose_mul
  keeps := h

/-! ### Circuits -/

namespace Circuit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type*} (F : ι → Γ)

/-- **Every Kraus map of the circuit keeps `F`.** -/
def AllKeep : Circuit ι → Prop
  | nil => True
  | kraus K c => K.Keeps F ∧ AllKeep c
  | query c => AllKeep c

variable {F}

theorem AllKeep.head : ∀ {c : Circuit ι}, AllKeep F c → (Circuit.head c).K.Keeps F
  | nil, _ => KrausMap.keeps_identity F
  | kraus _ c, h => (AllKeep.head (c := c) h.2).comp h.1
  | query _, _ => KrausMap.keeps_identity F

theorem AllKeep.tail : ∀ {c : Circuit ι}, AllKeep F c → AllKeep F (Circuit.tail c)
  | nil, h => h
  | kraus _ c, h => AllKeep.tail (c := c) h.2
  | query _, h => h

theorem AllKeep.seg {c : Circuit ι} (h : AllKeep F c) : ∀ k, (Circuit.seg c k).K.Keeps F
  | 0 => h.head
  | k + 1 => AllKeep.seg (c := Circuit.tail c) h.tail k

theorem seg_kraus_succ {R : Type} [Fintype R] (K : KrausMap R ι ι) (d : Circuit ι) (m : ℕ) :
    Circuit.seg (kraus K d) (m + 1) = Circuit.seg d (m + 1) :=
  rfl

/-- After the queries of a prefix, the query intervals are those of the rest. -/
theorem seg_append_succ : ∀ (c d : Circuit ι) (m : ℕ),
    Circuit.seg (c ++ d) (c.queries + (m + 1)) = Circuit.seg d (m + 1)
  | nil, d, m => by simp [queries]
  | kraus K c, d, m => by
    rw [kraus_append, queries]
    exact seg_append_succ c d m
  | query c, d, m => by
    rw [query_append, queries, show c.queries + 1 + (m + 1) = (c.queries + (m + 1)) + 1 by omega]
    exact seg_append_succ c d m

variable {V X Y O : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- **A circuit whose Kraus maps after the first `s` queries keep a function of the work register
compiles into a core algorithm whose maps after step `s` keep it**: for `c = c₁ ++ kraus J c₂`
with `s = c₁.queries` and every Kraus map of `c₂` keeping `f` of the work register. -/
theorem stepsKeep_toAlg {Γ : Type} {f : V → Γ} {R : Type} [Fintype R] (c₁ : Circuit (QueryReg V 1 X Y))
    (J : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)) (c₂ : Circuit (QueryReg V 1 X Y))
    (h : AllKeep (fun i : QueryReg V 1 X Y => f i.1) c₂) (init : MState (QueryReg V 1 X Y))
    (out : V → O) :
    ((c₁ ++ kraus J c₂).toAlg init out).StepsKeep c₁.queries f := by
  have hseg : ∀ j (hj : j < (c₁ ++ kraus J c₂).queries + 1), c₁.queries < j →
      (KrausMap.sigmaEmbed (fun k : Fin ((c₁ ++ kraus J c₂).queries + 1) => (c₁ ++ kraus J c₂).seg k)
        ⟨j, hj⟩).Keeps (fun i : QueryReg V 1 X Y => f i.1) := fun j hj hsj => by
    refine KrausMap.keeps_sigmaEmbed ?_
    obtain ⟨m, rfl⟩ : ∃ m, j = c₁.queries + (m + 1) := ⟨j - c₁.queries - 1, by omega⟩
    show (Circuit.seg (c₁ ++ kraus J c₂) (c₁.queries + (m + 1))).K.Keeps _
    rw [seg_append_succ, seg_kraus_succ]
    exact h.seg _
  exact ⟨fun j hj hsj => (hseg j hj hsj).tp, fun j hj hsj => (hseg j hj hsj).keeps⟩

end Circuit

/-! ### Circuits with reprogrammed queries -/

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] {Γ : Type*} (g : V → Γ)

/-- **Every Kraus map of the circuit keeps `g` of the work register** (the reprogrammed queries
keep it: `allKeep_toCircuit`). -/
def AllKeep : ReprogrammedCircuit V X Y → Prop
  | nil => True
  | kraus K c => K.Keeps (fun i : QueryReg V 1 X Y => g i.1) ∧ AllKeep c
  | rquery _ c => AllKeep c

variable {g}

theorem allKeep_append : ∀ {c d : ReprogrammedCircuit V X Y}, AllKeep g c → AllKeep g d →
    AllKeep g (c ++ d)
  | nil, _, _, hd => hd
  | kraus _ c, _, hc, hd => ⟨hc.1, allKeep_append (c := c) hc.2 hd⟩
  | rquery _ c, _, hc, hd => allKeep_append (c := c) hc hd

theorem keeps_liftAnc {R : Type} [Fintype R] {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h : K.Keeps fun i : QueryReg V 1 X Y => g i.1) :
    K.liftAnc.Keeps fun i : ReprogrammedQueryReg V X Y => g i.1.1 :=
  h.tensorId.reindex _ fun _ => rfl

/-- Concatenation of circuits with reprogrammed queries is associative. -/
theorem append_assoc : ∀ (c d e : ReprogrammedCircuit V X Y), c ++ d ++ e = c ++ (d ++ e)
  | nil, _, _ => rfl
  | kraus K c, d, e => by
    simp only [kraus_append]
    rw [append_assoc c d e]
  | rquery a c, d, e => by
    simp only [rquery_append]
    rw [append_assoc c d e]

/-- `concat` of an appended list. -/
theorem concat_append : ∀ (cs ds : List (ReprogrammedCircuit V X Y)),
    concat (cs ++ ds) = concat cs ++ concat ds
  | [], _ => rfl
  | c :: cs, ds => by
    rw [List.cons_append, concat, concat, concat_append cs ds, append_assoc]

theorem allKeep_concat : ∀ {cs : List (ReprogrammedCircuit V X Y)}, (∀ c ∈ cs, AllKeep g c) →
    AllKeep g (concat cs)
  | [], _ => trivial
  | c :: cs, h => allKeep_append (h c (List.mem_cons_self ..))
      (allKeep_concat (cs := cs) fun d hd => h d (List.mem_cons_of_mem _ hd))

variable [AddGroup Y]

theorem toCircuit_append : ∀ (c d : ReprogrammedCircuit V X Y),
    toCircuit (c ++ d) = toCircuit c ++ toCircuit d
  | nil, _ => rfl
  | kraus K c, d => by
    rw [kraus_append, toCircuit, toCircuit, toCircuit_append c d]
    rfl
  | rquery a c, d => by
    rw [rquery_append, toCircuit, toCircuit, toCircuit_append c d]
    rfl

omit [AddGroup Y] in
theorem keeps_reprogSwap (a : V → List (Assignment X Y)) :
    (KrausMap.ofPerm (reprogSwap a)).Keeps fun i : ReprogrammedQueryReg V X Y => g i.1.1 :=
  KrausMap.keeps_ofPerm fun p => by
    rw [reprogSwap_apply]
    split_ifs <;> rfl

theorem keeps_reprogAdd (a : V → List (Assignment X Y)) :
    (KrausMap.ofPerm (reprogAdd a)).Keeps fun i : ReprogrammedQueryReg V X Y => g i.1.1 :=
  KrausMap.keeps_ofPerm fun _ => rfl

/-- **The compiled circuit keeps `g` of the work register** when the circuit's own Kraus maps do:
the reprogramming sub-circuit changes only the query register and the ancilla. -/
theorem allKeep_toCircuit : ∀ {c : ReprogrammedCircuit V X Y}, AllKeep g c →
    Circuit.AllKeep (fun i : ReprogrammedQueryReg V X Y => g i.1.1) (toCircuit c)
  | nil, _ => trivial
  | kraus _ c, h => ⟨keeps_liftAnc h.1, allKeep_toCircuit (c := c) h.2⟩
  | rquery a c, h => ⟨keeps_reprogSwap a, ((keeps_reprogAdd a).comp (keeps_reprogSwap a)),
      allKeep_toCircuit (c := c) h⟩

/-- **Every Kraus map after the first keeps `g`**: the circuit is a Kraus map followed by a circuit
whose Kraus maps keep `g`. -/
def HeadKeep (g : V → Γ) (c : ReprogrammedCircuit V X Y) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (J : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y))
    (c' : ReprogrammedCircuit V X Y), c = kraus J c' ∧ AllKeep g c'

omit [AddGroup Y] in
theorem HeadKeep.append {c d : ReprogrammedCircuit V X Y} (hc : HeadKeep g c) (hd : AllKeep g d) :
    HeadKeep g (c ++ d) := by
  obtain ⟨R, _, J, c', rfl, hc'⟩ := hc
  exact ⟨R, inferInstance, J, c' ++ d, rfl, allKeep_append hc' hd⟩

omit [AddGroup Y] in
/-- **A concatenation over `Fin m` followed by `last` keeps `g` after its first Kraus map** when the
first member does after its first Kraus map, the others do throughout, and `last` does after its
first Kraus map if `m = 0` and throughout otherwise. -/
theorem headKeep_concat_finRange : ∀ (m : ℕ) (f : Fin m → ReprogrammedCircuit V X Y)
    (last : ReprogrammedCircuit V X Y), (m = 0 → HeadKeep g last) → (0 < m → AllKeep g last) →
    (∀ h : 0 < m, HeadKeep g (f ⟨0, h⟩)) → (∀ i : Fin m, 0 < (i : ℕ) → AllKeep g (f i)) →
    HeadKeep g (concat ((List.finRange m).map f) ++ last)
  | 0, _, last, h0, _, _, _ => by simpa [concat] using h0 rfl
  | n + 1, f, last, _, hl, hf0, hfi => by
    rw [List.finRange_succ, List.map_cons, concat, append_assoc]
    refine (hf0 (Nat.succ_pos n)).append (allKeep_append (allKeep_concat fun c hc => ?_) (hl (Nat.succ_pos n)))
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
    exact hfi _ (Nat.succ_pos _)

end ReprogrammedCircuit

end GordieHowe.Quantum
