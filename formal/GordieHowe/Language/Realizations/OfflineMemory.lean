-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
# Offline memory checking

The two facts every offline-memory-checking argument needs, independent of any scheme: a fingerprint
identity of two record multisets, packed as products of linear factors over a domain, forces the
multisets themselves to agree (`multiset_eq_of_prod_X_sub_C_eq`); and, given that the writes to one
address are chronologically labelled and every intermediate read's label precedes the label of the
write it is paired with, the multiset agreement forces each read to return the value of the write
immediately preceding it (`chronological`).
-/

namespace GordieHowe.OfflineMemory

open Polynomial

/-- **Fingerprint identity implies multiset equality.**  Over a domain, the
product of `X − C a` over one multiset of records equals the same product
over another multiset only when the multisets themselves agree: the roots of
`∏ (X − C a)`, with multiplicity, are exactly the multiset `s`
(`Polynomial.roots_multiset_prod_X_sub_C`), so equal products have equal
root multisets. -/
theorem multiset_eq_of_prod_X_sub_C_eq {R : Type*} [CommRing R] [IsDomain R] {s t : Multiset R}
    (h : (s.map fun a => X - C a).prod = (t.map fun a => X - C a).prod) : s = t := by
  have := congrArg Polynomial.roots h
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

/-- The list form: the fingerprint identity as a `List.prod`, concluding
equality of the two lists' underlying multisets. -/
theorem multiset_ofList_eq_of_prod_X_sub_C_eq {R : Type*} [CommRing R] [IsDomain R] {l₁ l₂ : List R}
    (h : (l₁.map fun a => X - C a).prod = (l₂.map fun a => X - C a).prod) :
    (↑l₁ : Multiset R) = ↑l₂ := by
  have hs : ((↑l₁ : Multiset R).map fun a => X - C a).prod = (l₁.map fun a => X - C a).prod :=
    Multiset.prod_coe _
  have ht : ((↑l₂ : Multiset R).map fun a => X - C a).prod = (l₂.map fun a => X - C a).prod :=
    Multiset.prod_coe _
  exact multiset_eq_of_prod_X_sub_C_eq (hs.trans (h.trans ht.symm))

/-- **The chronological memory argument.**  `W : Fin (m + 1) → V × O` lists the
`m + 1` writes to one address in chronological order, each carrying a label
(a timestamp or origin) in a linear order; `hW` states the labels strictly
increase along this order.  `R : Fin (m + 1) → V × O` lists, at index `i`
with `i.val < m`, the read paired with the replacement `W i.succ`, and at
index `m` the final read.  Given that the multiset of reads equals the
multiset of writes (`hperm`, from the fingerprint identity) and every
intermediate read's label precedes the label of the write it is paired with
(`horigin`, the circuit's origin bound), every read returns exactly the write
at its own index: `R i = W i` for every `i`, in particular the final read
`R (Fin.last m)` returns the last write. -/
theorem chronological {V O : Type*} [LinearOrder O] {m : ℕ} {W R : Fin (m + 1) → V × O}
    (hW : StrictMono fun i => (W i).2)
    (hperm : (↑(List.ofFn R) : Multiset (V × O)) = ↑(List.ofFn W))
    (horigin : ∀ i : Fin m, (R i.castSucc).2 < (W i.succ).2) :
    ∀ i, R i = W i := by
  have hWinj : Function.Injective W := fun i j hij => hW.injective (congrArg Prod.snd hij)
  have hRnodup : (List.ofFn R).Nodup :=
    (List.Perm.nodup_iff (Multiset.coe_eq_coe.mp hperm)).mpr (List.nodup_ofFn.mpr hWinj)
  have hRinj : Function.Injective R := List.nodup_ofFn.mp hRnodup
  have main : ∀ n : ℕ, ∀ i : Fin (m + 1), i.val = n → R i = W i := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro i hin
      have hmemR : R i ∈ List.ofFn R := List.mem_ofFn.mpr ⟨i, rfl⟩
      have hmemW : R i ∈ List.ofFn W := by
        have h := hmemR
        rwa [← Multiset.mem_coe, hperm, Multiset.mem_coe] at h
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hmemW
      have hkle : k.val ≤ i.val := by
        by_cases hlt : i.val < m
        · by_contra hcon
          set i0 : Fin m := ⟨i.val, hlt⟩ with hi0def
          have hcast : i0.castSucc = i := Fin.ext rfl
          have hbound := horigin i0
          rw [hcast] at hbound
          have hsucc_le : i0.succ.val ≤ k.val := by
            simp only [Fin.val_succ, hi0def]
            omega
          have hmono : (W i0.succ).2 ≤ (W k).2 := hW.monotone (Fin.le_def.mpr hsucc_le)
          have : (W k).2 < (W k).2 := by
            calc (W k).2 = (R i).2 := by rw [hk]
              _ < (W i0.succ).2 := hbound
              _ ≤ (W k).2 := hmono
          exact absurd this (lt_irrefl _)
        · omega
      have hknlt : ¬ k.val < i.val := by
        intro hklt
        have hRk : R k = W k := IH k.val (hin ▸ hklt) k rfl
        have heq : R k = R i := hRk.trans hk
        have : k = i := hRinj heq
        omega
      have hkeq : k.val = i.val := by omega
      rw [← hk, Fin.ext hkeq]
  intro i
  exact main i.val i rfl

end GordieHowe.OfflineMemory
