-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.Codec
public import GordieHowe.Model.IOP.CausalLeaves
public import Mathlib.Data.List.Sigma

@[expose] public section

/-!
# The bytes of the chains of several leaves

The byte encoding of chain inputs with merges (`GordieHowe/SPBCS/Bytes.lean`) writes the label of
the observer (from the path bytes of a leaf, `Leaf.pathBytes`), then the item bytes of the chains
of the leaves the observer reads in full, one after the other. This file holds those pieces.

* `Leaf.pathBytes`: one byte `0`/`1` per node on the path from the root to the leaf; path bytes are
  prefix-free (`Leaf.pathBytes_append_inj`).
* `ItemCodec.parseN`: exactly `c` items from position `r` on.
* `ItemCodec.serChains C qs chains`, `ItemCodec.parseChains C qs`: the item bytes of a full chain
  for each of the leaves `qs`, and their parse (`parseChains_serChains`, `ser_of_parseChains`).
-/

/-! ### Leaf labels -/

namespace GordieHowe.IOP.SPTerm.Leaf

open GordieHowe.QROM

variable {ι : Type}

/-- **The path bytes of a leaf**: `0` for each step into a first subterm, `1` for each step into a
second subterm. -/
def pathBytes : {t : SPTerm ι} → t.Leaf → List Byte
  | _, .here _ => []
  | _, .left p => 0 :: p.pathBytes
  | _, .right p => 1 :: p.pathBytes

/-- **The path bytes of component `i`'s leaf of `nodeN k m c`**: `i` steps into a second subterm,
one into a first, then the leaf's own. -/
theorem length_pathBytes_inN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (i : Fin m) →
    (p : (c i).Leaf) → (Leaf.inN k m i p).pathBytes.length = i + 1 + p.pathBytes.length
  | 0, _, i, _ => i.elim0
  | m + 1, c, i, p => by
    induction i using Fin.cases with
    | zero =>
      change (0 :: p.pathBytes).length = _
      simp only [List.length_cons, Fin.val_zero]
      omega
    | succ i =>
      change (1 :: (Leaf.inN k m (c := fun i => c i.succ) i p).pathBytes).length = _
      rw [List.length_cons, length_pathBytes_inN k m (c := fun i => c i.succ) i p, Fin.val_succ]
      omega

/-- **Path bytes are prefix-free**: two leaves whose path bytes followed by any bytes agree are
equal, and so are the bytes that follow. -/
theorem pathBytes_append_inj : ∀ {t : SPTerm ι} {p p' : t.Leaf} {s s' : List Byte},
    p.pathBytes ++ s = p'.pathBytes ++ s' → p = p' ∧ s = s'
  | _, .here _, .here _, _, _, h => ⟨rfl, by simpa [pathBytes] using h⟩
  | _, .left _, .left _, _, _, h => by
    simp only [pathBytes, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := pathBytes_append_inj h
    exact ⟨rfl, rfl⟩
  | _, .right _, .right _, _, _, h => by
    simp only [pathBytes, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := pathBytes_append_inj h
    exact ⟨rfl, rfl⟩
  | _, .left _, .right _, _, _, h => by simp [pathBytes] at h
  | _, .right _, .left _, _, _, h => by simp [pathBytes] at h

end GordieHowe.IOP.SPTerm.Leaf

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Enc

variable {ι : Type} {k L : ℕ}

/-! ### Exact item counts -/

namespace ItemCodec

variable {m : ℕ} {P : ProtocolSpec m} {Wr : P.MessageIdx → Type}
  (C : (i : P.MessageIdx) → WriteCodec (Wr i))

/-- Read exactly `c` items from position `r` on, returning the rest of the input.

Running time: `c` item parses. This running time is argued here, not proved in Lean. -/
def parseN : ℕ → ℕ → List Byte → Option (List (Item k (Σ i, Wr i)) × List Byte)
  | 0, _, s => some ([], s)
  | c + 1, r, s => (parseAt C r s).bind fun p =>
      (parseN c (r + 1) p.2).map fun q => (p.1 :: q.1, q.2)

theorem parseN_serList (l : List (Item k (Σ i, Wr i))) :
    ∀ r, (∀ j (hj : j < l.length), Fits P (r + j) l[j]) →
      ∀ u, parseN C l.length r (serList C l ++ u) = some (l, u) := by
  induction l with
  | nil => intro r _ u; rfl
  | cons it l ih =>
    intro r hf u
    have hl : ∀ j (hj : j < l.length), Fits P (r + 1 + j) l[j] := fun j hj => by
      have := hf (j + 1) (by simp; omega)
      rwa [show r + (j + 1) = r + 1 + j by omega] at this
    have hit : Fits P r it := hf 0 (by simp)
    have hs : serList C (it :: l) ++ u = ser C it ++ (serList C l ++ u) := by
      simp [serList]
    rw [List.length_cons, hs, parseN, parseAt_ser C hit,
      Option.bind_some, ih (r + 1) hl u]
    rfl

theorem ser_of_parseN : ∀ (c r : ℕ) {s u : List Byte} {l : List (Item k (Σ i, Wr i))},
    parseN C c r s = some (l, u) → s = serList C l ++ u
  | 0, _, s, u, l, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
    rfl
  | c + 1, r, s, u, l, h => by
    rw [parseN] at h
    obtain ⟨⟨it, v⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨l', w⟩, hn, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    dsimp only at hn ⊢
    rw [(ser_parseAt C hp).1, ser_of_parseN c (r + 1) hn]
    simp [serList]

/-- **Items read by `parseN` fit their positions.** -/
theorem fits_of_parseN : ∀ (c r : ℕ) {s u : List Byte} {l : List (Item k (Σ i, Wr i))},
    parseN C c r s = some (l, u) → ∀ j (hj : j < l.length), Fits P (r + j) l[j]
  | 0, _, s, u, l, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
    intro j hj
    simp at hj
  | c + 1, r, s, u, l, h => by
    rw [parseN] at h
    obtain ⟨⟨it, v⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨l', w⟩, hn, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    intro j hj
    cases j with
    | zero => simpa using (ser_parseAt C hp).2
    | succ j =>
      have := fits_of_parseN c (r + 1) hn j (by simp at hj; omega)
      rw [show r + 1 + j = r + (j + 1) by omega] at this
      simpa using this

/-- `parseN` reads exactly the requested number of items. -/
theorem length_of_parseN : ∀ (c r : ℕ) {s u : List Byte} {l : List (Item k (Σ i, Wr i))},
    parseN C c r s = some (l, u) → l.length = c
  | 0, _, s, u, l, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
    rfl
  | c + 1, r, s, u, l, h => by
    rw [parseN] at h
    obtain ⟨⟨it, v⟩, hp, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨l', w⟩, hn, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp [length_of_parseN c (r + 1) hn]

/-- A chain of `c` items followed by any bytes parses as `c` items. -/
theorem parseN_serList_of_length {l : List (Item k (Σ i, Wr i))} {c : ℕ} (hc : l.length = c)
    {r : ℕ} (hf : ∀ j (hj : j < l.length), Fits P (r + j) l[j]) (u : List Byte) :
    parseN C c r (serList C l ++ u) = some (l, u) := by
  subst hc
  exact parseN_serList C l r hf u

end ItemCodec

/-! ### Lists of key–value pairs -/

/-- A list search that succeeds at exactly one element returns that element's result. -/
theorem _root_.List.findSome?_eq_of_unique {α β : Type*} {f : α → Option β} {l : List α} {a : α}
    {b : β} (ha : a ∈ l) (hfa : f a = some b) (h : ∀ a' ∈ l, a' ≠ a → f a' = none) :
    l.findSome? f = some b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases hx : x = a
    · subst hx
      simp [hfa]
    · rw [List.findSome?_cons, h x (List.mem_cons_self) hx]
      exact ih ((List.mem_cons.1 ha).resolve_left (Ne.symm hx))
        fun a' ha' hne => h a' (List.mem_cons_of_mem _ ha') hne

/-- The lookup of a key in a list of key–value pairs built from a function. -/
theorem _root_.List.dlookup_map_mk {α : Type*} {β : α → Type*} [DecidableEq α] (f : (a : α) → β a)
    (a : α) : ∀ l : List α, (l.map fun q => (⟨q, f q⟩ : Sigma β)).dlookup a =
      if a ∈ l then some (f a) else none
  | [] => by simp
  | x :: xs => by
    by_cases hx : a = x
    · subst hx
      simp [List.dlookup_cons_eq]
    · rw [List.map_cons, List.dlookup_cons_ne _ _ hx, List.dlookup_map_mk f a xs]
      simp [hx]

/-- A list of key–value pairs with distinct keys is its keys, each with its looked-up value. -/
theorem _root_.List.eq_map_dlookup {α : Type*} {β : α → Type*} [DecidableEq α] (d : (a : α) → β a) :
    ∀ {l : List (Sigma β)}, l.NodupKeys →
      l = l.keys.map fun q => (⟨q, (l.dlookup q).getD (d q)⟩ : Sigma β)
  | [], _ => rfl
  | ⟨a, b⟩ :: l, h => by
    rw [List.nodupKeys_cons] at h
    conv_lhs => rw [List.eq_map_dlookup d h.2]
    simp only [List.keys_cons, List.map_cons, List.dlookup_cons_eq, Option.getD_some]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    have hne : q ≠ a := fun e => h.1 (e ▸ hq)
    rw [List.dlookup_cons_ne _ _ hne]

namespace ItemCodec

variable {t : SPTerm ι} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  {Wr : (j : ι) → (P j).MessageIdx → Type}
  (C : (j : ι) → (i : (P j).MessageIdx) → WriteCodec (Wr j i))

/-- The item bytes of the chains of the leaves `qs`, one after the other. -/
def serChains (qs : List t.Leaf) (chains : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))) :
    List Byte :=
  qs.flatMap fun q => ItemCodec.serList (C q.label) (chains q)

/-- Read a full chain for each of the leaves `qs`, one after the other.

Running time: one `ItemCodec.parseN` per leaf, `n` item parses each.
This running time is argued here, not proved in Lean. -/
def parseChains : List t.Leaf → List Byte →
    Option (List (Σ q : t.Leaf, List (Item k (Σ i, Wr q.label i))) × List Byte)
  | [], s => some ([], s)
  | q :: qs, s => (ItemCodec.parseN (C q.label) (n q.label) 0 s).bind fun p =>
      (parseChains qs p.2).map fun r => (⟨q, p.1⟩ :: r.1, r.2)

theorem parseChains_serChains (chains : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))) :
    ∀ qs : List t.Leaf, (∀ q ∈ qs, chainWF (P q.label) (chains q) ∧
      (chains q).length = n q.label) → ∀ u,
      parseChains C qs (serChains C qs chains ++ u) = some (qs.map fun q => ⟨q, chains q⟩, u)
  | [], _, u => rfl
  | q :: qs, h, u => by
    obtain ⟨hw, hl⟩ := h q List.mem_cons_self
    have e : serChains C (q :: qs) chains ++ u =
        ItemCodec.serList (C q.label) (chains q) ++ (serChains C qs chains ++ u) := by
      simp [serChains]
    rw [e, parseChains,
      ItemCodec.parseN_serList_of_length (C q.label) hl (fun j hj => by simpa using hw j hj),
      Option.bind_some, parseChains_serChains chains qs (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
        u]
    rfl

theorem ser_of_parseChains : ∀ (qs : List t.Leaf) {s u : List Byte}
    {ls : List (Σ q : t.Leaf, List (Item k (Σ i, Wr q.label i)))},
    parseChains C qs s = some (ls, u) →
      ls.keys = qs ∧ s = ls.flatMap (fun e => ItemCodec.serList (C e.1.label) e.2) ++ u
  | [], s, u, ls, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
    exact ⟨rfl, rfl⟩
  | q :: qs, s, u, ls, h => by
    rw [parseChains] at h
    obtain ⟨⟨l, v⟩, hn, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ls', w⟩, hc, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    dsimp only at hc ⊢
    obtain ⟨hk, hs⟩ := ser_of_parseChains qs hc
    refine ⟨by rw [List.keys_cons, hk], ?_⟩
    rw [ItemCodec.ser_of_parseN (C q.label) _ _ hn, hs]
    simp

theorem length_serChains_le {B : ℕ} (hB : ∀ j i, (C j i).B ≤ B) (qs : List t.Leaf)
    (chains : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))) :
    (serChains C qs chains).length ≤ (qs.map fun q => (chains q).length).sum * max B (9 + k) := by
  induction qs with
  | nil => simp [serChains]
  | cons q qs ih =>
    have := ItemCodec.length_serList_le (C q.label) (hB q.label) (chains q)
    simp only [serChains, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      Nat.add_mul] at ih ⊢
    omega

end ItemCodec

end GordieHowe.SPBCS
