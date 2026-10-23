-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.Codec
public import GordieHowe.Model.IOP.CausalLeaves
public import Mathlib.Data.List.Sigma

@[expose] public section

/-!
# Chain inputs of a series–parallel composition

The Fiat–Shamir compiler on a series–parallel term `t` (`GordieHowe.SPBCS.FullPast`, `GordieHowe/Model/IOP/Causal.lean`) derives the
challenge of round `r` of leaf `p` from a hash of that challenge's causal past: the Fiat–Shamir
salt, the statement, the leaf's label, the chains of every leaf sequenced before `p`, and the
first `r` items of `p`'s own chain (its writes and absorbed digests). This file fixes what a chain
input holds and how it is encoded.

* `CausalChain t k W`: the content of a chain input at the term `t`: the leaf `leaf`, a chain for
  every leaf (`chains`; only those of the leaves before `leaf` are read) and the leaf's own items
  `own`. `CausalChain.WF`: the chains of the leaves before `leaf` are full well-formed chains, the
  others are empty, and `own` is a well-formed proper prefix (a challenge prefix).
* `CausalEncoding`: the laws a chain-input encoding must satisfy: a decoder that inverts the
  encoding on well-formed content (unique decodability), whose decoded strings are encodings, and a
  bound on the digests one input carries.
* `CausalEncoding.bytes`: the byte encoding: the writes before round 0 (`CX`: label, salt,
  statement), the leaf's label (`Leaf.pathLabel`: its path from the root, one byte `0`/`1` per
  node, or nothing in a par-free term), then the item bytes of the chains of the leaves before the
  leaf in term order, then its own items, each item as in `ItemCodec`.

**Unique decodability.** In a term with a `par` node the path determines the leaf, and the path
bytes of two leaves are never one a prefix of the other (`Leaf.pathBytes_append_inj`). In a
par-free term no label is written; the leaves are totally ordered and the decoder tries each leaf
in term order. For a leaf `p'` before the true leaf `p`, the bytes hold `p'`'s full chain followed
by more bytes or by nothing, and neither is a challenge prefix of `p'`; for a leaf `p'` after `p`,
the decoder would need a full chain of `p` where the bytes hold a proper prefix. So exactly one
leaf parses (`decodeBytes_bytesOf`).

**The total-order case.** In a par-free term the label is empty (`Leaf.pathLabel_of_parFree`).
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

open Classical in
/-- **The label of a leaf in a chain input**: its path bytes, or nothing when the term is
par-free (its leaves are then told apart by the number of items before the challenge). -/
def pathLabel {t : SPTerm ι} (p : t.Leaf) : List Byte := if t.ParFree then [] else p.pathBytes

/-- In a par-free term no label is written. -/
@[simp] theorem pathLabel_of_parFree {t : SPTerm ι} (ht : t.ParFree) (p : t.Leaf) :
    p.pathLabel = [] := by
  simp [pathLabel, ht]

theorem pathLabel_of_not_parFree {t : SPTerm ι} (ht : ¬ t.ParFree) (p : t.Leaf) :
    p.pathLabel = p.pathBytes := by
  simp [pathLabel, ht]

end GordieHowe.IOP.SPTerm.Leaf

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Enc

variable {ι : Type} {k L : ℕ}

/-! ### Chain-input content -/

/-- **The content of a chain input** at the term `t`: the leaf of the challenge, a chain of items
for every leaf (only the chains of the leaves sequenced before `leaf` are part of the causal past;
`WF` requires the others to be empty), and the leaf's own items before the challenge. Items of
leaf `q` carry writes of type `W q.label`. -/
structure CausalChain (t : SPTerm ι) (k : ℕ) (W : ι → Type) where
  /-- The leaf of the challenge. -/
  leaf : t.Leaf
  /-- The chain of every leaf; those of the leaves before `leaf` are read. -/
  chains : (q : t.Leaf) → List (Item k (W q.label))
  /-- The leaf's own items before the challenge. -/
  own : List (Item k (W leaf.label))

namespace CausalChain

variable {t : SPTerm ι} {W : ι → Type}

/-- **Well-formed chain-input content** for components of `n j` rounds with well-formed chains
`WFi j`: the chains of the leaves before `leaf` are full well-formed chains, the other chains are
empty, and the own items are a well-formed proper prefix (the prefix before a challenge round). -/
structure WF (n : ι → ℕ) (WFi : (j : ι) → List (Item k (W j)) → Prop) (ch : CausalChain t k W) :
    Prop where
  /-- The chains of the leaves before are well formed. -/
  chains_wf : ∀ q, q.Before ch.leaf → WFi q.label (ch.chains q)
  /-- The chains of the leaves before are full. -/
  chains_length : ∀ q, q.Before ch.leaf → (ch.chains q).length = n q.label
  /-- The other chains are empty. -/
  chains_nil : ∀ q, ¬ q.Before ch.leaf → ch.chains q = []
  /-- The own items are well formed. -/
  own_wf : WFi ch.leaf.label ch.own
  /-- The own items are a proper prefix. -/
  own_length : ch.own.length < n ch.leaf.label

/-- The digests carried by chain-input content: those of every chain and of the own items. -/
def digests (dg : (j : ι) → W j → Finset (Digest k)) (ch : CausalChain t k W) : Finset (Digest k) :=
  (Finset.univ.biUnion fun q => chainDigests (dg q.label) (ch.chains q)) ∪
    chainDigests (dg ch.leaf.label) ch.own

/-- The number of items of chain-input content. -/
def size (ch : CausalChain t k W) : ℕ := (∑ q, (ch.chains q).length) + ch.own.length

/-- Content of `size` items carrying at most `nd ≥ 1` digests each carries at most `size · nd`. -/
theorem card_digests_le {dg : (j : ι) → W j → Finset (Digest k)} {nd : ℕ}
    (hdg : ∀ j w, (dg j w).card ≤ nd) (hnd : 1 ≤ nd) (ch : CausalChain t k W) :
    (ch.digests dg).card ≤ ch.size * nd := by
  unfold digests size
  refine (Finset.card_union_le _ _).trans ?_
  rw [Nat.add_mul, Finset.sum_mul]
  refine Nat.add_le_add (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ => ?_)) ?_
  · exact card_chainDigests_le (hdg _) hnd _
  · exact card_chainDigests_le (hdg _) hnd _

/-- **Well-formed content has at most as many items as all components have rounds.** -/
theorem size_le {n : ι → ℕ} {WFi : (j : ι) → List (Item k (W j)) → Prop} {ch : CausalChain t k W}
    (h : ch.WF n WFi) : ch.size ≤ ∑ q : t.Leaf, n q.label := by
  classical
  have hp : (ch.chains ch.leaf).length = 0 := by
    rw [h.chains_nil _ (Leaf.not_before_self _), List.length_nil]
  unfold size
  rw [← Finset.sum_erase (f := fun q => (ch.chains q).length) Finset.univ hp, ← Finset.sum_erase_add _ _ (Finset.mem_univ ch.leaf)]
  refine Nat.add_le_add (Finset.sum_le_sum fun q _ => ?_) h.own_length.le
  by_cases hq : q.Before ch.leaf
  · exact (h.chains_length q hq).le
  · rw [h.chains_nil q hq]
    exact Nat.zero_le _

end CausalChain

/-! ### Chain-input encodings -/

/-- **A chain-input encoding** at the term `t` (module docstring): the byte encoding of a value
in `X` (the Fiat–Shamir salt and the statement) followed by chain-input content, the input of the
`transcript` role. The fields:
- `decode_encode`: on well-formed content the decoder inverts the encoding (unique
  decodability);
- `encode_decode`: a decoded string is the encoding of its parse;
- `digest_mem`: the digests of an input contain those of well-formed content;
- `card_digestsOf_le`: an input contains at most `digestsPerInput` digests. -/
structure CausalEncoding (k L : ℕ) (t : SPTerm ι) (n : ι → ℕ) (X : Type) (W : ι → Type)
    (dg : (j : ι) → W j → Finset (Digest k)) (WFi : (j : ι) → List (Item k (W j)) → Prop) where
  /-- The input bytes. -/
  encode : X → CausalChain t k W → Bytes L
  /-- The parse of input bytes. -/
  decode : Bytes L → Option (X × CausalChain t k W)
  /-- The digests of input bytes. -/
  digestsOf : Bytes L → Finset (Digest k)
  /-- The bound on the digests of one input. -/
  digestsPerInput : ℕ
  decode_encode : ∀ x ch, ch.WF n WFi → decode (encode x ch) = some (x, ch)
  encode_decode : ∀ b x ch, decode b = some (x, ch) → encode x ch = b
  digest_mem : ∀ x ch, ch.WF n WFi → ch.digests dg ⊆ digestsOf (encode x ch)
  card_digestsOf_le : ∀ b, (digestsOf b).card ≤ digestsPerInput

namespace CausalEncoding

variable {t : SPTerm ι} {n : ι → ℕ} {X : Type} {W : ι → Type}
  {dg : (j : ι) → W j → Finset (Digest k)} {WFi : (j : ι) → List (Item k (W j)) → Prop}

/-- **A chain input determines the salted statement and the content.** -/
theorem encode_injective (E : CausalEncoding k L t n X W dg WFi) {x x' : X}
    {ch ch' : CausalChain t k W} (hw : ch.WF n WFi) (hw' : ch'.WF n WFi)
    (h : E.encode x ch = E.encode x' ch') : x = x' ∧ ch = ch' :=
  Prod.mk.inj (Option.some_inj.1
    ((E.decode_encode x ch hw).symm.trans (h ▸ E.decode_encode x' ch' hw')))

end CausalEncoding

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

theorem parseAt_nil (r : ℕ) : parseAt (k := k) C r [] = none := by
  rcases h : parseAt (k := k) C r [] with _ | ⟨it, u⟩
  · rfl
  · exact absurd (List.append_eq_nil_iff.1 (ser_parseAt C h).1.symm).1 (ser_ne_nil C it)

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

/-- Fewer items than requested do not parse. -/
theorem parseN_serList_of_lt (l : List (Item k (Σ i, Wr i))) :
    ∀ r c, (∀ j (hj : j < l.length), Fits P (r + j) l[j]) → l.length < c →
      parseN (k := k) C c r (serList C l) = none := by
  induction l with
  | nil =>
    intro r c _ hc
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by simp at hc; omega⟩
    simp [parseN, serList, parseAt_nil]
  | cons it l ih =>
    intro r c hf hc
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by simp at hc; omega⟩
    have hl : ∀ j (hj : j < l.length), Fits P (r + 1 + j) l[j] := fun j hj => by
      have := hf (j + 1) (by simp; omega)
      rwa [show r + (j + 1) = r + 1 + j by omega] at this
    have hit : Fits P r it := hf 0 (by simp)
    have hs : serList C (it :: l) = ser C it ++ serList C l := by simp [serList]
    rw [hs, parseN, parseAt_ser C hit, Option.bind_some,
      ih (r + 1) c hl (by simp at hc; omega)]
    rfl

/-- A full chain followed by more bytes does not parse as a chain. -/
theorem parseList_serList_append_of_ne_nil (l : List (Item k (Σ i, Wr i))) :
    ∀ r, (∀ j (hj : j < l.length), Fits P (r + j) l[j]) → r + l.length = m →
      ∀ s, s ≠ [] → ∀ fuel, parseList (k := k) C fuel r (serList C l ++ s) = none := by
  induction l with
  | nil =>
    intro r _ hr s hs fuel
    obtain ⟨b, s, rfl⟩ := List.exists_cons_of_ne_nil hs
    cases fuel with
    | zero => rfl
    | succ fuel =>
      have : parseAt (k := k) C r (b :: s) = none := by
        simp only [List.length_nil, Nat.add_zero] at hr
        simp [parseAt, hr]
      simp only [serList, List.map_nil, List.flatten_nil, List.nil_append, parseList, this]
      rfl
  | cons it l ih =>
    intro r hf hr s hs fuel
    have hl : ∀ j (hj : j < l.length), Fits P (r + 1 + j) l[j] := fun j hj => by
      have := hf (j + 1) (by simp; omega)
      rwa [show r + (j + 1) = r + 1 + j by omega] at this
    obtain ⟨b, v, hbv⟩ := List.exists_cons_of_ne_nil (ser_ne_nil C it)
    have he : serList C (it :: l) ++ s = b :: (v ++ (serList C l ++ s)) := by
      simp [serList, hbv]
    cases fuel with
    | zero => rw [he]; rfl
    | succ fuel =>
      have hp : parseAt C r (b :: (v ++ (serList C l ++ s))) = some (it, serList C l ++ s) := by
        rw [← List.cons_append, ← hbv]
        exact parseAt_ser C (hf 0 (by simp)) _
      rw [he, parseList, hp, Option.bind_some,
        ih (r + 1) hl (by simp at hr; omega) s hs fuel]
      rfl

end ItemCodec

/-! ### The byte encoding -/

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

namespace CausalEncoding

variable {t : SPTerm ι} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  {Wr : (j : ι) → (P j).MessageIdx → Type}
  (C : (j : ι) → (i : (P j).MessageIdx) → WriteCodec (Wr j i)) {X : Type} (CX : Codec X)

/-- The item bytes of the chains of the leaves `qs`, one after the other. -/
def serCtx (qs : List t.Leaf) (chains : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))) :
    List Byte :=
  qs.flatMap fun q => ItemCodec.serList (C q.label) (chains q)

/-- **The bytes of a chain input**: the writes before round 0 (`CX`), the leaf's label, the item
bytes of the chains of the leaves before it in term order, then its own items. -/
def bytesOf (x : X) (ch : CausalChain t k fun j => Σ i, Wr j i) : List Byte :=
  CX.ser x ++ ch.leaf.pathLabel ++ serCtx C ch.leaf.ctxList ch.chains ++
    ItemCodec.serList (C ch.leaf.label) ch.own

/-- Read a full chain for each of the leaves `qs`, one after the other.

Running time: one `ItemCodec.parseN` per leaf, `n` item parses each.
This running time is argued here, not proved in Lean. -/
def parseCtx : List t.Leaf → List Byte →
    Option (List (Σ q : t.Leaf, List (Item k (Σ i, Wr q.label i))) × List Byte)
  | [], s => some ([], s)
  | q :: qs, s => (ItemCodec.parseN (C q.label) (n q.label) 0 s).bind fun p =>
      (parseCtx qs p.2).map fun r => (⟨q, p.1⟩ :: r.1, r.2)

theorem parseCtx_append (qs qs' : List t.Leaf) (s : List Byte) :
    parseCtx (k := k) C (qs ++ qs') s = (parseCtx (k := k) C qs s).bind fun r =>
      (parseCtx (k := k) C qs' r.2).map fun r' => (r.1 ++ r'.1, r'.2) := by
  induction qs generalizing s with
  | nil => simp [parseCtx]
  | cons q qs ih =>
    simp only [List.cons_append, parseCtx]
    rcases ItemCodec.parseN (C q.label) (n q.label) 0 s with _ | ⟨l, u⟩
    · rfl
    · simp only [Option.bind_some, ih]
      rcases parseCtx C qs u with _ | ⟨ls, v⟩
      · rfl
      · simp only [Option.map_some, Option.bind_some]
        rcases parseCtx C qs' v with _ | ⟨ls', w⟩ <;> rfl

theorem parseCtx_serCtx (chains : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))) :
    ∀ qs : List t.Leaf, (∀ q ∈ qs, chainWF (P q.label) (chains q) ∧
      (chains q).length = n q.label) → ∀ u,
      parseCtx C qs (serCtx C qs chains ++ u) = some (qs.map fun q => ⟨q, chains q⟩, u)
  | [], _, u => rfl
  | q :: qs, h, u => by
    obtain ⟨hw, hl⟩ := h q List.mem_cons_self
    have e : serCtx C (q :: qs) chains ++ u =
        ItemCodec.serList (C q.label) (chains q) ++ (serCtx C qs chains ++ u) := by
      simp [serCtx]
    rw [e, parseCtx,
      ItemCodec.parseN_serList_of_length (C q.label) hl (fun j hj => by simpa using hw j hj),
      Option.bind_some, parseCtx_serCtx chains qs (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
        u]
    rfl

theorem ser_of_parseCtx : ∀ (qs : List t.Leaf) {s u : List Byte}
    {ls : List (Σ q : t.Leaf, List (Item k (Σ i, Wr q.label i)))},
    parseCtx C qs s = some (ls, u) →
      ls.keys = qs ∧ s = ls.flatMap (fun e => ItemCodec.serList (C e.1.label) e.2) ++ u
  | [], s, u, ls, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
    exact ⟨rfl, rfl⟩
  | q :: qs, s, u, ls, h => by
    rw [parseCtx] at h
    obtain ⟨⟨l, v⟩, hn, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ls', w⟩, hc, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    dsimp only at hc ⊢
    obtain ⟨hk, hs⟩ := ser_of_parseCtx qs hc
    refine ⟨by rw [List.keys_cons, hk], ?_⟩
    rw [ItemCodec.ser_of_parseN (C q.label) _ _ hn, hs]
    simp

/-- **Parse a chain input's content at the candidate leaf `p`**: strip `p`'s label, read the
full chains of the leaves before `p`, read the rest as `p`'s own items, and accept only a proper
prefix.

Running time: a label comparison, one `parseCtx`, one `ItemCodec.parseList`.
This running time is argued here, not proved in Lean. -/
def tryAt (s : List Byte) (p : t.Leaf) : Option (CausalChain t k fun j => Σ i, Wr j i) :=
  (strip p.pathLabel s).bind fun u => (parseCtx (k := k) C p.ctxList u).bind fun r =>
    (ItemCodec.parseList (C p.label) r.2.length 0 r.2).bind fun own =>
      if own.length < n p.label then some ⟨p, fun q => (r.1.dlookup q).getD [], own⟩ else none

/-- **Decode a chain input**: the decoder of `CX`, then the first leaf in term order at which the
rest parses (`tryAt`).

Running time: one run of `CX.parse`, then at most one `tryAt` per leaf.
This running time is argued here, not proved in Lean. -/
def decodeBytes (s : List Byte) : Option (X × CausalChain t k fun j => Σ i, Wr j i) :=
  (CX.parse s).bind fun r => (t.leaves.findSome? (tryAt C r.2)).map (r.1, ·)

variable {C CX}

/-- The rest of a chain input after the writes before round 0. -/
theorem bytesOf_eq (x : X) (ch : CausalChain t k fun j => Σ i, Wr j i) :
    bytesOf C CX x ch = CX.ser x ++ (ch.leaf.pathLabel ++ (serCtx C ch.leaf.ctxList ch.chains ++
      ItemCodec.serList (C ch.leaf.label) ch.own)) := by
  simp [bytesOf, List.append_assoc]

/-- The content parses at its own leaf. -/
theorem tryAt_self {ch : CausalChain t k fun j => Σ i, Wr j i}
    (h : ch.WF n fun j => chainWF (P j)) :
    tryAt C (ch.leaf.pathLabel ++ (serCtx C ch.leaf.ctxList ch.chains ++
      ItemCodec.serList (C ch.leaf.label) ch.own)) ch.leaf = some ch := by
  rcases ch with ⟨p, chains, own⟩
  have hctx := parseCtx_serCtx (C := C) chains p.ctxList (fun q hq =>
    ⟨h.chains_wf q (Leaf.mem_ctxList.1 hq), h.chains_length q (Leaf.mem_ctxList.1 hq)⟩)
    (ItemCodec.serList (C p.label) own)
  have hown := ItemCodec.parseList_serList (C p.label) own 0
    (fun j hj => by simpa using h.own_wf j hj) _ le_rfl
  simp only [tryAt, strip_append, Option.bind_some, hctx, hown, h.own_length, ↓reduceIte]
  congr 2
  funext q
  rw [List.dlookup_map_mk]
  split_ifs with hq
  · rfl
  · exact (h.chains_nil q (fun hb => hq (Leaf.mem_ctxList.2 hb))).symm

/-- **The content parses at no other leaf** (module docstring). -/
theorem tryAt_other {ch : CausalChain t k fun j => Σ i, Wr j i}
    (h : ch.WF n fun j => chainWF (P j)) {p' : t.Leaf} (hne : p' ≠ ch.leaf) :
    tryAt (k := k) C (ch.leaf.pathLabel ++ (serCtx C ch.leaf.ctxList ch.chains ++
      ItemCodec.serList (C ch.leaf.label) ch.own)) p' = none := by
  rcases ch with ⟨p, chains, own⟩
  dsimp only at hne h ⊢
  have hwf : ∀ q, q.Before p → chainWF (P q.label) (chains q) ∧ (chains q).length = n q.label :=
    fun q hq => ⟨h.chains_wf q hq, h.chains_length q hq⟩
  by_cases ht : t.ParFree
  · rw [Leaf.pathLabel_of_parFree ht, List.nil_append]
    unfold tryAt
    rw [Leaf.pathLabel_of_parFree ht, strip, Option.bind_some]
    rcases ParFree.before_or_before ht p' p hne with hb | hb
    · -- `p'` before `p`: its full chain is followed by more bytes or by nothing.
      obtain ⟨M, hM⟩ := ParFree.ctxList_of_before ht hb
      have e : serCtx C p.ctxList chains ++ ItemCodec.serList (C p.label) own =
          serCtx C p'.ctxList chains ++ (ItemCodec.serList (C p'.label) (chains p') ++
            (serCtx C M chains ++ ItemCodec.serList (C p.label) own)) := by
        simp [hM, serCtx, List.flatMap_append, List.append_assoc]
      rw [e, parseCtx_serCtx C chains p'.ctxList (fun q hq =>
        hwf q ((Leaf.mem_ctxList.1 hq).trans hb)), Option.bind_some]
      dsimp only
      obtain ⟨hw', hl'⟩ := hwf p' hb
      by_cases hrest : serCtx C M chains ++ ItemCodec.serList (C p.label) own = []
      · rw [hrest, List.append_nil,
          ItemCodec.parseList_serList (C p'.label) (chains p') 0 (fun j hj => by simpa using hw' j hj)
            _ le_rfl, Option.bind_some]
        simp [hl']
      · rw [ItemCodec.parseList_serList_append_of_ne_nil (C p'.label) (chains p') 0
          (fun j hj => by simpa using hw' j hj) (by omega) _ hrest]
        rfl
    · -- `p` before `p'`: a full chain of `p` would be needed where its bytes are a proper prefix.
      obtain ⟨M, hM⟩ := ParFree.ctxList_of_before ht hb
      rw [hM, parseCtx_append, parseCtx_serCtx C chains p.ctxList (fun q hq =>
        hwf q (Leaf.mem_ctxList.1 hq)), Option.bind_some]
      dsimp only
      rw [parseCtx, ItemCodec.parseN_serList_of_lt (C p.label) own 0 _
        (fun j hj => by simpa using h.own_wf j hj) h.own_length]
      rfl
  · -- With a `par` node the labels differ.
    unfold tryAt
    rw [Leaf.pathLabel_of_not_parFree ht p, Leaf.pathLabel_of_not_parFree ht p']
    rcases hs : strip p'.pathBytes (p.pathBytes ++ (serCtx C p.ctxList chains ++
      ItemCodec.serList (C p.label) own)) with _ | u
    · rfl
    · exact absurd (Leaf.pathBytes_append_inj (eq_of_strip hs)).1.symm hne

/-- **Unique decodability**: the decoder reads well-formed content back from its bytes. -/
theorem decodeBytes_bytesOf {x : X} {ch : CausalChain t k fun j => Σ i, Wr j i}
    (h : ch.WF n fun j => chainWF (P j)) : decodeBytes C CX (bytesOf C CX x ch) = some (x, ch) := by
  rw [decodeBytes, bytesOf_eq, CX.parse_ser, Option.bind_some,
    List.findSome?_eq_of_unique (mem_leaves ch.leaf) (tryAt_self h)
      fun p' _ hne => tryAt_other h hne]
  rfl

/-- **Decoded bytes are an encoding.** -/
theorem bytesOf_of_decodeBytes {s : List Byte} {x : X} {ch : CausalChain t k fun j => Σ i, Wr j i}
    (h : decodeBytes C CX s = some (x, ch)) : bytesOf C CX x ch = s := by
  obtain ⟨⟨x', v⟩, hx, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ch', hf, he⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some hf
  rw [CX.ser_parse hx]
  unfold tryAt at hp
  obtain ⟨u, hu, hp⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨⟨ls, w⟩, hc, hp⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨own, ho, hp⟩ := Option.bind_eq_some_iff.1 hp
  split_ifs at hp with hlt
  obtain rfl := Option.some_inj.1 hp
  dsimp only at hu ho ⊢
  obtain ⟨hk, hs⟩ := ser_of_parseCtx C p.ctxList hc
  have hnd : ls.NodupKeys := by
    unfold List.NodupKeys
    rw [hk]
    exact Leaf.nodup_ctxList p
  have hls := List.eq_map_dlookup (fun _ => ([] : List _)) hnd
  rw [bytesOf_eq, eq_of_strip hu, hs, ItemCodec.serList_of_parseList _ _ _ ho]
  dsimp only
  congr 3
  conv_rhs => rw [hls, hk]
  simp [serCtx, List.flatMap_map]

variable (C CX)

theorem length_serCtx_le {B : ℕ} (hB : ∀ j i, (C j i).B ≤ B) (qs : List t.Leaf)
    (chains : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))) :
    (serCtx C qs chains).length ≤ (qs.map fun q => (chains q).length).sum * max B (9 + k) := by
  induction qs with
  | nil => simp [serCtx]
  | cons q qs ih =>
    have := ItemCodec.length_serList_le (C q.label) (hB q.label) (chains q)
    simp only [serCtx, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons,
      Nat.add_mul] at ih ⊢
    omega

/-- **The length of a chain input**: the writes before round 0, the label, and at most
`max B (9 + k)` bytes for each item. -/
theorem length_bytesOf_le {B : ℕ} (hB : ∀ j i, (C j i).B ≤ B) (x : X)
    (ch : CausalChain t k fun j => Σ i, Wr j i) :
    (bytesOf C CX x ch).length ≤
      (CX.ser x).length + ch.leaf.pathLabel.length + ch.size * max B (9 + k) := by
  classical
  have h1 := length_serCtx_le C hB ch.leaf.ctxList ch.chains
  have h2 := ItemCodec.length_serList_le (C ch.leaf.label) (hB _) ch.own
  have h3 : (ch.leaf.ctxList.map fun q => (ch.chains q).length).sum ≤
      ∑ q, (ch.chains q).length := by
    rw [← List.sum_toFinset _ (Leaf.nodup_ctxList ch.leaf)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h4 := Nat.mul_le_mul_right (max B (9 + k)) h3
  simp only [bytesOf, List.length_append, CausalChain.size, Nat.add_mul]
  omega

variable (dg : (j : ι) → (Σ i, Wr j i) → Finset (Digest k)) {nd : ℕ} (B : ℕ)

/-- **The byte encoding of chain inputs** (module docstring), with `decode` the algorithm
`decodeBytes`; `digestsOf b` is the digest set of the parsed content, so an input carries at most
`nd` digests per item and `(∑ q, n q.label) · nd` in all.
- `hdg`, `hnd`: a write carries at most `nd ≥ 1` roots;
- `hB`: every write has at most `B` bytes;
- `hL`: every chain input fits in `L` bytes. -/
def bytes (hdg : ∀ j w, (dg j w).card ≤ nd) (hnd : 1 ≤ nd) (hB : ∀ j i, (C j i).B ≤ B)
    (hL : ∀ x (p : t.Leaf), (CX.ser x).length + p.pathLabel.length +
      (∑ q : t.Leaf, n q.label) * max B (9 + k) ≤ L) :
    CausalEncoding k L t n X (fun j => Σ i, Wr j i) dg (fun j => chainWF (P j)) where
  encode x ch := Bytes.ofList (bytesOf C CX x ch)
  decode b := decodeBytes C CX (Bytes.toList b)
  digestsOf b := match decodeBytes (k := k) (t := t) C CX (Bytes.toList b) with
    | some (_, ch) => if ch.size ≤ ∑ q : t.Leaf, n q.label then ch.digests dg else ∅
    | none => ∅
  digestsPerInput := (∑ q : t.Leaf, n q.label) * nd
  decode_encode x ch h := by
    have hlen := (length_bytesOf_le C CX hB x ch).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (CausalChain.size_le h)) _).trans
        (hL x ch.leaf))
    simp only [Bytes.toList_ofList hlen, decodeBytes_bytesOf h]
  encode_decode b x ch h := by
    rw [bytesOf_of_decodeBytes h, Bytes.ofList_toList]
  digest_mem x ch h := by
    have hlen := (length_bytesOf_le C CX hB x ch).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (CausalChain.size_le h)) _).trans
        (hL x ch.leaf))
    simp [Bytes.toList_ofList hlen, decodeBytes_bytesOf h, CausalChain.size_le h]
  card_digestsOf_le b := by
    split
    · split_ifs with hs
      · exact (CausalChain.card_digests_le hdg hnd _).trans (Nat.mul_le_mul_right _ hs)
      · simp
    · simp

end CausalEncoding

end GordieHowe.SPBCS
