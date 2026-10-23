-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Encoding

@[expose] public section

/-!
# The byte encoding of chain inputs with merges

A byte encoding of the chain inputs of the spBCS compiler (`GordieHowe/SPBCS/Encoding.lean`)
that satisfies `MergeEncoding`, so the spBCS compiler (`GordieHowe.SPBCS`) exists for every
series–parallel term with merges. It follows the paper's challenge-input layout
(`app:bcs-details`, "Challenge inputs"):

* the writes before round 0 (`CX`: label, salt, statement);
* the observer's label (`label`): `0` and the leaf's path bytes (`Leaf.pathBytes`) for a challenge
  round, `1` and the site's code (`SiteLayout.code`) for a branch's final input;
* the item bytes of the full chains of the leaves the observer reads in full, in term order
  (`visList`), as in `CausalEncoding.bytes`;
* the final digest of each branch hidden from the observer, in the layout's site order
  (`hidList`), `k` bytes each;
* for a round, its own items.

`SiteLayout Mg` is a list of the sites without repetitions and a prefix-free code for them;
`MTerm.siteLayout` (`GordieHowe/SPBCS/TermLayout.lean`) gives one for every term with merges.

**Unique decodability** (`decodeBytes_bytesOf`). The tag byte tells rounds from final inputs; the
path bytes of leaves and the codes of sites are prefix-free, so the label determines the observer.
The observer fixes which leaves' full chains follow, each of a known number of items, and which
digests follow, each of `k` bytes; the rest is the own items.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Enc

variable {ι : Type} {k L : ℕ} {t : SPTerm ι}

/-- **A layout of the sites**: a list of all sites without repetitions, and a prefix-free code
of each site. -/
structure SiteLayout (Mg : Merges t) where
  /-- The sites in order. -/
  sites : List Mg.Site
  /-- No site is listed twice. -/
  nodup : sites.Nodup
  /-- Every site is listed. -/
  mem_sites : ∀ s, s ∈ sites
  /-- The code of a site. -/
  code : Mg.Site → List Byte
  /-- The codes are prefix-free. -/
  code_append_inj : ∀ {s s' : Mg.Site} {u u' : List Byte}, code s ++ u = code s' ++ u' →
    s = s' ∧ u = u'

namespace MergeBytes

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  {Wr : (j : ι) → (P j).MessageIdx → Type}
  (C : (j : ι) → (i : (P j).MessageIdx) → WriteCodec (Wr j i)) {X' : Type} (CX : Codec X')
  (Λ : SiteLayout Mg)

/-- The content of a chain input with writes `Wr`. -/
abbrev BContent (Mg : Merges t) (k : ℕ) (Wr : (j : ι) → (P j).MessageIdx → Type) (X' : Type) :
    Type :=
  Content Mg k (fun j => Σ i, Wr j i) X'

/-- **The leaves an observer reads in full**, in term order. -/
def visList (o : Mg.Obs) : List t.Leaf := t.leaves.filter fun q => decide (o.Visible q)

/-- **The branches hidden from an observer**, in the layout's order. -/
def hidList (o : Mg.Obs) : List Mg.Site := Λ.sites.filter fun s => decide (Mg.Hides s o)

theorem mem_visList {o : Mg.Obs} {q : t.Leaf} : q ∈ visList o ↔ o.Visible q := by
  simp [visList, mem_leaves]

theorem mem_hidList {o : Mg.Obs} {s : Mg.Site} : s ∈ hidList Λ o ↔ Mg.Hides s o := by
  simp [hidList, Λ.mem_sites]

theorem nodup_visList (o : Mg.Obs) : (visList o).Nodup := (nodup_leaves t).filter _

theorem nodup_hidList (o : Mg.Obs) : (hidList Λ o).Nodup := Λ.nodup.filter _

/-- **The label of an observer**: a tag byte, then the leaf's path or the site's code. -/
def label : Mg.Obs → List Byte
  | .leaf p => 0 :: p.pathBytes
  | .sink s => 1 :: Λ.code s

/-- The bytes of the final digests of the branches `ss`, `k` bytes each. -/
def serDs (ss : List Mg.Site) (ds : Mg.Site → Digest k) : List Byte :=
  ss.flatMap fun s => List.ofFn (ds s)

/-- Read one digest for each of the branches `ss`, one after the other.

Running time: `|ss|` reads of `k` bytes. This running time is argued here, not proved in Lean. -/
def parseDs : List Mg.Site → List Byte → Option (List (Σ _ : Mg.Site, Digest k) × List Byte)
  | [], u => some ([], u)
  | s :: ss, u => (takeFin k u).bind fun p => (parseDs ss p.2).map fun r => (⟨s, p.1⟩ :: r.1, r.2)

/-- The own items of a content, as bytes. -/
def ownBytes : BContent Mg k Wr X' → List Byte
  | .round _ p _ _ own => ItemCodec.serList (C p.label) own
  | .final _ _ _ _ => []

/-- **The bytes of a chain input** (module docstring). -/
def bytesOf (c : BContent Mg k Wr X') : List Byte :=
  CX.ser c.stmt ++ (label Λ c.obs ++ (CausalEncoding.serCtx C (visList c.obs) c.chains ++
    (serDs (hidList Λ c.obs) c.ds ++ ownBytes C c)))

/-- **Parse the rest of a round input at the candidate leaf `p`**: strip `p`'s label, read the
full chains of the leaves `p` reads in full, the digests of the branches hidden from `p`, then the
rest as `p`'s own items, and accept only a proper prefix.

Running time: a label comparison, one `parseCtx`, one `parseDs`, one `ItemCodec.parseList`.
This running time is argued here, not proved in Lean. -/
def tryLeaf (ss : X') (u : List Byte) (p : t.Leaf) : Option (BContent Mg k Wr X') :=
  (strip (label Λ (.leaf p)) u).bind fun u₁ =>
    (CausalEncoding.parseCtx (k := k) C (visList (Mg := Mg) (.leaf p)) u₁).bind fun r =>
      (parseDs (k := k) (hidList Λ (.leaf p)) r.2).bind fun r' =>
        (ItemCodec.parseList (C p.label) r'.2.length 0 r'.2).bind fun own =>
          if own.length < n p.label then
            some (.round ss p (fun q => (r.1.dlookup q).getD []) (fun s => (r'.1.dlookup s).getD 0)
              own)
          else none

/-- **Parse the rest of a final input at the candidate site `s`**: strip `s`'s label, read the
full chains of the leaves its sink reads in full and the digests of the branches hidden from its
sink, and accept only if nothing is left.

Running time: a label comparison, one `parseCtx`, one `parseDs`.
This running time is argued here, not proved in Lean. -/
def trySink (ss : X') (u : List Byte) (s : Mg.Site) : Option (BContent Mg k Wr X') :=
  (strip (label Λ (.sink s)) u).bind fun u₁ =>
    (CausalEncoding.parseCtx (k := k) C (visList (Mg := Mg) (.sink s)) u₁).bind fun r =>
      (parseDs (k := k) (hidList Λ (.sink s)) r.2).bind fun r' =>
        if r'.2 = [] then
          some (.final ss s (fun q => (r.1.dlookup q).getD []) fun s' => (r'.1.dlookup s').getD 0)
        else none

/-- **Decode a chain input**: the decoder of `CX`, then the first leaf in term order at which the
rest parses as a round input, or else the first site at which it parses as a final input.

Running time: one run of `CX.parse`, then at most one `tryLeaf` per leaf and one `trySink` per
site. This running time is argued here, not proved in Lean. -/
def decodeBytes (u : List Byte) : Option (BContent Mg k Wr X') :=
  (CX.parse u).bind fun r =>
    (t.leaves.findSome? (tryLeaf C Λ r.1 r.2)).or (Λ.sites.findSome? (trySink C Λ r.1 r.2))

/-! ### Digests -/

theorem parseDs_serDs (ds : Mg.Site → Digest k) : ∀ (ss : List Mg.Site) (u : List Byte),
    parseDs ss (serDs ss ds ++ u) = some (ss.map fun s => ⟨s, ds s⟩, u)
  | [], u => rfl
  | s :: ss, u => by
    have e : serDs (s :: ss) ds ++ u = List.ofFn (ds s) ++ (serDs ss ds ++ u) := by
      simp [serDs]
    rw [e, parseDs, takeFin_append, Option.bind_some, parseDs_serDs ds ss u]
    rfl

theorem ser_of_parseDs : ∀ (ss : List Mg.Site) {u v : List Byte}
    {ls : List (Σ _ : Mg.Site, Digest k)}, parseDs ss u = some (ls, v) →
      ls.keys = ss ∧ u = ls.flatMap (fun e => List.ofFn e.2) ++ v
  | [], u, v, ls, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
    exact ⟨rfl, rfl⟩
  | s :: ss, u, v, ls, h => by
    rw [parseDs] at h
    obtain ⟨⟨d, w⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ls', w'⟩, hc, he⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    dsimp only at hc ⊢
    obtain ⟨hk, hs⟩ := ser_of_parseDs ss hc
    refine ⟨by rw [List.keys_cons, hk], ?_⟩
    rw [eq_of_takeFin hd, hs]
    simp

/-! ### Well-formed parses -/

variable {C} in
/-- **The chains read by `parseCtx` are full and well formed.** -/
theorem wf_of_parseCtx : ∀ (qs : List t.Leaf) {u v : List Byte}
    {ls : List (Σ q : t.Leaf, List (Item k (Σ i, Wr q.label i)))},
    CausalEncoding.parseCtx C qs u = some (ls, v) →
      ∀ e ∈ ls, chainWF (P e.1.label) e.2 ∧ e.2.length = n e.1.label
  | [], u, v, ls, h, e, he => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.1 h)
    simp at he
  | q :: qs, u, v, ls, h, e, he => by
    rw [CausalEncoding.parseCtx] at h
    obtain ⟨⟨l, w⟩, hn, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ls', w'⟩, hc, hls⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hls
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨fun j hj => ?_, ItemCodec.length_of_parseN _ _ _ hn⟩
      simpa using ItemCodec.fits_of_parseN _ _ _ hn j hj
    · exact wf_of_parseCtx qs hc e he

/-- A lookup in a list whose keys are `qs` succeeds exactly at `qs`, at a member of the list. -/
theorem dlookup_getD_of_keys {α : Type} [DecidableEq α] {β : α → Type} {l : List (Sigma β)}
    {qs : List α} (hk : l.keys = qs) (d : (a : α) → β a) (a : α) :
    (a ∈ qs → ∃ b, ⟨a, b⟩ ∈ l ∧ (l.dlookup a).getD (d a) = b) ∧
      (a ∉ qs → (l.dlookup a).getD (d a) = d a) := by
  constructor
  · intro ha
    rw [← hk] at ha
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (List.dlookup_isSome.2 ha)
    exact ⟨b, List.of_mem_dlookup hb, by rw [hb]; rfl⟩
  · intro ha
    rw [← hk] at ha
    rw [List.dlookup_eq_none.2 ha]
    rfl

/-! ### Unique decodability -/

variable {C CX Λ}

/-- The bytes after the writes before round 0. -/
theorem bytesOf_eq (c : BContent Mg k Wr X') :
    bytesOf C CX Λ c = CX.ser c.stmt ++ (label Λ c.obs ++ (CausalEncoding.serCtx C (visList c.obs)
      c.chains ++ (serDs (hidList Λ c.obs) c.ds ++ ownBytes C c))) := rfl

/-- The chains of well-formed content parse as the full chains of the leaves read in full. -/
theorem parseCtx_view {o : Mg.Obs} {chs : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))}
    {ds : Mg.Site → Digest k} (hv : Content.ViewWF n (fun j => chainWF (P j)) o chs ds)
    (u : List Byte) : CausalEncoding.parseCtx C (visList o) (CausalEncoding.serCtx C (visList o) chs ++ u) =
      some ((visList o).map fun q => ⟨q, chs q⟩, u) :=
  CausalEncoding.parseCtx_serCtx C chs _ (fun q hq =>
    ⟨hv.chains_wf q (mem_visList.1 hq), hv.chains_length q (mem_visList.1 hq)⟩) u

/-- The chains of a view, read back by lookup. -/
theorem view_chains_lookup {o : Mg.Obs} {chs : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))}
    {ds : Mg.Site → Digest k} (hv : Content.ViewWF n (fun j => chainWF (P j)) o chs ds) :
    (fun q => (((visList o).map fun q => (⟨q, chs q⟩ : Σ q : t.Leaf, List (Item k (Σ i, Wr q.label i)))).dlookup q).getD []) = chs := by
  funext q
  rw [List.dlookup_map_mk]
  split_ifs with hq
  · rfl
  · exact (hv.chains_nil q fun h => hq (mem_visList.2 h)).symm

/-- The digests of a view, read back by lookup. -/
theorem view_ds_lookup {o : Mg.Obs} {chs : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))}
    {ds : Mg.Site → Digest k} (hv : Content.ViewWF n (fun j => chainWF (P j)) o chs ds) :
    (fun s => (((hidList Λ o).map fun s => (⟨s, ds s⟩ : Σ _ : Mg.Site, Digest k)).dlookup s).getD 0) =
      ds := by
  funext s
  rw [List.dlookup_map_mk]
  split_ifs with hs
  · rfl
  · exact (hv.ds_zero s fun h => hs ((mem_hidList Λ).2 h)).symm

/-- A round input parses at its own leaf. -/
theorem tryLeaf_self {ss : X'} {p : t.Leaf} {chs : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))}
    {ds : Mg.Site → Digest k} {own : List (Item k (Σ i, Wr p.label i))}
    (h : (Content.round ss p chs ds own : BContent Mg k Wr X').WF n fun j => chainWF (P j)) :
    tryLeaf C Λ ss (label Λ (.leaf p : Mg.Obs) ++ (CausalEncoding.serCtx C (visList (.leaf p : Mg.Obs)) chs ++
      (serDs (hidList Λ (.leaf p : Mg.Obs)) ds ++ ItemCodec.serList (C p.label) own))) p =
      some (.round ss p chs ds own) := by
  cases h with
  | round hv hown hlt =>
    have hparse := ItemCodec.parseList_serList (C p.label) own 0
      (fun j hj => by simpa using hown j hj) _ le_rfl
    simp only [tryLeaf, strip_append, Option.bind_some, parseCtx_view hv, parseDs_serDs, hparse,
      hlt, ↓reduceIte, view_chains_lookup hv, view_ds_lookup hv]

/-- A final input parses at its own site. -/
theorem trySink_self {ss : X'} {s : Mg.Site} {chs : (q : t.Leaf) → List (Item k (Σ i, Wr q.label i))}
    {ds : Mg.Site → Digest k}
    (h : (Content.final ss s chs ds : BContent Mg k Wr X').WF n fun j => chainWF (P j)) :
    trySink C Λ ss (label Λ (.sink s : Mg.Obs) ++ (CausalEncoding.serCtx C (visList (.sink s : Mg.Obs)) chs ++
      (serDs (hidList Λ (.sink s : Mg.Obs)) ds ++ []))) s = some (.final ss s chs ds) := by
  cases h with
  | final hv =>
    simp only [trySink, strip_append, Option.bind_some, parseCtx_view hv, parseDs_serDs,
      ↓reduceIte, view_chains_lookup hv, view_ds_lookup hv]

/-- A label determines its observer. -/
theorem label_append_inj {o o' : Mg.Obs} {u u' : List Byte}
    (h : label Λ o ++ u = label Λ o' ++ u') : o = o' := by
  cases o <;> cases o' <;> simp only [label, List.cons_append, List.cons.injEq] at h
  · exact congrArg _ (Leaf.pathBytes_append_inj h.2).1
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · exact congrArg _ (Λ.code_append_inj h.2).1

theorem tryLeaf_other {ss : X'} {o : Mg.Obs} {u : List Byte} {p' : t.Leaf}
    (hne : o ≠ .leaf p') : tryLeaf (k := k) (n := n) C Λ ss (label Λ o ++ u) p' = none := by
  unfold tryLeaf
  rcases hs : strip (label Λ (.leaf p')) (label Λ o ++ u) with _ | v
  · rfl
  · exact absurd (label_append_inj (eq_of_strip hs)) hne

theorem trySink_other {ss : X'} {o : Mg.Obs} {u : List Byte} {s' : Mg.Site}
    (hne : o ≠ .sink s') : trySink (k := k) (n := n) C Λ ss (label Λ o ++ u) s' = none := by
  unfold trySink
  rcases hs : strip (label Λ (.sink s')) (label Λ o ++ u) with _ | v
  · rfl
  · exact absurd (label_append_inj (eq_of_strip hs)) hne

/-- **Unique decodability**: the decoder reads well-formed content back from its bytes. -/
theorem decodeBytes_bytesOf {c : BContent Mg k Wr X'} (h : c.WF n fun j => chainWF (P j)) :
    decodeBytes C CX Λ (bytesOf C CX Λ c) = some c := by
  rw [decodeBytes, bytesOf_eq, CX.parse_ser, Option.bind_some]
  dsimp only
  cases c with
  | round ss p chs ds own =>
    dsimp only [Content.stmt, Content.obs, Content.chains, Content.ds, ownBytes]
    rw [List.findSome?_eq_of_unique (mem_leaves p) (tryLeaf_self h)
      fun p' _ hne => tryLeaf_other fun e => hne (by cases e; rfl)]
    rfl
  | final ss s chs ds =>
    dsimp only [Content.stmt, Content.obs, Content.chains, Content.ds, ownBytes]
    rw [List.findSome?_eq_none_iff.2 fun p' _ => tryLeaf_other (by simp), Option.none_or,
      List.findSome?_eq_of_unique (Λ.mem_sites s) (trySink_self h)
        fun s' _ hne => trySink_other fun e => hne (by cases e; rfl)]

/-- What a successful `tryLeaf` read. -/
theorem tryLeaf_spec {ss : X'} {u : List Byte} {p : t.Leaf} {c : BContent Mg k Wr X'}
    (h : tryLeaf C Λ ss u p = some c) :
    c.WF n (fun j => chainWF (P j)) ∧ c.stmt = ss ∧ c.obs = .leaf p ∧
      label Λ c.obs ++ (CausalEncoding.serCtx C (visList c.obs) c.chains ++
        (serDs (hidList Λ c.obs) c.ds ++ ownBytes C c)) = u := by
  unfold tryLeaf at h
  obtain ⟨u₁, hu, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ls, w⟩, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨lds, w'⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨own, ho, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hlt
  obtain rfl := Option.some_inj.1 h
  dsimp only at hu hc hd ho ⊢
  obtain ⟨hk, hs⟩ := CausalEncoding.ser_of_parseCtx C _ hc
  obtain ⟨hkd, hsd⟩ := ser_of_parseDs _ hd
  have hwf := wf_of_parseCtx _ hc
  refine ⟨.round ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun s hs => ?_⟩
    (fun j hj => by simpa using ItemCodec.fits_of_parseList _ _ _ ho j hj) hlt, rfl, rfl, ?_⟩
  · obtain ⟨b, hb, hb'⟩ := (dlookup_getD_of_keys hk (fun _ => []) q).1 (mem_visList.2 hq)
    rw [hb']
    exact (hwf _ hb).1
  · obtain ⟨b, hb, hb'⟩ := (dlookup_getD_of_keys hk (fun _ => []) q).1 (mem_visList.2 hq)
    rw [hb']
    exact (hwf _ hb).2
  · exact (dlookup_getD_of_keys hk (fun _ => []) q).2 fun h => hq (mem_visList.1 h)
  · exact (dlookup_getD_of_keys hkd (fun _ => 0) s).2 fun h => hs ((mem_hidList Λ).1 h)
  · have hnd : ls.NodupKeys := by
      unfold List.NodupKeys
      rw [hk]
      exact nodup_visList _
    have hndd : lds.NodupKeys := by
      unfold List.NodupKeys
      rw [hkd]
      exact nodup_hidList Λ _
    have hls := List.eq_map_dlookup (fun _ => ([] : List _)) hnd
    have hlds := List.eq_map_dlookup (fun _ => (0 : Digest k)) hndd
    simp only [Content.obs, Content.chains, Content.ds, ownBytes]
    rw [eq_of_strip hu, hs, hsd, ← ItemCodec.serList_of_parseList _ _ _ ho]
    congr 2
    · conv_rhs => rw [hls, hk]
      simp [CausalEncoding.serCtx, List.flatMap_map]
    · congr 1
      conv_rhs => rw [hlds, hkd]
      simp [serDs, List.flatMap_map]

/-- What a successful `trySink` read. -/
theorem trySink_spec {ss : X'} {u : List Byte} {s : Mg.Site} {c : BContent Mg k Wr X'}
    (h : trySink C Λ ss u s = some c) :
    c.WF n (fun j => chainWF (P j)) ∧ c.stmt = ss ∧ c.obs = .sink s ∧
      label Λ c.obs ++ (CausalEncoding.serCtx C (visList c.obs) c.chains ++
        (serDs (hidList Λ c.obs) c.ds ++ ownBytes C c)) = u := by
  unfold trySink at h
  obtain ⟨u₁, hu, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ls, w⟩, hc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨lds, w'⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h with hnil
  obtain rfl := Option.some_inj.1 h
  dsimp only at hu hc hd hnil ⊢
  subst hnil
  obtain ⟨hk, hs⟩ := CausalEncoding.ser_of_parseCtx C _ hc
  obtain ⟨hkd, hsd⟩ := ser_of_parseDs _ hd
  have hwf := wf_of_parseCtx _ hc
  refine ⟨.final ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun s' hs' => ?_⟩, rfl, rfl, ?_⟩
  · obtain ⟨b, hb, hb'⟩ := (dlookup_getD_of_keys hk (fun _ => []) q).1 (mem_visList.2 hq)
    rw [hb']
    exact (hwf _ hb).1
  · obtain ⟨b, hb, hb'⟩ := (dlookup_getD_of_keys hk (fun _ => []) q).1 (mem_visList.2 hq)
    rw [hb']
    exact (hwf _ hb).2
  · exact (dlookup_getD_of_keys hk (fun _ => []) q).2 fun h => hq (mem_visList.1 h)
  · exact (dlookup_getD_of_keys hkd (fun _ => 0) s').2 fun h => hs' ((mem_hidList Λ).1 h)
  · have hnd : ls.NodupKeys := by
      unfold List.NodupKeys
      rw [hk]
      exact nodup_visList _
    have hndd : lds.NodupKeys := by
      unfold List.NodupKeys
      rw [hkd]
      exact nodup_hidList Λ _
    have hls := List.eq_map_dlookup (fun _ => ([] : List _)) hnd
    have hlds := List.eq_map_dlookup (fun _ => (0 : Digest k)) hndd
    simp only [Content.obs, Content.chains, Content.ds, ownBytes]
    rw [eq_of_strip hu, hs, hsd]
    congr 2
    · conv_rhs => rw [hls, hk]
      simp [CausalEncoding.serCtx, List.flatMap_map]
    · congr 1
      conv_rhs => rw [hlds, hkd]
      simp [serDs, List.flatMap_map]

/-- **What the decoder reads**: well-formed content whose bytes are the input. -/
theorem decodeBytes_spec {u : List Byte} {c : BContent Mg k Wr X'}
    (h : decodeBytes C CX Λ u = some c) :
    c.WF n (fun j => chainWF (P j)) ∧ bytesOf C CX Λ c = u := by
  obtain ⟨⟨ss, v⟩, hx, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  have hu := CX.ser_parse hx
  rcases hl : t.leaves.findSome? (tryLeaf C Λ ss v) with _ | c'
  · rw [hl, Option.none_or] at h
    obtain ⟨s, -, hs⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨hwf, hst, -, hb⟩ := trySink_spec hs
    exact ⟨hwf, by rw [bytesOf_eq, hst, hb, hu]⟩
  · rw [hl, Option.some_or] at h
    obtain rfl := Option.some_inj.1 h
    obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some hl
    obtain ⟨hwf, hst, -, hb⟩ := tryLeaf_spec hp
    exact ⟨hwf, by rw [bytesOf_eq, hst, hb, hu]⟩

/-! ### Lengths -/

variable (C CX Λ)

/-- **The length of a chain input of well-formed content**: the writes before round 0, the
label, at most `max B (9 + k)` bytes for each item and `k` bytes for each final digest. -/
theorem length_bytesOf_le {B : ℕ} (hB : ∀ j i, (C j i).B ≤ B) {c : BContent Mg k Wr X'}
    (h : c.WF n fun j => chainWF (P j)) :
    (bytesOf C CX Λ c).length ≤ (CX.ser c.stmt).length + (label Λ c.obs).length +
      (∑ q : t.Leaf, n q.label) * max B (9 + k) + Mg.nJ * k := by
  have hds : (serDs (hidList Λ c.obs) c.ds).length = (hidList Λ c.obs).length * k := by
    unfold serDs
    induction hidList Λ c.obs with
    | nil => simp
    | cons s l ih => simp [List.flatMap_cons, ih, Nat.add_mul, Nat.add_comm]
  have hhid : (hidList Λ c.obs).length ≤ Mg.nJ := by
    rw [← List.toFinset_card_of_nodup (nodup_hidList Λ _)]
    refine le_trans (Finset.card_le_card fun s hs => ?_) (Merges.card_hiders_le c.obs)
    exact Merges.mem_hiders.2 ((mem_hidList Λ).1 (List.mem_toFinset.1 hs))
  have hctx := CausalEncoding.length_serCtx_le C hB (visList c.obs) c.chains
  have hvis : ((visList c.obs).map fun q => (c.chains q).length).sum ≤ ∑ q, (c.chains q).length := by
    rw [← List.sum_toFinset _ (nodup_visList _)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hown : (ownBytes C c).length ≤ c.ownLength * max B (9 + k) := by
    cases c with
    | round _ p _ _ own => exact ItemCodec.length_serList_le (C p.label) (hB _) own
    | final => simp [ownBytes]
  have hsize := Nat.mul_le_mul_right (max B (9 + k)) (Content.size_le h)
  have hk := Nat.mul_le_mul_right k hhid
  have h4 := Nat.mul_le_mul_right (max B (9 + k)) hvis
  simp only [bytesOf, List.length_append, Content.size, Nat.add_mul] at hctx hsize ⊢
  omega

variable (dg : (j : ι) → (Σ i, Wr j i) → Finset (Digest k)) {nd : ℕ} (B : ℕ)

/-- **The byte encoding of chain inputs with merges** (module docstring), with `decode` the
algorithm `decodeBytes`; `digestsOf b` is the item digests of the parsed content, so an input
carries at most `nd` digests per item and `(∑ q, n q.label) · nd` in all.
- `hdg`, `hnd`: a write carries at most `nd ≥ 1` roots;
- `hB`: every write has at most `B` bytes;
- `hL`: every chain input fits in `L` bytes. -/
def bytes (hdg : ∀ j w, (dg j w).card ≤ nd) (hnd : 1 ≤ nd) (hB : ∀ j i, (C j i).B ≤ B)
    (hL : ∀ (x : X') (o : Mg.Obs), (CX.ser x).length + (label Λ o).length +
      (∑ q : t.Leaf, n q.label) * max B (9 + k) + Mg.nJ * k ≤ L) :
    MergeEncoding k L Mg n X' (fun j => Σ i, Wr j i) dg (fun j => chainWF (P j)) where
  encode c := Bytes.ofList (bytesOf C CX Λ c)
  decode b := decodeBytes C CX Λ (Bytes.toList b)
  digestsOf b := match decodeBytes (n := n) C CX Λ (Bytes.toList (L := L) b) with
    | some c => if c.size ≤ ∑ q : t.Leaf, n q.label then c.itemDigests dg else ∅
    | none => ∅
  digestsPerInput := (∑ q : t.Leaf, n q.label) * nd
  decode_encode c h := by
    simp only [Bytes.toList_ofList ((length_bytesOf_le C CX Λ hB h).trans (hL _ _)),
      decodeBytes_bytesOf h]
  encode_decode b c h := by
    rw [(decodeBytes_spec h).2, Bytes.ofList_toList]
  wf_of_decode b c h := (decodeBytes_spec h).1
  digest_mem c h := by
    simp [Bytes.toList_ofList ((length_bytesOf_le C CX Λ hB h).trans (hL _ _)),
      decodeBytes_bytesOf h, Content.size_le h]
  card_digestsOf_le b := by
    split
    · split_ifs with hs
      · exact (Content.card_itemDigests_le hdg hnd _).trans (Nat.mul_le_mul_right _ hs)
      · simp
    · simp

end MergeBytes

end GordieHowe.SPBCS
