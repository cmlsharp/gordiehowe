-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merges
public import GordieHowe.SPBCS.FullPast.Encoding

@[expose] public section

/-!
# Chain inputs of the spBCS compiler

The chain inputs of the spBCS compiler (paper `prot:generalized-bcs`) on a series–parallel
term `t` with merges `Mg` (`GordieHowe/SPBCS/Merges.lean`). Every chain input belongs to an observer
(`Merges.Obs`) and holds the salted statement, the observer's *view* of its past, and, for a leaf,
its own items:

* the view of an observer `o`: the full chain of every leaf that `o` reads in full
  (`Obs.Visible`), and the final digest of every branch hidden from `o` (`Merges.Hides`);
* `round ss p chains ds own`: the chain input of a challenge round of leaf `p`, with `p`'s items
  `own` before the round;
* `final ss s chains ds`: the final input of the branch of site `s`, the input of its sink. Its
  view holds the full chain of every leaf of the branch, so its digest is the branch's final
  digest.

`Content.WF` is well-formed content (the view's chains full and well formed where read, empty
elsewhere; the digests `0` off the hidden branches; the own items a well-formed proper prefix).
`MergeEncoding` is the laws an encoding of contents must satisfy, those of `CausalEncoding`: a
decoder that inverts it on well-formed content, whose decoded strings are encodings and parse
well-formed content, and the digests of an input containing those of its items.

Without merges (`Merges.none`) every observer is a leaf reading its whole causal past, and the
content is the content of the compiler over the term (`CausalChain`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {k L : ℕ} {t : SPTerm ι} {Mg : Merges t}

/-! ### Views -/

/-- **The chains an observer reads**: the chains `chs` at the leaves it reads in full, empty
elsewhere. -/
def Merges.Obs.viewChains {W : ι → Type} (o : Mg.Obs) (chs : (q : t.Leaf) → List (Item k (W q.label)))
    (q : t.Leaf) : List (Item k (W q.label)) :=
  if o.Visible q then chs q else []

/-- **The final digests an observer reads**: the digests `fs` at the branches hidden from it, `0`
elsewhere. -/
def Merges.Obs.viewDs (o : Mg.Obs) (fs : Mg.Site → Digest k) (s : Mg.Site) : Digest k :=
  if Mg.Hides s o then fs s else 0

namespace Merges.Obs

variable {W : ι → Type} (o : Mg.Obs)

theorem viewChains_of_visible (chs : (q : t.Leaf) → List (Item k (W q.label))) {q : t.Leaf}
    (hq : o.Visible q) : o.viewChains chs q = chs q :=
  ite_eq_left hq

theorem viewChains_of_not_visible (chs : (q : t.Leaf) → List (Item k (W q.label))) {q : t.Leaf}
    (hq : ¬ o.Visible q) : o.viewChains chs q = [] :=
  ite_eq_right hq

theorem viewDs_of_hides (fs : Mg.Site → Digest k) {s : Mg.Site} (hs : Mg.Hides s o) :
    o.viewDs fs s = fs s :=
  ite_eq_left hs

theorem viewDs_of_not_hides (fs : Mg.Site → Digest k) {s : Mg.Site} (hs : ¬ Mg.Hides s o) :
    o.viewDs fs s = 0 :=
  ite_eq_right hs

/-- **A view reads the chains only at the leaves read in full.** -/
theorem viewChains_congr {chs chs' : (q : t.Leaf) → List (Item k (W q.label))}
    (h : ∀ q, o.Visible q → chs q = chs' q) : o.viewChains chs = o.viewChains chs' := funext fun q => by
  unfold viewChains
  split_ifs with hq
  · exact h q hq
  · rfl

/-- **A view reads the final digests only at the hidden branches.** -/
theorem viewDs_congr {fs fs' : Mg.Site → Digest k} (h : ∀ s, Mg.Hides s o → fs s = fs' s) :
    o.viewDs fs = o.viewDs fs' := funext fun s => by
  unfold viewDs
  split_ifs with hs
  · exact h s hs
  · rfl

end Merges.Obs

/-! ### Content -/

variable (Mg) in
/-- **The content of a chain input** (module docstring), with the observer it belongs to; every
input holds the salted statement `ss`.
- `round ss p chains ds own`: a challenge round of leaf `p` after its items `own`;
- `final ss s chains ds`: the final input of the branch of site `s`. -/
inductive Content (k : ℕ) (W : ι → Type) (X' : Type) where
  /-- The chain input of a challenge round of a leaf. -/
  | round (ss : X') (p : t.Leaf) (chains : (q : t.Leaf) → List (Item k (W q.label)))
      (ds : Mg.Site → Digest k) (own : List (Item k (W p.label)))
  /-- The final input of a branch. -/
  | final (ss : X') (s : Mg.Site) (chains : (q : t.Leaf) → List (Item k (W q.label)))
      (ds : Mg.Site → Digest k)

namespace Content

variable {W : ι → Type} {X' : Type}

/-- The observer of a content. -/
def obs : Content Mg k W X' → Mg.Obs
  | round _ p _ _ _ => .leaf p
  | final _ s _ _ => .sink s

/-- The salted statement of a content. -/
def stmt : Content Mg k W X' → X'
  | round ss _ _ _ _ => ss
  | final ss _ _ _ => ss

/-- The chains of a content. -/
def chains : (c : Content Mg k W X') → (q : t.Leaf) → List (Item k (W q.label))
  | round _ _ chs _ _ => chs
  | final _ _ chs _ => chs

/-- The final digests of a content. -/
def ds : Content Mg k W X' → Mg.Site → Digest k
  | round _ _ _ ds _ => ds
  | final _ _ _ ds => ds

@[simp] theorem obs_round (ss : X') (p : t.Leaf) chs ds (own : List (Item k (W p.label))) :
    (round (Mg := Mg) ss p chs ds own).obs = .leaf p := rfl
@[simp] theorem obs_final (ss : X') (s : Mg.Site) chs ds :
    (final (k := k) (W := W) ss s chs ds).obs = .sink s := rfl
@[simp] theorem stmt_round (ss : X') (p : t.Leaf) chs ds (own : List (Item k (W p.label))) :
    (round (Mg := Mg) ss p chs ds own).stmt = ss := rfl
@[simp] theorem stmt_final (ss : X') (s : Mg.Site) chs ds :
    (final (k := k) (W := W) ss s chs ds).stmt = ss := rfl

variable (n : ι → ℕ) (WFi : (j : ι) → List (Item k (W j)) → Prop)

/-- **A well-formed view of the observer `o`**: full well-formed chains at the leaves `o` reads in
full, empty chains elsewhere, and digest `0` at the branches not hidden from `o`. -/
structure ViewWF (o : Mg.Obs) (chs : (q : t.Leaf) → List (Item k (W q.label)))
    (ds : Mg.Site → Digest k) : Prop where
  /-- The chains read are well formed. -/
  chains_wf : ∀ q, o.Visible q → WFi q.label (chs q)
  /-- The chains read are full. -/
  chains_length : ∀ q, o.Visible q → (chs q).length = n q.label
  /-- The other chains are empty. -/
  chains_nil : ∀ q, ¬ o.Visible q → chs q = []
  /-- The digests off the hidden branches are `0`. -/
  ds_zero : ∀ s, ¬ Mg.Hides s o → ds s = 0

/-- **Well-formed content**: a well-formed view, and for a round its own items a well-formed
proper prefix. -/
inductive WF : Content Mg k W X' → Prop where
  /-- A well-formed round input. -/
  | round {ss : X'} {p : t.Leaf} {chs : (q : t.Leaf) → List (Item k (W q.label))}
      {ds : Mg.Site → Digest k} {own : List (Item k (W p.label))} :
      ViewWF n WFi (.leaf p) chs ds → WFi p.label own → own.length < n p.label →
      WF (round ss p chs ds own)
  /-- A well-formed final input. -/
  | final {ss : X'} {s : Mg.Site} {chs : (q : t.Leaf) → List (Item k (W q.label))}
      {ds : Mg.Site → Digest k} : ViewWF n WFi (.sink s) chs ds → WF (final ss s chs ds)

variable {n WFi}

/-- **The view of full chains is well formed.** -/
theorem viewWF_view (o : Mg.Obs) {chs : (q : t.Leaf) → List (Item k (W q.label))}
    (hwf : ∀ q, o.Visible q → WFi q.label (chs q))
    (hlen : ∀ q, o.Visible q → (chs q).length = n q.label) (fs : Mg.Site → Digest k) :
    ViewWF n WFi o (o.viewChains chs) (o.viewDs fs) where
  chains_wf q hq := by rw [o.viewChains_of_visible chs hq]; exact hwf q hq
  chains_length q hq := by rw [o.viewChains_of_visible chs hq]; exact hlen q hq
  chains_nil q hq := o.viewChains_of_not_visible chs hq
  ds_zero s hs := o.viewDs_of_not_hides fs hs

/-- The view of well-formed content. -/
theorem WF.viewWF {c : Content Mg k W X'} (h : c.WF n WFi) : ViewWF n WFi c.obs c.chains c.ds := by
  cases h with
  | round hv _ _ => exact hv
  | final hv => exact hv

/-- **A well-formed content's chains are its observer's view of them.** -/
theorem ViewWF.viewChains_eq {o : Mg.Obs} {chs : (q : t.Leaf) → List (Item k (W q.label))}
    {ds : Mg.Site → Digest k} (h : ViewWF n WFi o chs ds) : o.viewChains chs = chs := funext fun q => by
  by_cases hq : o.Visible q
  · exact o.viewChains_of_visible chs hq
  · rw [o.viewChains_of_not_visible chs hq, h.chains_nil q hq]

/-- **A well-formed content's digests are its observer's view of them.** -/
theorem ViewWF.viewDs_eq {o : Mg.Obs} {chs : (q : t.Leaf) → List (Item k (W q.label))}
    {ds : Mg.Site → Digest k} (h : ViewWF n WFi o chs ds) : o.viewDs ds = ds := funext fun s => by
  by_cases hs : Mg.Hides s o
  · exact o.viewDs_of_hides ds hs
  · rw [o.viewDs_of_not_hides ds hs, h.ds_zero s hs]

/-- **The final digests a content holds**: those of the branches hidden from its observer. -/
def finalDs (c : Content Mg k W X') : Finset (Digest k) := (Merges.hiders c.obs).image c.ds

/-- **A content holds at most `nJ` final digests.** -/
theorem card_finalDs_le (c : Content Mg k W X') : c.finalDs.card ≤ Mg.nJ :=
  Finset.card_image_le.trans (Merges.card_hiders_le _)

/-- **The digests of the items** a content holds: those of its chains and, for a round, of its
own items. -/
def itemDigests (dg : (j : ι) → W j → Finset (Digest k)) : Content Mg k W X' → Finset (Digest k)
  | round _ p chs _ own =>
    (Finset.univ.biUnion fun q => chainDigests (dg q.label) (chs q)) ∪ chainDigests (dg p.label) own
  | final _ _ chs _ => Finset.univ.biUnion fun q => chainDigests (dg q.label) (chs q)

/-- The number of own items of a content (`0` for a final input). -/
def ownLength : Content Mg k W X' → ℕ
  | round _ _ _ _ own => own.length
  | final _ _ _ _ => 0

/-- **The number of items** of a content: those of its chains and its own items. -/
def size (c : Content Mg k W X') : ℕ := (∑ q, (c.chains q).length) + c.ownLength

/-- Content of `size` items carrying at most `nd ≥ 1` digests each carries at most `size · nd`
item digests. -/
theorem card_itemDigests_le {dg : (j : ι) → W j → Finset (Digest k)} {nd : ℕ}
    (hdg : ∀ j w, (dg j w).card ≤ nd) (hnd : 1 ≤ nd) (c : Content Mg k W X') :
    (c.itemDigests dg).card ≤ c.size * nd := by
  have hctx : ∀ chs : (q : t.Leaf) → List (Item k (W q.label)),
      (Finset.univ.biUnion fun q => chainDigests (dg q.label) (chs q)).card ≤
        (∑ q, (chs q).length) * nd := fun chs => by
    rw [Finset.sum_mul]
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun q _ =>
      card_chainDigests_le (hdg _) hnd _)
  cases c with
  | round _ p chs _ own =>
    refine (Finset.card_union_le _ _).trans ?_
    simp only [size, chains, ownLength, Nat.add_mul]
    exact Nat.add_le_add (hctx chs) (card_chainDigests_le (hdg _) hnd _)
  | final _ _ chs _ =>
    simpa [itemDigests, size, chains, ownLength] using hctx chs

/-- **Well-formed content has at most as many items as all components have rounds.** -/
theorem size_le {c : Content Mg k W X'} (h : c.WF n WFi) : c.size ≤ ∑ q : t.Leaf, n q.label := by
  cases h with
  | @round ss p chs ds own hv _ hlt =>
    have hp : chs p = [] := hv.chains_nil p fun hv' => Leaf.not_before_self p hv'.1
    have hle : ∀ q, (chs q).length + (if q = p then own.length else 0) ≤ n q.label := fun q => by
      by_cases hq : q = p
      · subst hq
        simpa [hp] using hlt.le
      · rw [ite_eq_right hq, add_zero]
        by_cases hvq : (Merges.Obs.leaf p : Mg.Obs).Visible q
        · exact (hv.chains_length q hvq).le
        · rw [hv.chains_nil q hvq]
          exact Nat.zero_le _
    calc size (round ss p chs ds own)
        = ∑ q, ((chs q).length + if q = p then own.length else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ p, ite_eq_left (Finset.mem_univ p)]
          rfl
      _ ≤ _ := Finset.sum_le_sum fun q _ => hle q
  | @final ss s chs ds hv =>
    show (∑ q, (chs q).length) + 0 ≤ _
    rw [add_zero]
    refine Finset.sum_le_sum fun q _ => ?_
    by_cases hvq : (Merges.Obs.sink s : Mg.Obs).Visible q
    · exact (hv.chains_length q hvq).le
    · rw [hv.chains_nil q hvq]
      exact Nat.zero_le _

end Content

/-! ### Encodings -/

/-- **A chain-input encoding for the spBCS compiler** (module docstring), the laws of
`CausalEncoding` for contents:
- `decode_encode`: on well-formed content the decoder inverts the encoding;
- `encode_decode`: a decoded string is the encoding of its parse;
- `wf_of_decode`: the decoder parses only well-formed content;
- `digest_mem`: the digests of an input contain those of the items of well-formed content;
- `card_digestsOf_le`: an input contains at most `digestsPerInput` digests. -/
structure MergeEncoding (k L : ℕ) (Mg : Merges t) (n : ι → ℕ) (X' : Type) (W : ι → Type)
    (dg : (j : ι) → W j → Finset (Digest k)) (WFi : (j : ι) → List (Item k (W j)) → Prop) where
  /-- The input bytes. -/
  encode : Content Mg k W X' → Bytes L
  /-- The parse of input bytes. -/
  decode : Bytes L → Option (Content Mg k W X')
  /-- The digests of input bytes. -/
  digestsOf : Bytes L → Finset (Digest k)
  /-- The bound on the digests of one input. -/
  digestsPerInput : ℕ
  decode_encode : ∀ c, c.WF n WFi → decode (encode c) = some c
  encode_decode : ∀ b c, decode b = some c → encode c = b
  wf_of_decode : ∀ b c, decode b = some c → c.WF n WFi
  digest_mem : ∀ c, c.WF n WFi → c.itemDigests dg ⊆ digestsOf (encode c)
  card_digestsOf_le : ∀ b, (digestsOf b).card ≤ digestsPerInput

namespace MergeEncoding

variable {n : ι → ℕ} {X' : Type} {W : ι → Type} {dg : (j : ι) → W j → Finset (Digest k)}
  {WFi : (j : ι) → List (Item k (W j)) → Prop}

/-- **An input determines its content.** -/
theorem encode_injective (E : MergeEncoding k L Mg n X' W dg WFi) {c c' : Content Mg k W X'}
    (hw : c.WF n WFi) (hw' : c'.WF n WFi) (h : E.encode c = E.encode c') : c = c' :=
  Option.some_inj.1 ((E.decode_encode c hw).symm.trans (h ▸ E.decode_encode c' hw'))

end MergeEncoding

end GordieHowe.SPBCS
