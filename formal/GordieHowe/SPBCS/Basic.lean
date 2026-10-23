-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Encoding
public import GordieHowe.SPBCS.FullPast.Model

@[expose] public section

/-!
# The spBCS compiler: the compiler on a series–parallel term with merges

The spBCS compiler (paper `prot:generalized-bcs`) on a series–parallel term `t` with merges
`Mg` (`GordieHowe/SPBCS/Merges.lean`): the leaves have the chains, writes, Merkle trees, proofs and
query phases of the compiler data over the term (`GordieHowe.SPBCS.Base`), every stream point carries the
Fiat–Shamir salt, and every chain input holds its observer's view (`GordieHowe/SPBCS/Encoding.lean`):
the full chains of the leaves it reads in full and the final digests of the branches hidden from
it.

* `GordieHowe.SPBCS Mg P X k kN kS L e`: a `GordieHowe.SPBCS.Base` of the term with Fiat–Shamir salts of `kS` bytes,
  and the encoding `senc` of the chain inputs with merges. The base model's own encoding `enc`
  (the full causal past) is not used by the compiled argument; a database extractor re-encodes
  the causal pasts it reads with it, and a knowledge bound counts its digests as those of the
  content (`enc_digests_subset`).
* `roundContent`, `finalContent`: the content of a challenge round's chain input and of a
  branch's final input, from chains `chs` of all leaves and final digests `fs` of all branches.
* `finalStep`, `finalsWith chs`: the final digest of a branch is the digest of its final input,
  which holds the final digests of the branches hidden from its sink. These are fewer
  (`Merges.hiders_sink_ssubset`), so iterating `finalStep` as many times as there are branches
  gives the solution `finalsWith chs` of `fs s = finalStep chs fs s` (`finalsWith_eq`), the only
  one (`eq_finalsWith`).
* `chains`: the chains of all leaves (the causal fixpoint `SPTerm.solve`): a leaf's chain is its
  component's chain for the keys of its chain inputs, from the chains of the leaves before it and
  the final digests computed from them; `chains_eq` states it at the final chains and digests
  (`finals`).
* `chal`, `chV`: the challenges; `Accepts`: the compiled verifier.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

/-- **The compiler data of a term with merges** (module docstring): the data of the compiler over
the term, with salts of `kS` bytes, and the encoding of the chain inputs with merges. -/
structure _root_.GordieHowe.SPBCS (Mg : Merges t) {n : ι → ℕ} (P : (j : ι) → ProtocolSpec (n j))
    [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] (X : Type)
    (k kN kS L e : ℕ) extends Base P t X k kN kS L e where
  /-- The encoding of the chain inputs with merges. -/
  senc : MergeEncoding k L Mg n (SaltedStatement kS X) (fun j => (comp j).W)
    (fun j => (comp j).roots) (fun j => chainWF (P j))
  /-- The base model's encoding carries only the digests of its content. -/
  enc_digests_subset : ∀ ss ch, ch.WF n (fun j => chainWF (P j)) →
    enc.digestsOf (enc.encode ss ch) ⊆ ch.digests fun j => (comp j).roots

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-- The compiler data of `M` as a full-past compiler (proof-internal): field notation on it reaches
the declarations of the namespace `FullPast`. -/
abbrev toFullPast : FullPast P t X k kN kS L e := M.toBase

/-- The content of a chain input of `M`. -/
abbrev MContent : Type := Content Mg k (fun j => (M.comp j).W) (SaltedStatement kS X)

/-- Chains of all leaves. -/
abbrev Chains : Type := (q : t.Leaf) → M.Items q

variable {M} in
/-- **The content of the chain input of leaf `p` at its own items `l`**: its view of the chains
`chs` and the final digests `fs`. -/
def roundContent (ss : SaltedStatement kS X) (chs : M.Chains) (fs : Mg.Site → Digest k)
    (p : t.Leaf) (l : M.Items p) : M.MContent :=
  .round ss p ((Merges.Obs.leaf p : Mg.Obs).viewChains (W := fun j => (M.comp j).W) chs)
    ((Merges.Obs.leaf p : Mg.Obs).viewDs fs) l

variable {M} in
/-- **The content of the final input of the branch of site `s`**: its sink's view of the chains
`chs` and the final digests `fs`. -/
def finalContent (ss : SaltedStatement kS X) (chs : M.Chains) (fs : Mg.Site → Digest k)
    (s : Mg.Site) : M.MContent :=
  .final ss s ((Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) chs)
    ((Merges.Obs.sink s : Mg.Obs).viewDs fs)

variable (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X)

/-- **The key of a chain input of leaf `p`**: the digest of `h` at its encoding. -/
def key (chs : M.Chains) (fs : Mg.Site → Digest k) (p : t.Leaf) (l : M.Items p) : Digest k :=
  (h (.transcript (M.senc.encode (roundContent ss chs fs p l)))).digest

/-- **The final digest of a branch** at the chains `chs` and the final digests `fs`: the digest
of `h` at its final input. -/
def finalStep (chs : M.Chains) (fs : Mg.Site → Digest k) (s : Mg.Site) : Digest k :=
  (h (.transcript (M.senc.encode (finalContent ss chs fs s)))).digest

/-- **The final digests at the chains `chs`** (module docstring): `finalStep` iterated once per
branch from `0`. -/
def finalsWith (chs : M.Chains) : Mg.Site → Digest k :=
  (M.finalStep h ss chs)^[Fintype.card Mg.Site] 0

/-! ### What a key and a final digest read -/

section Reads

variable {M h ss}

/-- **A key reads the chains only at the leaves its leaf reads in full and the final digests only
at the branches hidden from its leaf.** -/
theorem key_congr {chs chs' : M.Chains} {fs fs' : Mg.Site → Digest k} {p : t.Leaf}
    (hc : ∀ q, (Merges.Obs.leaf p : Mg.Obs).Visible q → chs q = chs' q)
    (hf : ∀ s, Mg.Hides s (.leaf p) → fs s = fs' s) : M.key h ss chs fs p = M.key h ss chs' fs' p :=
  funext fun l => by
    unfold key roundContent
    rw [Merges.Obs.viewChains_congr _ hc, Merges.Obs.viewDs_congr _ hf]

/-- **A final digest reads the chains only at the leaves its sink reads in full and the final
digests only at the branches hidden from its sink.** -/
theorem finalStep_congr {chs chs' : M.Chains} {fs fs' : Mg.Site → Digest k} {s : Mg.Site}
    (hc : ∀ q, (Merges.Obs.sink s : Mg.Obs).Visible q → chs q = chs' q)
    (hf : ∀ s', Mg.Hides s' (.sink s) → fs s' = fs' s') :
    M.finalStep h ss chs fs s = M.finalStep h ss chs' fs' s := by
  unfold finalStep finalContent
  rw [Merges.Obs.viewChains_congr _ hc, Merges.Obs.viewDs_congr _ hf]

/-- The number of branches hidden from a sink is below the number of branches. -/
theorem card_hiders_sink_lt (s : Mg.Site) :
    (Merges.hiders (M := Mg) (.sink s)).card < Fintype.card Mg.Site :=
  Finset.card_lt_univ_of_notMem (Merges.mem_hiders.not.2 (Merges.not_hides_sink_self s))

/-- **The iterates of `finalStep` agree at a branch after more steps than the branches hidden
from its sink.** -/
theorem iterate_finalStep_eq (chs : M.Chains) : ∀ (c : ℕ) (s : Mg.Site),
    (Merges.hiders (M := Mg) (.sink s)).card = c → ∀ m m', c < m → c < m' →
    (M.finalStep h ss chs)^[m] 0 s = (M.finalStep h ss chs)^[m'] 0 s := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro s hc m m' hm hm'
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', m' = a' + 1 := ⟨m' - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine finalStep_congr (fun _ _ => rfl) fun s' hs' => ?_
    have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
    rw [hc] at hlt
    exact ih _ hlt s' rfl a a' (by omega) (by omega)

/-- **The final digests solve their equation**: each is the digest of its final input at the
final digests. -/
theorem finalsWith_eq (chs : M.Chains) (s : Mg.Site) :
    M.finalsWith h ss chs s = M.finalStep h ss chs (M.finalsWith h ss chs) s := by
  unfold finalsWith
  rw [← Function.iterate_succ_apply' (M.finalStep h ss chs)]
  exact iterate_finalStep_eq chs _ s rfl _ _ (card_hiders_sink_lt s) (by
    have := card_hiders_sink_lt s
    omega)

/-- **The final digests are the only solution of their equation.** -/
theorem eq_finalsWith {chs : M.Chains} {fs : Mg.Site → Digest k}
    (hfs : ∀ s, fs s = M.finalStep h ss chs fs s) : fs = M.finalsWith h ss chs := by
  funext s
  induction hc : (Merges.hiders (M := Mg) (.sink s)).card using Nat.strong_induction_on
    generalizing s with
  | _ c ih =>
    rw [hfs s, finalsWith_eq chs s]
    refine finalStep_congr (fun _ _ => rfl) fun s' hs' => ?_
    have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
    rw [hc] at hlt
    exact ih _ hlt s' rfl

/-- **A final digest reads the chains only in the past of its sink.** -/
theorem finalsWith_congr {chs chs' : M.Chains} {s : Mg.Site}
    (hc : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q → chs q = chs' q) :
    M.finalsWith h ss chs s = M.finalsWith h ss chs' s := by
  induction hcard : (Merges.hiders (M := Mg) (.sink s)).card using Nat.strong_induction_on
    generalizing s with
  | _ c ih =>
    rw [finalsWith_eq chs s, finalsWith_eq chs' s]
    refine finalStep_congr (fun q hq => hc q hq.1) fun s' hs' => ?_
    have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
    rw [hcard] at hlt
    exact ih _ hlt (fun q hq => hc q (Merges.sees_of_sees_sink hs' hq)) rfl

/-- **The final digests of the branches hidden from a leaf read only the chains before it.** -/
theorem finalsWith_congr_of_hides {chs chs' : M.Chains} {p : t.Leaf}
    (hc : ∀ q, q.Before p → chs q = chs' q) {s : Mg.Site} (hs : Mg.Hides s (.leaf p)) :
    M.finalsWith h ss chs s = M.finalsWith h ss chs' s :=
  finalsWith_congr fun q hq => hc q (Merges.sees_of_sees_sink hs hq)

end Reads

/-! ### The chains of a proof -/

/-- **A leaf's chain from the chains `chs` of the leaves before it**: its component's chain for the
keys of its chain inputs at `chs` and the final digests computed from `chs`. -/
def leafChain (wr : M.Writes) (p : t.Leaf) (chs : M.Chains) : M.Items p :=
  (M.comp p.label).chainWith (wr p) (M.key h ss chs (M.finalsWith h ss chs) p) ss.salt h
    (n p.label) le_rfl

/-- **The chains of all leaves** (the causal fixpoint, module docstring). -/
def chains (wr : M.Writes) : M.Chains :=
  SPTerm.solve fun p ctx => M.leafChain h ss wr p (M.chainsOf ctx)

/-- **The final digests of a proof**: those at its chains. -/
def finals (wr : M.Writes) : Mg.Site → Digest k := M.finalsWith h ss (M.chains h ss wr)

section Chains

variable {M h ss}

/-- **A leaf's chain reads only the chains before it.** -/
theorem leafChain_congr (wr : M.Writes) {p : t.Leaf} {chs chs' : M.Chains}
    (hc : ∀ q, q.Before p → chs q = chs' q) :
    M.leafChain h ss wr p chs = M.leafChain h ss wr p chs' := by
  unfold leafChain
  rw [key_congr (fun q hq => hc q hq.1) fun s hs => finalsWith_congr_of_hides hc hs]

/-- **The defining equation of the chains**: a leaf's chain is its component's chain for the keys
at the chains and final digests of the proof. -/
theorem chains_eq (wr : M.Writes) (p : t.Leaf) :
    M.chains h ss wr p = M.leafChain h ss wr p (M.chains h ss wr) := by
  rw [chains, SPTerm.solve_eq]
  refine leafChain_congr wr fun q hq => ?_
  rw [Base.chainsOf_of_before _ _ hq]

theorem chains_eq_chainWith (wr : M.Writes) (p : t.Leaf) :
    M.chains h ss wr p = (M.comp p.label).chainWith (wr p)
      (M.key h ss (M.chains h ss wr) (M.finals h ss wr) p) ss.salt h (n p.label) le_rfl :=
  chains_eq wr p

/-- **The final digests of a proof solve their equation.** -/
theorem finals_eq (wr : M.Writes) (s : Mg.Site) :
    M.finals h ss wr s = M.finalStep h ss (M.chains h ss wr) (M.finals h ss wr) s :=
  finalsWith_eq _ s

theorem length_chains (wr : M.Writes) (p : t.Leaf) : (M.chains h ss wr p).length = n p.label := by
  rw [chains_eq_chainWith]
  exact ComponentModel.length_chainWith _ _ _ _ _ _ _

theorem chainWF_chains (wr : M.Writes) (p : t.Leaf) : chainWF (P p.label) (M.chains h ss wr p) := by
  rw [chains_eq_chainWith]
  exact ComponentModel.chainWF_chainWith _ _ _ _ _ _ _

/-- **The item of a prover round of a leaf's chain is the leaf's write.** -/
theorem chains_getElem?_message (wr : M.Writes) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    (M.chains h ss wr p)[i.1.1]? = some (.write ⟨i, wr p i⟩) := by
  rw [chains_eq_chainWith, ComponentModel.chainWith_getElem? _ _ _ _ _ _ _ i.1 i.1.2]
  unfold ComponentModel.itemWith
  simp only [i.2, ↓reduceDIte]
  rfl

/-- **A leaf's chain reads only the writes of the leaf and of the leaves before it.** -/
theorem chains_congr {wr wr' : M.Writes} (p : t.Leaf)
    (hw : ∀ q, q.Before p ∨ q = p → wr q = wr' q) : M.chains h ss wr p = M.chains h ss wr' p := by
  induction p using (wellFounded_before t).induction with
  | _ p ih =>
    rw [chains_eq, chains_eq, leafChain_congr wr (chs' := M.chains h ss wr') fun q hq =>
      ih q hq fun r hr => hw r (Or.inl (hr.elim (·.trans hq) (· ▸ hq)))]
    unfold leafChain
    rw [hw p (Or.inr rfl)]

/-- **The final digest of a branch reads only the writes in the past of its sink.** -/
theorem finals_congr {wr wr' : M.Writes} {s : Mg.Site}
    (hw : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q → wr q = wr' q) :
    M.finals h ss wr s = M.finals h ss wr' s := by
  refine finalsWith_congr fun q hq => chains_congr q fun r hr => hw r ?_
  rcases hr with hr | rfl
  · exact Merges.sees_sink_of_before hq hr
  · exact hq

end Chains

/-! ### Challenges and the verifier -/

/-- **The challenge `c`**, sampled from the stream at the key of its chain input and the
Fiat–Shamir salt, or `none` when the sampler rejects. -/
def chal (wr : M.Writes) (c : ChIdx P t) : Option c.Challenge :=
  (M.comp c.leaf.label).chalWith (wr c.leaf)
    (M.key h ss (M.chains h ss wr) (M.finals h ss wr) c.leaf) ss.salt h c.idx

/-- The challenges, with the sampler's default value where it rejects (the verifier rejects
then). -/
def chV (wr : M.Writes) : Chs P t := fun c =>
  (M.chal h ss wr c).getD ((M.comp c.leaf.label).sampler c.idx).default

/-- **The compiled spBCS verifier `V^h(x, π)` accepts**: recompute the chains and the final
digests from `h`, each challenge from the stream at its key and the Fiat–Shamir salt; the samplers
accept every stream (`sampled`); there is one opened leaf per queried position (`leaves_length`);
every tree's opening checks (`paths`); the query phase accepts (`decides`). -/
structure Accepts [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} (x : X)
    (π : M.NIProof) (Q : M.IOPQueries V x) : Prop where
  /-- The sampler accepts the stream of every challenge. -/
  sampled : ∀ c, (M.chal h ⟨π.salt, x⟩ π.writes c).isSome
  /-- One opened leaf per queried position. -/
  leaves_length : (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)).length =
    π.leaves.length
  /-- Every tree's opening checks. -/
  paths : ∀ τ ∈ M.trees (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)),
    Base.checkTree h π
      (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)) τ
  /-- The query phase's decision accepts. -/
  decides : Q.verdict (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes) π.leaves =
    true

end

end GordieHowe.SPBCS
