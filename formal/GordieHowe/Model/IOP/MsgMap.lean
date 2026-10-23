-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Round-by-round knowledge soundness along a map of messages

Two protocols `Q` and `P` with the same rounds and directions, and a map of messages from each
round of `Q` to the same round of `P` that is a bijection at every challenge round
(`ProtocolSpec.MsgMap`), relate their transcripts round by round (`MsgMap.transcript`).
Round-by-round knowledge soundness of `P` gives that of `Q` (`rbrKnowledgeSoundness.comap`): at
the extractor and the state function read through the map (`Extractor.comap`,
`KnowledgeStateFunction.comap`), for every verifier of `Q` that accepts only transcripts whose
image the verifier of `P` accepts, with the error of each challenge round of `Q` the error of the
same round of `P`. A uniform challenge of `Q` maps to a uniform challenge of `P`
(`probUniform_comp_bijective`), and a prover message of `Q` maps to a prover message of `P`, which
never makes a false state true.

Two uses: a prover message that carries data the verifier and the extractor never read (the
pads of the late values in the first message of the source protocol of a GordieHowe program,
`GordieHowe/Language/RealizedProgram/SourcePaper.lean`) can be dropped or filled in either direction; and a stricter
verifier of the same protocol (the identity map) keeps round-by-round knowledge soundness.
-/

namespace GordieHowe.IOP

open scoped NNReal ENNReal

/-- **A bijection preserves the uniform probability of an event**: an event on the image of a
uniform element of `α` under a bijection `f : α → β` has the probability of the event on a uniform
element of `β`. -/
theorem probUniform_comp_bijective {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] {f : α → β} (hf : Function.Bijective f) (p : β → Prop) :
    Pr[a ← α : p (f a)] = Pr[b ← β : p b] := by
  classical
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_of_bijective hf]
  congr 2
  rw [← Finset.card_map ⟨f, hf.1⟩]
  congr 1
  ext b
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hb
    obtain ⟨a, rfl⟩ := hf.2 b
    exact ⟨a, hb, rfl⟩

/-- **The second coordinate of a uniform pair is uniform**: an event on the second coordinate of a
uniform element of `A × C` has the probability of the event on a uniform element of `C`. -/
theorem probUniform_prod_snd {A C : Type} [Fintype A] [Nonempty A] [Fintype C] [Nonempty C]
    (p : C → Prop) : Pr[ac ← (A × C) : p ac.2] = Pr[c ← C : p c] := by
  rw [probUniform_prod_eq_tsum]
  simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

open Classical in
/-- **An event bounded at one coordinate whatever the others**: if, at every point `f` of a finite
product, the event at `f` with coordinate `i` replaced by a uniform value has probability at most
`δ`, the event has probability at most `δ` over a uniform point of the product. -/
theorem probUniform_le_of_update {ι : Type*} [DecidableEq ι] [Fintype ι] {β : ι → Type*}
    [∀ j, Fintype (β j)] [∀ j, Nonempty (β j)] (i : ι) (bad : (∀ j, β j) → Prop) {δ : ℝ≥0}
    (h : ∀ f : ∀ j, β j, Pr[v ← β i : bad (Function.update f i v)] ≤ δ) :
    Pr[f ← (∀ j, β j) : bad f] ≤ δ := by
  rw [← card_le_iff_probUniform_le]
  refine card_le_of_card_update_le i fun f => ?_
  have hf := (card_le_iff_probUniform_le _ _ _).mpr (h f)
  simpa using hf

/-- **An event of probability at most `0` under a uniform draw never holds.** -/
theorem not_of_probUniform_le_zero {C : Type*} [Fintype C] [Nonempty C] {p : C → Prop}
    (h : Pr[c ← C : p c] ≤ 0) (c : C) : ¬ p c := by
  classical
  intro hc
  rw [probUniform_eq_card_div, nonpos_iff_eq_zero, ENNReal.div_eq_zero_iff] at h
  rcases h with h | h
  · have : c ∈ Finset.univ.filter p := Finset.mem_filter.2 ⟨Finset.mem_univ c, hc⟩
    rw [Nat.cast_eq_zero, Finset.card_eq_zero] at h
    simp [h] at this
  · exact ENNReal.natCast_ne_top _ h

variable {n : ℕ}

/-- **A map of messages from the protocol `Q` to the protocol `P`** with the same rounds: the rounds
have the same directions, each round's message of `Q` maps to a message of the same round of `P`,
and at every challenge round the map is a bijection. -/
structure ProtocolSpec.MsgMap (Q P : ProtocolSpec n) where
  /-- The rounds have the same directions. -/
  dir_eq : ∀ i, Q.dir i = P.dir i
  /-- The message of each round. -/
  map : ∀ i, Q.Type i → P.Type i
  /-- At each challenge round, the map is a bijection. -/
  bijective : ∀ i, Q.dir i = .V_to_P → Function.Bijective (map i)

namespace ProtocolSpec.MsgMap

variable {Q P : ProtocolSpec n} (g : Q.MsgMap P)

/-- **A transcript of `Q` mapped round by round** to a transcript of `P`. -/
def transcript {m : Fin (n + 1)} (tr : Q.Transcript m) : P.Transcript m :=
  fun i => g.map _ (tr i)

/-- **The challenge round of `P`** at a challenge round of `Q`: the same round. -/
def chalIdx (i : Q.ChallengeIdx) : P.ChallengeIdx := ⟨i.1, (g.dir_eq i.1).symm.trans i.2⟩

/-- **Mapping commutes with appending a message.** -/
theorem transcript_concat {m : Fin n} (tr : Q.Transcript m.castSucc) (msg : Q.Type m) :
    g.transcript (Q.concat tr msg) = P.concat (g.transcript tr) (g.map m msg) := by
  funext i
  obtain ⟨i, hi⟩ := i
  simp only [transcript, ProtocolSpec.concat, Fin.snoc]
  split_ifs with h
  · rfl
  · obtain rfl : i = m.1 := by simp only [Fin.val_succ] at hi; omega
    rfl

/-- **Mapping commutes with taking a prefix.** -/
theorem transcript_take {k : Fin (n + 1)} (m : Fin (n + 1)) (hm : m ≤ k) (tr : Q.Transcript k) :
    g.transcript (tr.take m hm) = (g.transcript tr).take m hm :=
  rfl

end ProtocolSpec.MsgMap

variable {Q P : ProtocolSpec n} {StmtIn W : Type}

/-- **An extractor of `P` read through a map of messages**: at a prefix of `Q`, the extractor at
the mapped prefix.

Running time: the map of each round's message of the prefix, then `E`'s. Polynomial when `E` and
the map are. This running time is argued here, not proved in Lean. -/
def Extractor.comap (E : Extractor P StmtIn W) (g : Q.MsgMap P) : Extractor Q StmtIn W where
  extract m x tr := E m x (g.transcript tr)

/-- **A state function of `P` read through a map of messages**: at a prefix of `Q`, the state at the
mapped prefix. It is a state function for every verifier `V'` of `Q` that accepts only transcripts
whose image `V` accepts. -/
def KnowledgeStateFunction.comap {V : Verifier P StmtIn} (S : KnowledgeStateFunction V)
    (g : Q.MsgMap P) {V' : Verifier Q StmtIn}
    (hV : ∀ x tr, V' x tr = true → V x (g.transcript tr) = true) :
    KnowledgeStateFunction V' where
  toFun m x tr := S.toFun m x (g.transcript tr)
  toFun_empty x _ := S.toFun_empty x _
  toFun_next m hm x tr msg h := by
    rw [g.transcript_concat]
    exact S.toFun_next m ((g.dir_eq m).symm.trans hm) x _ _ h
  toFun_full x tr h := S.toFun_full x _ (hV x tr h)

/-- **Round-by-round knowledge soundness along a map of messages**: if `P` is round-by-round
knowledge sound for `rel` at `V`, `E`, `S` and errors `ε`, then `Q` is, at every verifier `V'` that
accepts only transcripts whose image `V` accepts, the extractor and the state function read through
the map, and the error of each challenge round of `Q` that of the same round of `P`. -/
theorem rbrKnowledgeSoundness.comap [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [∀ i, Fintype (Q.Challenge i)]
    [∀ i, Nonempty (Q.Challenge i)] {rel : Set (StmtIn × W)} {V : Verifier P StmtIn}
    {E : Extractor P StmtIn W} {S : KnowledgeStateFunction V} {ε : P.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel V E S ε) (g : Q.MsgMap P) {V' : Verifier Q StmtIn}
    (hV : ∀ x tr, V' x tr = true → V x (g.transcript tr) = true) :
    rbrKnowledgeSoundness rel V' (E.comap g) (S.comap g hV) fun i => ε (g.chalIdx i) := by
  intro x i tr
  have hb := g.bijective i.1 i.2
  change Pr[c ← Q.Challenge i : (x, E i.1.castSucc x (g.transcript tr)) ∉ rel ∧
      ¬ S.toFun i.1.castSucc x (g.transcript tr) ∧
        S.toFun i.1.succ x (g.transcript (Q.concat tr c))] ≤ ε (g.chalIdx i)
  simp only [g.transcript_concat]
  have e := probUniform_comp_bijective (β := P.Challenge (g.chalIdx i)) (f := g.map i.1) hb
    (fun c => (x, E i.1.castSucc x (g.transcript tr)) ∉ rel ∧
      ¬ S.toFun i.1.castSucc x (g.transcript tr) ∧
        S.toFun i.1.succ x (P.concat (g.transcript tr) c))
  exact e.trans_le (h x (g.chalIdx i) (g.transcript tr))

end GordieHowe.IOP
