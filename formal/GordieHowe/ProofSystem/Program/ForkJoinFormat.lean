-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkJoinBCS
public import GordieHowe.SPBCS.Format.SpecWrites
public import GordieHowe.SPBCS.Sampler.ChallengeReader
public import GordieHowe.ProofSystem.Program.Basic
public import GordieHowe.SPBCS.Sampler.ChallengeReader

@[expose] public section

/-!
# The codecs and the samplers of a multi-circuit IOP with forked domains

The pieces of a setting (`GordieHowe.SPBCS.Setting`) for the composite IOP of a
multi-circuit IOP with forked domains (`GordieHowe.RealizedProgram.ProofSystem.IOP.toCausalIOP`), assembled from the parts of the
IOP:

* `writeOf`: the write of every prover message of every component: at the prefix, the roots of the
  domains' trees for the first message (one byte-string write per tree, `WriteCodec.roots`) and
  the commit rounds' and the application phase's codecs for the later ones (`prefixLater`); at a
  branch or a join part, its codecs (`SpecWrites`), every message read in full;
* `leafOf`: the leaf codec of every tree (the domains' trees of the prefix's first message);
* `readersOf`, `samplersOf`, `preimagesOf`: the challenge readers of every component (the prefix:
  the domains' commit rounds, then the application phase), the samplers they define on the
  `k + e`-byte stream at per-round stream lengths, and their preimage samplers.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec IOP.SPTerm SPBCS
open scoped NNReal

namespace RealizedProgram.ProofSystem.IOP

variable {Stmt W : Type} {rel : Set (Stmt × W)} (C : IOP Stmt W rel) {k B : ℕ}

/-- The prefix's first message is read as the table of the domains' trees. -/
theorem preShape_of_eq {i : (C.P .pre).MessageIdx} (h : (i.1 : ℕ) = 0) :
    C.preShape i = .trees C.m (fun d => (C.oracle d).nLeaves) (fun d => (C.oracle d).Leaf)
      (fun d => (C.oracle d).leafDefault)
      ((Equiv.cast (congrArg (C.P .pre).Type (Fin.ext h : i.1 = ⟨0, C.pos_rounds_pre⟩))).trans
        ((Equiv.cast C.type_zero).trans C.leavesEquiv)) :=
  dite_eq_left h

/-- The prefix's later messages are read in full. -/
theorem preShape_of_ne {i : (C.P .pre).MessageIdx} (h : (i.1 : ℕ) ≠ 0) :
    C.preShape i = .plain _ :=
  dite_eq_right h

/-- The write of the prefix's first message is the roots of the domains' trees. -/
theorem prefixWrite_of_eq {i : (C.P .pre).MessageIdx} (h : (i.1 : ℕ) = 0) :
    CompWrite C.toCausalIOP k .pre i = Write Unit C.m k := by
  change Write (C.preShape i).NonOracle (C.preShape i).nTrees k = _
  rw [C.preShape_of_eq h]
  rfl

/-- The write of a later message of the prefix is the message, with no roots. -/
theorem prefixWrite_of_ne {i : (C.P .pre).MessageIdx} (h : (i.1 : ℕ) ≠ 0) :
    CompWrite C.toCausalIOP k .pre i = Write ((C.P .pre).Type i.1) 0 k := by
  change Write (C.preShape i).NonOracle (C.preShape i).nTrees k = _
  rw [C.preShape_of_ne h]
  rfl

/-- The commit rounds and the application phase, after the commitment round. -/
abbrev roundsApp : ProtocolSpec (C.nc + C.app.n) := C.commitRounds ++ C.app.spec

/-- A prover round of the prefix that is a round of the commitment round is round `0`. -/
theorem val_eq_zero_of_inl {j : (C.P .pre).MessageIdx} {c : (commitSpec C.Com).MessageIdx}
    (h : messageIdxEquiv (P₁ := commitSpec C.Com) (P₂ := C.roundsApp) j = .inl c) :
    (j.1 : ℕ) = 0 := by
  rw [MessageIdx.eq_inl_of_equiv h, MessageIdx.val_inl, Fin.val_castAdd]
  exact Fin.val_eq_zero c.1

/-- **The codec of a later prover round of the prefix**, given the part's round `s` that it is:
the commit rounds' or the application phase's codec (`Wra`). -/
def prefixLater (Wra : SpecWrites C.roundsApp B) (j : (C.P .pre).MessageIdx) (hj : (j.1 : ℕ) ≠ 0) :
    ∀ s, messageIdxEquiv (P₁ := commitSpec C.Com) (P₂ := C.roundsApp) j = s →
      WriteCodec ((C.P .pre).Type j.1)
  | .inl _, h => absurd (C.val_eq_zero_of_inl h) hj
  | .inr a, h => (Wra.write a).appendInr h

theorem prefixLater_le (Wra : SpecWrites C.roundsApp B) (j : (C.P .pre).MessageIdx)
    (hj : (j.1 : ℕ) ≠ 0) : ∀ s h, (C.prefixLater Wra j hj s h).B ≤ B
  | .inl _, h => absurd (C.val_eq_zero_of_inl h) hj
  | .inr a, _ => Wra.le a

/-- **The write of every prover message of every component** (module docstring). -/
def writeOf (Wra : SpecWrites C.roundsApp B)
    (Wbr : ∀ d b, SpecWrites ((C.circuit d).branch b) B) (Wjn : ∀ d, SpecWrites (C.circuit d).join B) :
    ∀ j i, WriteCodec (CompWrite C.toCausalIOP k j i)
  | .pre, i =>
    if h : (i.1 : ℕ) = 0 then
      ((WriteCodec.roots C.m k).mapEquiv (Write.rootsEquiv _ _)).mapEquiv
        (Equiv.cast (C.prefixWrite_of_eq h))
    else ((C.prefixLater Wra i h _ rfl).mapEquiv (Write.nonOracleEquiv _ _)).mapEquiv
      (Equiv.cast (C.prefixWrite_of_ne h))
  | .br d b, i => ((Wbr d b).write i).mapEquiv (Write.nonOracleEquiv _ _)
  | .jn d, i => ((Wjn d).write i).mapEquiv (Write.nonOracleEquiv _ _)

theorem writeOf_B_le {Wra : SpecWrites C.roundsApp B}
    {Wbr : ∀ d b, SpecWrites ((C.circuit d).branch b) B} {Wjn : ∀ d, SpecWrites (C.circuit d).join B}
    (hroots : C.m * (9 + k) ≤ B) : ∀ j i, (C.writeOf (k := k) Wra Wbr Wjn j i).B ≤ B
  | .pre, i => by
    rw [writeOf]
    split_ifs with h
    · exact (WriteCodec.roots_B C.m k).trans_le hroots
    · exact C.prefixLater_le Wra i h _ rfl
  | .br d b, i => (Wbr d b).le i
  | .jn d, i => (Wjn d).le i

/-- The prefix's first message carries the domains' trees. -/
theorem nTrees_pre_of_eq {i : (C.P .pre).MessageIdx} (h : (i.1 : ℕ) = 0) :
    (C.comp .pre).nTrees i = C.m := by
  change (C.preShape i).nTrees = _
  rw [C.preShape_of_eq h]
  rfl

/-- **The leaf codec of every tree**: tree `d` of the prefix's first message by `lc d`; no other
message has trees. -/
def leafOf (lc : ∀ d, Codec (C.oracle d).Leaf) :
    ∀ j i (t : Fin ((C.comp j).nTrees i)), Codec ((C.comp j).Leaf i t)
  | .pre, i, t =>
    if h : (i.1 : ℕ) = 0 then
      cast (congrArg (fun i => ∀ t : Fin ((C.comp .pre).nTrees i), Codec ((C.comp .pre).Leaf i t))
        (Subtype.ext (Fin.ext h) : i = C.oracleIdx).symm) lc t
    else (Fin.cast (C.nTrees_comp_eq_zero i (.inr h)) t).elim0
  | .br _ _, _, t => t.elim0
  | .jn _, _, t => t.elim0

theorem leafOf_fit {lc : ∀ d, Codec (C.oracle d).Leaf} {L : ℕ}
    (hfit : ∀ d c, ((lc d).ser c).length ≤ L) :
    ∀ j i t c, ((C.leafOf lc j i t).ser c).length ≤ L
  | .pre, i, t, c => by
    rw [leafOf]
    split_ifs with h
    · obtain rfl : i = C.oracleIdx := Subtype.ext (Fin.ext h)
      exact hfit t c
    · exact (Fin.cast (C.nTrees_comp_eq_zero i (.inr h)) t).elim0
  | .br _ _, _, t, _ => t.elim0
  | .jn _, _, t, _ => t.elim0

/-- **A message carries at most one tree per domain.** -/
theorem nTrees_le_m : ∀ (j : C.shape.Idx) (i : (C.P j).MessageIdx), (C.comp j).nTrees i ≤ C.m
  | .pre, i => by
    by_cases h : (i.1 : ℕ) = 0
    · exact (C.nTrees_pre_of_eq h).le
    · exact (C.nTrees_comp_eq_zero i (.inr h)).trans_le (Nat.zero_le _)
  | .br d b, i => (C.nTrees_comp_eq_zero i (.inl (by simp))).trans_le (Nat.zero_le _)
  | .jn d, i => (C.nTrees_comp_eq_zero i (.inl (by simp))).trans_le (Nat.zero_le _)

/-- **Every tree has at most `N` leaves** when every domain's tree has. -/
theorem nLeaves_comp_le {N : ℕ} (hN : ∀ d, (C.oracle d).nLeaves ≤ N) :
    ∀ (j : C.shape.Idx) (i : (C.P j).MessageIdx) (t : Fin ((C.comp j).nTrees i)),
      (C.comp j).nLeaves i t ≤ N
  | .pre, i, t => by
    by_cases hi : (i.1 : ℕ) = 0
    · obtain rfl : i = C.oracleIdx := Subtype.ext (Fin.ext hi)
      revert t
      change ∀ t : Fin (C.preShape C.oracleIdx).nTrees, (C.preShape C.oracleIdx).nLeaves t ≤ N
      rw [C.preShape_of_eq rfl]
      exact fun t => hN t
    · exact (Fin.cast (C.nTrees_comp_eq_zero i (.inr hi)) t).elim0
  | .br d b, i, t => (Fin.cast (C.nTrees_comp_eq_zero i (.inl (by simp))) t).elim0
  | .jn d, i, t => (Fin.cast (C.nTrees_comp_eq_zero i (.inl (by simp))) t).elim0

/-- **The leaves of a component's trees**: the domains' at the prefix, none elsewhere. -/
theorem sum_nLeaves_comp (j : C.shape.Idx) :
    ∑ i, ∑ t : Fin ((C.comp j).nTrees i), (C.comp j).nLeaves i t =
      if j = .pre then ∑ d, (C.oracle d).nLeaves else 0 := by
  have hz : ∀ i : (C.P j).MessageIdx, (C.comp j).nTrees i = 0 →
      ∑ t : Fin ((C.comp j).nTrees i), (C.comp j).nLeaves i t = 0 := fun i h =>
    Finset.sum_eq_zero fun t _ => (Fin.cast h t).elim0
  split_ifs with hj
  · subst hj
    rw [Finset.sum_eq_single C.oracleIdx]
    · change ∑ t : Fin (C.preShape C.oracleIdx).nTrees, (C.preShape C.oracleIdx).nLeaves t = _
      rw [C.preShape_of_eq rfl]
      rfl
    · intro i _ hi
      exact hz i (C.nTrees_comp_eq_zero i (.inr fun h => hi (Subtype.ext (Fin.ext h))))
    · exact fun h => absurd (Finset.mem_univ _) h
  · exact Finset.sum_eq_zero fun i _ => hz i (C.nTrees_comp_eq_zero i (.inl hj))

/-- **The queried leaves** are at most `q d` per domain when domain `d`'s verdict reads at most
`q d` leaves. -/
theorem length_queryList_le {q : Fin C.m → ℕ} (hq : ∀ d ch, ((C.oracle d).queries ch).card ≤ q d)
    (ch : Chs C.P C.term) : (C.queryList ch).length ≤ ∑ d, q d := by
  unfold queryList
  rw [List.length_flatMap, ← Fin.sum_univ_def]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [List.length_map, Finset.length_sort]
  exact hq d _

/-- **The rounds of the series–parallel term**: the commitment round, every domain's commit rounds, the
application phase, and every domain's branches and join part. -/
theorem sum_rounds :
    ∑ q : C.shape.term.Leaf, C.rounds q.label =
      1 + (∑ d, (C.circuit d).nc + C.app.n) + ∑ d, (∑ b, (C.circuit d).bn b + (C.circuit d).jn) := by
  rw [IOP.Shape.sum_leaves_label]
  change 1 + (lenN C.m _ + C.app.n) + _ = _
  rw [lenN_eq_sum]
  rfl

/-! ### The challenge readers and the samplers -/

/-- **The challenge readers of every component**: at the prefix, none at the commitment round,
then every domain's commit-round readers `rr d` in order and the application phase's `rApp`; at a
branch or a join part, its own. -/
def readersOf (rr : ∀ d, SpecReaders (C.circuit d).commitRounds) (rApp : SpecReaders C.app.spec)
    (rbr : ∀ d b, SpecReaders ((C.circuit d).branch b)) (rjn : ∀ d, SpecReaders (C.circuit d).join) :
    ∀ j, SpecReaders (C.P j)
  | .pre => SpecReaders.append (P₁ := commitSpec C.Com) (fun c => (commitSpec.not_challengeIdx c).elim)
      (SpecReaders.appendN C.m rr ++ rApp)
  | .br d b => rbr d b
  | .jn d => rjn d

/-- **The loads of every component's readers** satisfy `good` when the domains' commit rounds',
the application phase's, the branches' and the join parts' do. -/
theorem readersOf_allLoads {rr : ∀ d, SpecReaders (C.circuit d).commitRounds}
    {rApp : SpecReaders C.app.spec} {rbr : ∀ d b, SpecReaders ((C.circuit d).branch b)}
    {rjn : ∀ d, SpecReaders (C.circuit d).join} {good : SPBCS.Load → Prop}
    (hr : ∀ d, (rr d).AllLoads good) (happ : rApp.AllLoads good)
    (hbr : ∀ d b, (rbr d b).AllLoads good) (hjn : ∀ d, (rjn d).AllLoads good) :
    ∀ j, (C.readersOf rr rApp rbr rjn j).AllLoads good
  | .pre => SpecReaders.append_allLoads (r₁ := fun c => (commitSpec.not_challengeIdx c).elim)
      (fun c => (commitSpec.not_challengeIdx c).elim)
      (SpecReaders.append_allLoads (SpecReaders.appendN_allLoads C.m hr) happ)
  | .br d b => hbr d b
  | .jn d => hjn d

/-- **The challenge samplers of every component** on the `k + e`-byte stream, round `i` of
component `j` reading at most `N j i` bytes (`SpecReaders.sampler`). -/
def samplersOf (rd : ∀ j, SpecReaders (C.P j)) (k e : ℕ)
    (N : ∀ j, (C.P j).ChallengeIdx → ℕ) (j : C.shape.Idx) (i : (C.P j).ChallengeIdx) :
    SPBCS.Sampler k e ((C.P j).Challenge i) :=
  SpecReaders.sampler (P := C.P j) (rd j) k e (N j) i

/-- **The preimage samplers of the challenge samplers** (`SpecReaders.preimage`). -/
def preimagesOf (rd : ∀ j, SpecReaders (C.P j)) (k e : ℕ)
    (N : ∀ j, (C.P j).ChallengeIdx → ℕ) (j : C.shape.Idx) (i : (C.P j).ChallengeIdx) :
    (C.samplersOf rd k e N j i).Preimage :=
  SpecReaders.preimage (P := C.P j) (rd j) k e (N j) i

end RealizedProgram.ProofSystem.IOP

end GordieHowe
