-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.Extract
public import GordieHowe.Model.IOP.RBR
public import GordieHowe.SPBCS.Extraction.Position
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# Hash chains: items, chain-input encodings, samplers and salted statements

The objects of a Fiat–Shamir hash chain over the domain-separated oracle of
`GordieHowe/Model/QROM/Oracle.lean`, used by the spBCS compiler and its series–parallel base model
(`GordieHowe/SPBCS/Basic.lean`, `GordieHowe/SPBCS/FullPast/Model.lean`). They follow
Chiesa–Manohar–Spooner, "Succinct Arguments in the Quantum Random Oracle Model" (CMS19,
ePrint 2019/834; printed page numbers), section 8.2 (the BCS hash chain, pp. 38–39).

- `Item k W`: one round of a chain, a prover write or the digest absorbed after a challenge round
  (the challenge write-back of CMS19 section 8.6, p. 45; C++ `close_point`,
  `lib/random/transcript.h` lines 382–396); `chainDigests`: the digests a chain carries.
- `Fits`, `chainWF`: the well-formed chains of a protocol.
- `Sampler k e C`: a challenge sampler, a partial map from the `k + e`-byte stream to a challenge
  with equal fibres (the C++ challenge expansion from `FSXOF`, `lib/random/transcript.h`).
- Database facts used by the database extractors; `SaltedStatement kS X`: the proof's Fiat–Shamir
  salt and the statement, written at the start of every `transcript` input (strong Fiat–Shamir).
- `defaultOut`: the default answer; `keyCollision n k = (n choose 2) / 2^(8k)`: the bound on two of
  `n` rounds deriving the same key.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP
open scoped ENNReal

variable {k kN kS L e : ℕ}

/-- One round of the hash chain: a prover write, or the digest absorbed after a
challenge round. -/
inductive Item (k : ℕ) (W : Type) where
  | write (w : W)
  | absorb (d : Digest k)

namespace Item

variable {W : Type}

/-- The digests an item carries: the Merkle roots `dg w` of a write, the absorbed digest. -/
def digests (dg : W → Finset (Digest k)) : Item k W → Finset (Digest k)
  | write w => dg w
  | absorb d => {d}

end Item

/-- The digests carried by a chain. -/
def chainDigests {W : Type} (dg : W → Finset (Digest k)) : List (Item k W) → Finset (Digest k)
  | [] => ∅
  | it :: l => it.digests dg ∪ chainDigests dg l

theorem mem_chainDigests {W : Type} {dg : W → Finset (Digest k)} {l : List (Item k W)}
    {d : Digest k} : d ∈ chainDigests dg l ↔ ∃ it ∈ l, d ∈ it.digests dg := by
  induction l with
  | nil => simp [chainDigests]
  | cons it l ih => simp [chainDigests, ih]

theorem chainDigests_take_subset {W : Type} (dg : W → Finset (Digest k)) (l : List (Item k W))
    (r : ℕ) : chainDigests dg (l.take r) ⊆ chainDigests dg l := by
  intro d hd
  obtain ⟨it, hit, h⟩ := mem_chainDigests.1 hd
  exact mem_chainDigests.2 ⟨it, List.mem_of_mem_take hit, h⟩

/-- A chain of items carrying at most `nd ≥ 1` digests each carries at most `|l| · nd`. -/
theorem card_chainDigests_le {W : Type} {dg : W → Finset (Digest k)} {nd : ℕ}
    (hdg : ∀ w, (dg w).card ≤ nd) (hnd : 1 ≤ nd) :
    ∀ l : List (Item k W), (chainDigests dg l).card ≤ l.length * nd
  | [] => by simp [chainDigests]
  | it :: l => by
    have hit : (it.digests dg).card ≤ nd := by
      cases it with
      | write w => exact hdg w
      | absorb d => simpa [Item.digests] using hnd
    have := card_chainDigests_le hdg hnd l
    rw [chainDigests, List.length_cons, Nat.succ_mul]
    exact (Finset.card_union_le _ _).trans (by omega)

/-! ### Well-formed chains of a protocol -/

section WellFormed

variable {n : ℕ} (P : ProtocolSpec n) {Wr : P.MessageIdx → Type}

/-- Item `it` fits position `r` of a chain of `P`: a write of round `r`, or an absorbed
digest at a challenge round `r`. -/
def Fits (r : ℕ) : Item k (Σ i : P.MessageIdx, Wr i) → Prop
  | .write w => w.1.1.1 = r
  | .absorb _ => ∃ h : r < n, P.dir ⟨r, h⟩ = .V_to_P

/-- A chain of `P` is well formed when every item fits its position. -/
def chainWF (l : List (Item k (Σ i : P.MessageIdx, Wr i))) : Prop :=
  ∀ r (h : r < l.length), Fits P r l[r]

variable {P}

theorem lt_of_fits {r : ℕ} {it : Item k (Σ i : P.MessageIdx, Wr i)} (h : Fits P r it) : r < n := by
  cases it with
  | write w => exact h ▸ w.1.1.2
  | absorb d => exact h.1

end WellFormed

/-! ### The sampler -/

/-- The challenge sampler of a round: a partial map from the `k + e`-byte XOF stream to a
challenge (the C++ challenge expansion from `FSXOF`). On a uniform
stream every challenge has the same number of preimages (the output is exactly uniform
given `some`); its rejection probability is `SPBCS.Sampler.rejectionProb`. -/
structure Sampler (k e : ℕ) (C : Type) [Fintype C] [DecidableEq C] where
  sample : (Fin (k + e) → Byte) → Option C
  /-- The challenge read where the sampler rejects (the verifier rejects there), so that the
  challenges of a transcript are a total function. -/
  default : C
  card_eq : ∀ c c' : C, (Finset.univ.filter fun s => sample s = some c).card =
    (Finset.univ.filter fun s => sample s = some c').card

namespace Sampler

/-- **The rejection probability of a sampler**: the exact probability that it returns `none` on
a uniform stream. For an abstract sampler it may be `1`; the C++
samplers bound it (`Sampler.ofReader_rejectionProb`, `CReader.failProb_le`). -/
noncomputable def rejectionProb {C : Type} [Fintype C] [DecidableEq C] (S : Sampler k e C) : ℝ≥0∞ :=
  Pr[s ← (Fin (k + e) → Byte) : S.sample s = none]

theorem prob_none_le {C : Type} [Fintype C] [DecidableEq C] (S : Sampler k e C) :
    Pr[s ← (Fin (k + e) → Byte) : S.sample s = none] ≤ S.rejectionProb :=
  le_rfl

/-- The rejection probability is a probability. -/
theorem rejectionProb_le_one {C : Type} [Fintype C] [DecidableEq C] (S : Sampler k e C) : S.rejectionProb ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _))

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C] (S : Sampler k e C)

/-- Counting a property of the stream `Out.stream y` over answers `y` is counting it over
streams: `Out.stream` is the bijection `Out.streamEquiv`. -/
theorem card_filter_stream (p : (Fin (k + e) → Byte) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun y : Out k e => p y.stream).card =
      (Finset.univ.filter p).card := by
  refine Finset.card_bij (fun y _ => y.stream) (by simp) ?_ ?_
  · intro a _ b _ h
    exact Out.streamEquiv.injective h
  · intro s hs
    have h : Out.stream (Out.streamEquiv.symm s : Out k e) = s :=
      Out.streamEquiv.apply_symm_apply s
    exact ⟨Out.streamEquiv.symm s,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [h]; exact (Finset.mem_filter.1 hs).2⟩, h⟩

theorem card_out : Fintype.card (Out k e) = Fintype.card (Fin (k + e) → Byte) :=
  Fintype.card_congr Out.streamEquiv

open Classical in
/-- The sampler is at most uniform: a set `A` of challenges is hit with probability at
most `|A| / |C|`, the uniform probability of `A`. -/
theorem prob_mem_le (A : Set C) :
    Pr[y ← Out k e : ∃ c ∈ A, S.sample y.stream = some c] ≤ Pr[c ← C : c ∈ A] := by
  set N := (Finset.univ.filter fun s => S.sample s = some (Classical.arbitrary C)).card
  have hN : ∀ c, (Finset.univ.filter fun s => S.sample s = some c).card = N :=
    fun c => S.card_eq c _
  -- `|C| · N ≤ |stream|`: the fibres over the challenges are disjoint.
  have hCN : Fintype.card C * N ≤ Fintype.card (Fin (k + e) → Byte) := by
    have hdisj : ((Finset.univ : Finset C).biUnion fun c =>
        Finset.univ.filter fun s => S.sample s = some c).card =
          ∑ c : C, (Finset.univ.filter fun s => S.sample s = some c).card := by
      refine Finset.card_biUnion fun a _ b _ hab => ?_
      refine Finset.disjoint_left.2 fun s ha hb => hab ?_
      simp only [Finset.mem_filter] at ha hb
      exact Option.some_inj.1 (ha.2.symm.trans hb.2)
    calc Fintype.card C * N = ∑ c : C, (Finset.univ.filter fun s => S.sample s = some c).card := by
          simp [hN, Finset.card_univ]
      _ = _ := hdisj.symm
      _ ≤ Fintype.card (Fin (k + e) → Byte) := Finset.card_le_univ _
  let AF : Finset C := Finset.univ.filter (· ∈ A)
  have hcount : (Finset.univ.filter fun s => ∃ c ∈ A, S.sample s = some c).card ≤ AF.card * N := by
    have hsub : (Finset.univ.filter fun s => ∃ c ∈ A, S.sample s = some c) ⊆
        AF.biUnion fun c => Finset.univ.filter fun s => S.sample s = some c := by
      intro s hs
      obtain ⟨c, hc, hs⟩ := (Finset.mem_filter.1 hs).2
      exact Finset.mem_biUnion.2 ⟨c, by simp [AF, hc], by simp [hs]⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    simp [hN, AF]
  rw [probUniform_eq_card_div, probUniform_eq_card_div, card_filter_stream
    (fun s => ∃ c ∈ A, S.sample s = some c), card_out]
  have hC : (Fintype.card C : ℝ≥0∞) ≠ 0 := by simp
  have hS : (Fintype.card (Fin (k + e) → Byte) : ℝ≥0∞) ≠ 0 := by simp
  have hnat : (Finset.univ.filter fun s => ∃ c ∈ A, S.sample s = some c).card *
      Fintype.card C ≤ AF.card * Fintype.card (Fin (k + e) → Byte) :=
    calc _ ≤ AF.card * N * Fintype.card C := Nat.mul_le_mul_right _ hcount
      _ = AF.card * (Fintype.card C * N) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hCN
  rw [ENNReal.div_le_iff hS (by simp), ← ENNReal.mul_div_right_comm,
    ENNReal.le_div_iff_mul_le (Or.inl hC) (Or.inl (by simp))]
  exact_mod_cast hnat

/-- Every challenge has at most `|stream| / |C|` streams sampling it: the fibres of the sampler
are disjoint and of one size. -/
theorem card_fibre_mul_le (c : C) :
    (Finset.univ.filter fun y : Out k e => S.sample y.stream = some c).card * Fintype.card C ≤
      Fintype.card (Out k e) := by
  classical
  have hN : ∀ c', (Finset.univ.filter fun y : Out k e => S.sample y.stream = some c').card =
      (Finset.univ.filter fun y : Out k e => S.sample y.stream = some c).card := fun c' => by
    rw [card_filter_stream (fun s => S.sample s = some c'),
      card_filter_stream (fun s => S.sample s = some c), S.card_eq]
  calc _ = ∑ c' : C, (Finset.univ.filter fun y : Out k e => S.sample y.stream = some c').card := by
        simp [hN, Finset.card_univ, mul_comm]
    _ = ((Finset.univ : Finset C).biUnion fun c' =>
          Finset.univ.filter fun y : Out k e => S.sample y.stream = some c').card := by
        refine (Finset.card_biUnion fun a _ b _ hab => ?_).symm
        refine Finset.disjoint_left.2 fun y ha hb => hab ?_
        simp only [Finset.mem_filter] at ha hb
        exact Option.some_inj.1 (ha.2.symm.trans hb.2)
    _ ≤ _ := Finset.card_le_univ _

end Sampler

open Classical in
/-- **Sampled challenges are dominated by uniform challenges**: for samplers `S i` reading
independent uniform answers `g i`, the probability that every sampler accepts and the sampled
challenges lie in `R` is at most the uniform probability of `R`. -/
theorem Sampler.prob_forall_sample_le {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → Type}
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)] [∀ i, Nonempty (C i)]
    (S : (i : ι) → Sampler k e (C i)) (R : ((i : ι) → C i) → Prop) :
    Pr[g ← (ι → Out k e) : (∀ i, ((S i).sample (g i).stream).isSome) ∧
        R fun i => ((S i).sample (g i).stream).getD (S i).default] ≤
      Pr[c ← ((i : ι) → C i) : R c] := by
  -- the sampled challenges lie in `R`, so the answers lie in one fibre per challenge in `R`
  let fib : ((i : ι) → C i) → Finset (ι → Out k e) := fun c =>
    Fintype.piFinset fun i => Finset.univ.filter fun y : Out k e => (S i).sample y.stream = some (c i)
  have hsub : (Finset.univ.filter fun g : ι → Out k e => (∀ i, ((S i).sample (g i).stream).isSome) ∧
      R fun i => ((S i).sample (g i).stream).getD (S i).default) ⊆
        (Finset.univ.filter R).biUnion fib := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    refine Finset.mem_biUnion.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg.2⟩, ?_⟩
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hg.1 i)
    simp [hc]
  have hfib : ∀ c, (fib c).card * Fintype.card ((i : ι) → C i) ≤
      Fintype.card (Out k e) ^ Fintype.card ι := by
    intro c
    rw [Fintype.card_piFinset, Fintype.card_pi, ← Finset.prod_mul_distrib]
    calc _ ≤ ∏ _i : ι, Fintype.card (Out k e) :=
          Finset.prod_le_prod fun i _ => (S i).card_fibre_mul_le (c i)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_fun]
  refine natCast_div_le_natCast_div (by simp) Fintype.card_ne_zero ?_
  calc _ ≤ ((Finset.univ.filter R).biUnion fib).card * Fintype.card ((i : ι) → C i) :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ c ∈ Finset.univ.filter R, (fib c).card) * Fintype.card ((i : ι) → C i) :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ ≤ _ := by
        rw [Finset.sum_mul, ← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun c _ => hfib c

/-! ### Database facts used by the extractor -/

section DBFacts

variable {D : ODB k kN kS L e} {x q : Query k kN kS L} {y v : Out k e}

/-- A recorded answer survives recording a new input. -/
theorem lookup_extend_of_lookup (hx : x ∉ D) (h : D.lookup q = some v) :
    (D.extend x y).lookup q = some v := by
  have hq : q ≠ x := fun hqx => hx (hqx ▸ DB.mem_iff_lookup.2 ⟨v, h⟩)
  rw [DB.lookup_extend_of_ne hq, h]

/-- A lookup that succeeds after recording `x ↦ y` but not before is the new entry. -/
theorem eq_of_lookup_extend (h : D.lookup q = none) (h' : (D.extend x y).lookup q = some v) :
    q = x ∧ v = y := by
  by_cases hq : q = x
  · subst hq
    rw [DB.lookup_extend_self] at h'
    exact ⟨rfl, (Option.some_inj.1 h').symm⟩
  · rw [DB.lookup_extend_of_ne hq, h] at h'
    exact absurd h' (by simp)

/-- A recorded `xof` key lies in `S(D)`. -/
theorem key_mem_halfPre {digestsOf : Bytes L → Finset (Digest k)} {κ : Digest k} {σ : FiatShamirSalt kS}
    (h : Query.xof κ σ ∈ D) : κ ∈ halfPre digestsOf D :=
  mem_halfPre.2 ⟨_, h, by simp [Query.digests]⟩

/-- A digest parsed from a recorded `transcript` input lies in `S(D)`. -/
theorem mem_halfPre_of_transcript {digestsOf : Bytes L → Finset (Digest k)} {b : Bytes L}
    {u : Digest k} (h : Query.transcript b ∈ D) (hu : u ∈ digestsOf b) :
    u ∈ halfPre digestsOf D :=
  mem_halfPre.2 ⟨_, h, by simpa [Query.digests] using hu⟩

/-- CMS19 Lemma 6.5 (p. 31) on views: if recording `x ↦ y` changes the extracted tree and
leaves no digest collision, the digest of `y` is the root or lies in `S(D)`. -/
theorem digest_mem_of_view_ne (hx : x ∉ D) (hcol : D.extend x y ∉ digestCollision)
    (digestsOf : Bytes L → Finset (Digest k)) {n : ℕ} {rt : Digest k}
    (h : view (D.extend x y) n rt ≠ view D n rt) :
    y.digest ∈ insert rt (halfPre digestsOf D) := by
  refine digest_mem_of_extract_ne (n := n) hx digestsOf ?_
  rw [extract_eq_some (notMem_collisionOn_of_extend hx hcol), extract_eq_some hcol]
  exact fun h' => h (Option.some_inj.1 h').symm

end DBFacts

/-! ### The chain model -/

namespace Item

variable {W : Type}

/-- The digest of an absorb item. -/
def getAbsorb : Item k W → Option (Digest k)
  | write _ => none
  | absorb d => some d

theorem eq_absorb_of_getAbsorb {it : Item k W} {d : Digest k} (h : it.getAbsorb = some d) :
    it = absorb d := by
  cases it <;> simp_all [getAbsorb]

end Item

/-- The challenge index of a verifier round `r`. -/
def _root_.GordieHowe.IOP.ProtocolSpec.chIdx {n : ℕ} (P : ProtocolSpec n) (r : Fin n) (hd : ¬ P.dir r = .P_to_V) :
    P.ChallengeIdx :=
  ⟨r, by cases h : P.dir r <;> simp_all⟩

/-- **A salted statement**: the proof's Fiat–Shamir salt and the statement, written at the start
of every `transcript` input (strong Fiat–Shamir). -/
@[ext]
structure SaltedStatement (kS : ℕ) (X : Type) where
  /-- The Fiat–Shamir salt. -/
  salt : FiatShamirSalt kS
  /-- The statement. -/
  stmt : X
deriving DecidableEq

/-- **An entry of a list at index `r` lies in its first `r + 1` entries.** -/
theorem mem_take_succ_of_getElem? {α : Type*} {l : List α} {r : ℕ} {a : α}
    (h : l[r]? = some a) : a ∈ l.take (r + 1) :=
  List.mem_of_getElem? (by rw [List.getElem?_take_of_lt (Nat.lt_succ_self r)]; exact h)

/-! ### Chain queries, digest collisions and claims -/

/-- **The chain queries**: the `transcript` and `xof` queries, the domain of the honest prover's
strategy. -/
def IsChainQuery : Query k kN kS L → Prop
  | .transcript _ => True
  | .xof _ _ => True
  | _ => False

/-- The probability that two fixed coordinates of a uniform answer vector have the same digest:
`1 / 2^(8k)`. -/
theorem prob_digest_eq_le {m : ℕ} {j j' : Fin m} (hjj : j ≠ j') :
    Pr[a ← (Fin m → Out k e) : (a j).digest = (a j').digest] ≤ 1 / 2 ^ (8 * k) := by
  classical
  let φ : Fin 2 ↪ Fin m := ⟨![j, j'], by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Eq.comm]⟩
  have h1 : Pr[a ← (Fin m → Out k e) : (a j).digest = (a j').digest] =
      Pr[g ← (Fin 2 → Out k e) : (g 0).digest = (g 1).digest] :=
    probUniform_comp_embedding (Y := Out k e) φ fun g => (g 0).digest = (g 1).digest
  rw [h1, ← QROM.probUniform_equiv (piFinTwoEquiv fun _ => Out k e).symm
    (fun g => (g 0).digest = (g 1).digest)]
  refine probUniform_prod_le (fun p : Out k e × Out k e => _) fun z => ?_
  have := Out.probUniform_digest_mem (k := k) (e := e) {z.digest}
  simp only [Finset.mem_singleton, Finset.card_singleton, Nat.cast_one] at this
  simpa [piFinTwoEquiv] using this.le

/-- **A claim**: a statement and a proof of it, the output of an adversary against the compiled
verifier. -/
structure Claim (Stmt Proof : Type) where
  /-- The statement. -/
  stmt : Stmt
  /-- The proof. -/
  proof : Proof

/-! ### The default answer and the key-collision term -/

/-- The default answer, read where an answer is missing. -/
def defaultOut : Out k e := ⟨fun _ => 0, fun _ => 0⟩

/-- **The key-collision term** `(n choose 2) / 2^(8k)`: a bound on the probability that two of
the `n` rounds of the honest prover derive the same key (`GordieHowe.SPBCS.prob_lazyKey_not_injective_le`); the streams of
the two rounds are then equal. -/
noncomputable def keyCollision (n k : ℕ) : ℝ≥0∞ := (n.choose 2 : ℝ≥0∞) / 2 ^ (8 * k)

/-- **The key-collision term is finite.** -/
theorem keyCollision_ne_top (n k : ℕ) : keyCollision n k ≠ ⊤ :=
  ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)

/-- **The key-collision term grows with the rounds**: at most `n'` rounds give at most
`C(n', 2) / 2^(8k)`. -/
theorem keyCollision_mono {n n' : ℕ} (hn : n ≤ n') (k : ℕ) : keyCollision n k ≤ keyCollision n' k := by
  unfold keyCollision
  exact ENNReal.div_le_div_right (by exact_mod_cast Nat.choose_le_choose 2 hn) _

end GordieHowe.SPBCS
