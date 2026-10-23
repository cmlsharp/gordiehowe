-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Cover
public import GordieHowe.SPBCS.Stability
public import GordieHowe.SPBCS.FullPast.Targeted
public import GordieHowe.Foundations.ToMathlib.FinsetSingleton

@[expose] public section

/-!
# The targeted extractor of the spBCS compiler

The targeted extractor of the compiler over the term (`GordieHowe.SPBCS.Base.targetedExtract`,
`GordieHowe/SPBCS/FullPast/Targeted.lean`) at the challenges with merges (`chV`): the composite transcript
along the proof, with the messages read from the Merkle views of the database at the roots of the
proof's writes. The argument reads the database through the translation with merges (`GordieHowe.SPBCS.trans`).

- `preimage_trans`, `children_trans`, `opening_trans`, `view_trans`: without a digest collision,
  the translated database (`trans`) has the Merkle views of the database itself (a Merkle query
  translates to itself, any other query to a query of the same kind).
- `mem_of_verify_targeted`: CMS19 Proposition 8.12 along one accepted spBCS proof with the
  targeted extractor: a database recording the spBCS verifier's queries with the answers of
  `h` has a digest collision, lies in `bad`, or the targeted extractor at the challenges with
  merges returns a witness (`mem_of_verify_targeted` for the compiler over the term on the
  translated database, `accepts_transOracle`, `chV_transOracle`, `view_trans`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable {M : SPBCS Mg P X k kN kS L e}

/-! ### The translated database has the database's Merkle views -/

section Views

variable {D : ODB k kN kS L e}

/-- A recorded query of the translated database with answer digest `u` is the translation of a
recorded query of `D` with answer digest `u`. -/
theorem exists_mem_preimages_of_mem_trans (hD : D ∉ digestCollision) {u : Digest k}
    {q : Query k kN kS L} (hq : q ∈ preimages (M.trans D) u) :
    ∃ q₀ ∈ preimages D u, M.φ D q₀ = some q := by
  obtain ⟨hmem, hdig⟩ := mem_preimages.1 hq
  obtain ⟨q₀, hq₀, hφ⟩ := (DB.mem_image_iff (injOnKeys_φ hD)).1 hmem
  obtain ⟨y, hy⟩ := DB.mem_iff_lookup.1 hq₀
  refine ⟨q₀, mem_preimages.2 ⟨hq₀, ?_⟩, hφ⟩
  rw [trans_lookup_of hD hy hφ] at hdig
  rw [hy]
  exact hdig

/-- The translation of a recorded query of `D` with answer digest `u` is a recorded query of the
translated database with answer digest `u`. -/
theorem mem_preimages_trans (hD : D ∉ digestCollision) {u : Digest k} {q₀ q : Query k kN kS L}
    (hq₀ : q₀ ∈ preimages D u) (hφ : M.φ D q₀ = some q) : q ∈ preimages (M.trans D) u := by
  obtain ⟨hmem, hdig⟩ := mem_preimages.1 hq₀
  obtain ⟨y, hy⟩ := DB.mem_iff_lookup.1 hmem
  have hl := trans_lookup_of hD hy hφ
  refine mem_preimages.2 ⟨DB.mem_iff_lookup.2 ⟨y, hl⟩, ?_⟩
  rw [hl]
  rw [hy] at hdig
  exact hdig

/-- **The unique preimage in the translated database is the translation of the unique preimage
in `D`**, without a digest collision. -/
theorem preimage_trans (hD : D ∉ digestCollision) (u : Digest k) :
    preimage (M.trans D) u = (preimage D u).bind (M.φ D) := by
  rcases hpre : preimage D u with _ | q₀
  · -- no preimage in `D`: the preimage set is empty, and so is the translated one
    have hempty : preimages D u = ∅ := by
      by_contra hne
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hs : preimages D u = {a} :=
        Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb =>
          Finset.card_le_one.1 (card_preimages_le_one hD u) b hb a ha⟩
      rw [preimage_eq_some_iff.2 hs] at hpre
      cases hpre
    have hempty' : preimages (M.trans D) u = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.2 fun q hq => ?_
      obtain ⟨q₀, hq₀, -⟩ := exists_mem_preimages_of_mem_trans hD hq
      rw [hempty] at hq₀
      exact Finset.notMem_empty _ hq₀
    rw [Option.bind_none]
    rcases h : preimage (M.trans D) u with _ | q
    · rfl
    · have := preimage_eq_some_iff.1 h
      rw [hempty'] at this
      exact absurd this (Finset.empty_ne_singleton q)
  · have hs := preimage_eq_some_iff.1 hpre
    have huniq : ∀ q ∈ preimages (M.trans D) u, M.φ D q₀ = some q := fun q hq => by
      obtain ⟨q₁, hq₁, hφ⟩ := exists_mem_preimages_of_mem_trans hD hq
      rw [hs, Finset.mem_singleton] at hq₁
      rw [← hq₁]
      exact hφ
    rw [Option.bind_some]
    rcases hφ : M.φ D q₀ with _ | q
    · rcases h : preimage (M.trans D) u with _ | q'
      · rfl
      · have hq' := mem_of_preimage_eq_some h
        have hmem : q' ∈ preimages (M.trans D) u := by
          rw [preimage_eq_some_iff.1 h]
          exact Finset.mem_singleton_self q'
        rw [huniq q' hmem] at hφ
        cases hφ
    · have hq : q ∈ preimages (M.trans D) u :=
        mem_preimages_trans hD (by rw [hs]; exact Finset.mem_singleton_self q₀) hφ
      refine preimage_eq_some_iff.2 (Finset.eq_singleton_iff_unique_mem.2 ⟨hq, fun q' hq' => ?_⟩)
      have := huniq q' hq'
      rw [hφ] at this
      exact (Option.some_inj.1 this).symm

/-- The translation keeps the children of a query: a Merkle node translates to itself, and a
chain input to a chain input. -/
theorem children_bind_φ (q₀ : Query k kN kS L) : (M.φ D q₀).bind Query.children = q₀.children := by
  by_cases ht : ∃ b, q₀ = .transcript b
  · obtain ⟨b, rfl⟩ := ht
    rcases h : M.φ D (.transcript b) with _ | q
    · rfl
    · obtain ⟨c, ss, ch, -, -, rfl⟩ := φ_transcript_eq_some h
      rfl
  · push Not at ht
    rw [φ_of_not_transcript ht, Option.bind_some]

/-- The translation keeps the opening of a query: a Merkle leaf translates to itself, and a chain
input to a chain input. -/
theorem opening_bind_φ (q₀ : Query k kN kS L) : (M.φ D q₀).bind Query.opening = q₀.opening := by
  by_cases ht : ∃ b, q₀ = .transcript b
  · obtain ⟨b, rfl⟩ := ht
    rcases h : M.φ D (.transcript b) with _ | q
    · rfl
    · obtain ⟨c, ss, ch, -, -, rfl⟩ := φ_transcript_eq_some h
      rfl
  · push Not at ht
    rw [φ_of_not_transcript ht, Option.bind_some]

theorem children_trans (hD : D ∉ digestCollision) (u : Digest k) :
    children (M.trans D) u = children D u := by
  rw [children, children, preimage_trans hD, Option.bind_assoc]
  exact congrArg _ (funext children_bind_φ)

theorem opening_trans (hD : D ∉ digestCollision) (u : Digest k) :
    Merkle.opening (M.trans D) u = Merkle.opening D u := by
  rw [Merkle.opening, Merkle.opening, preimage_trans hD, Option.bind_assoc]
  exact congrArg _ (funext opening_bind_φ)

theorem label_trans (hD : D ∉ digestCollision) {m : ℕ} {rt : Digest k} :
    ∀ p, label (M.trans D) m rt p = label D m rt p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p with
    | 0 => simp [label_zero]
    | 1 => simp [label_one]
    | p + 2 =>
      rw [label_succ_succ, label_succ_succ, ih _ (by omega)]
      simp only [children_trans hD]

/-- **Without a digest collision, the translated database has the Merkle views of `D`.** -/
theorem view_trans (hD : D ∉ digestCollision) (m : ℕ) (rt : Digest k) :
    view (M.trans D) m rt = view D m rt := by
  refine MerkleView.ext (funext (label_trans hD)) (funext fun j => ?_)
  simp only [view, leafAt, label_trans hD, opening_trans hD]

end Views

/-! ### Proposition 8.12 along the proof -/

section Prop812

variable [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} {Wit : Type}
  (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (St : CausalStateFn P t X)
  {ε : ChIdx P t → NNReal}

/-- **CMS19 Proposition 8.12 along one accepted spBCS proof, with the targeted extractor**:
a database that records the spBCS verifier's queries on an accepted proof `π` of `x` with
the answers of `h` has a digest collision, lies in `bad`, or the targeted extractor at the
challenges with merges returns a witness for `x`. -/
theorem mem_of_verify_targeted [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E St ε)
    {h : Query k kN kS L → Out k e} {x : X} {π : M.NIProof} {Q : M.IOPQueries V x}
    {D : ODB k kN kS L e} (hv : M.Accepts h x π Q) (hrec : RecordsQueries D h x π Q) :
    (∃ w ∈ M.targetedExtract D π (M.chV h (M.ssOf x π) π.writes) E x, (x, w) ∈ rel) ∨
      D ∈ M.bad rel E St ∪ digestCollision := by
  by_cases hD : D ∈ digestCollision
  · exact Or.inr (Or.inr hD)
  rcases M.toFullPast.mem_of_verifyFullPast_targeted rel E St hrbr (M.transOracle D h) x π Q
      (accepts_transOracle hD hrec hv) (mem_trans_of_queries hD hrec) with hE | hbad | hcol
  · obtain ⟨w, hw, hrel⟩ := hE
    refine Or.inl ⟨w, ?_, hrel⟩
    rw [chV_transOracle hD hrec] at hw
    unfold Base.targetedExtract at hw ⊢
    rw [M.trT_congr _ fun q i => funext fun τ => view_trans hD _ _] at hw
    exact hw
  · exact Or.inr (Or.inl hbad)
  · exact absurd hcol (trans_notMem_digestCollision hD)

end Prop812

end

end GordieHowe.SPBCS
