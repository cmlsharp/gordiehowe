-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.ClaimReduction
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.ProofSystem.Ligero.SubfieldTest

@[expose] public section

/-!
# The packed H circuit

With the packed witness, the H circuit's Longfellow proof is a GKR reduction followed by Ligero with
a subfield check. This file holds the Ligero phase with its column-query round exposed (`IOP.LigeroQuery`) and the
subfield checks on the packed rows (`HashCircuit.Packed.SubfieldCheck`,
`HashCircuit.Packed.JointSubfieldCheck`).
-/

namespace GordieHowe
open IOP

open scoped NNReal
open PackedClaim

variable {F : Type} [Field F] {a b nY : ℕ}

/-! ### Ligero with the subfield check -/

open scoped NNReal
open Polynomial

variable {Ctx : Type}

/-- A Ligero proof phase with its column-query round exposed: the challenge of round
`q` is a sample of `t` distinct columns out of `N`. CHVY25 Theorem 4.3 supplies
code proximity/query agreement, and Theorem 4.4 supplies linear and quadratic
constraint satisfaction conditional on the good-codeword event. Their per-prefix
round-by-round assembly is in section 4's proof of Theorem 4.1 (pp. 14–15).
Remark 1 permits equations chosen after commitment, with the decoded witness
fixed by that commitment and the equations fixed before the test challenge. -/
structure IOP.LigeroQuery (Ctx : Type) (t N : ℕ) where
  /-- The number of rounds. -/
  n : ℕ
  /-- The proof phase. -/
  spec : ProtocolSpec n
  [fintype : ∀ i, Fintype (spec.Challenge i)]
  [nonempty : ∀ i, Nonempty (spec.Challenge i)]
  /-- The round errors. -/
  ε : spec.ChallengeIdx → ℝ≥0
  /-- Round-by-round soundness of the exact constraints: the interface to CHVY25
  section 4's proof of Theorem 4.1, using Theorems 4.3 and 4.4 as ingredients.
  Those two ingredient theorems alone are not a per-prefix `ClaimProof`. -/
  proof : ClaimProof spec Ctx ε
  /-- The column-query round. -/
  q : spec.ChallengeIdx
  /-- Its challenge is a sample of distinct columns. -/
  query : spec.Challenge q ≃ (Fin t ↪ Fin N)

attribute [instance] LigeroQuery.fintype LigeroQuery.nonempty

variable {t N : ℕ}

/-- The columns queried, read from a transcript past the query round. -/
def IOP.LigeroQuery.queryOf (L : LigeroQuery Ctx t N) {m : Fin (L.n + 1)} (tr : L.spec.Transcript m)
    (h : (L.q.1 : ℕ) < m) : Fin t ↪ Fin N :=
  L.query (tr ⟨L.q.1, h⟩)

/-- The columns read from a transcript extended by round `m`'s message are the columns read
from the transcript before, when the query round comes earlier than `m`. -/
theorem IOP.LigeroQuery.queryOf_concat_of_lt (L : LigeroQuery Ctx t N) {m : Fin L.n}
    (tr : L.spec.Transcript m.castSucc) (msg : L.spec.Type m) (h : (L.q.1 : ℕ) < (m : ℕ))
    (h' : (L.q.1 : ℕ) < (m.succ : ℕ)) :
    L.queryOf (L.spec.concat tr msg) h' = L.queryOf tr h := by
  unfold LigeroQuery.queryOf
  congr 1
  exact ProtocolSpec.concat_apply_of_lt tr msg L.q.1 h

open Classical in
/-- A row `u` is within distance `e` of the evaluations of `f` on the domain `D`. -/
def IOP.Close (D : Fin N → F) (e : ℕ) (u : Fin N → F) (f : F[X]) : Prop :=
  (Finset.univ.filter fun j => u j ≠ f.eval (D j)).card ≤ e

/-- The data of the subfield check: the packed rows' committed entries, the subfield,
the domain, and the decoder's property that a packed value outside `E` comes from a row
close to a polynomial of degree `< k` with a coefficient outside `E`. For a far row the
decoder returns a default whose packed values lie in `E`. -/
structure HashCircuit.Packed.SubfieldCheck (Ctx : Type) (N R : ℕ) (pE : Ctx → Prop) where
  E : Subfield F
  /-- Membership in the subfield is decidable (for `fixedField`, the Frobenius test). -/
  [decMem : DecidablePred (· ∈ E)]
  D : Fin N → F
  D_injective : Function.Injective D
  D_mem : ∀ j, D j ∈ E
  /-- The packed rows' committed entries. -/
  rows : Ctx → Fin R → Fin N → F
  k : ℕ
  e : ℕ
  decode : ∀ c, ¬ pE c → ∃ r f, f.natDegree < k ∧ (∃ i, f.coeff i ∉ E) ∧ Close D e (rows c r) f

attribute [instance] HashCircuit.Packed.SubfieldCheck.decMem

variable {R : ℕ} {pE : Ctx → Prop}

open Classical in
/-- Among the query round's challenges, at most `(e+k).descFactorial t / N.descFactorial t` of them keep every packed row's
opened entries in the subfield, when `c` fails the subfield check
(`Ligero.SubfieldTest.subfieldCheck_sound_exact`, transported along `L.query`). -/
theorem IOP.LigeroQuery.card_filter_queryE_le (L : LigeroQuery Ctx t N)
    (C : HashCircuit.Packed.SubfieldCheck (F := F) Ctx N R pE) {c : Ctx} (hnpE : ¬ pE c) :
    ((Finset.univ.filter fun ch : L.spec.Challenge L.q =>
        ∀ r s, C.rows c r (L.query ch s) ∈ C.E).card : ℝ≥0) ≤
      Ligero.SubfieldTest.queryError C.e C.k N t * Fintype.card (L.spec.Challenge L.q) := by
  have hcard_eq : Fintype.card (L.spec.Challenge L.q) = Fintype.card (Fin t ↪ Fin N) :=
    Fintype.card_congr L.query
  by_cases htN : t ≤ N
  · obtain ⟨r₀, f, hf, hbad, hclose⟩ := C.decode c hnpE
    have hsub : (Finset.univ.filter fun ch : L.spec.Challenge L.q =>
        ∀ r s, C.rows c r (L.query ch s) ∈ C.E) ⊆
        (Finset.univ.filter fun ch : L.spec.Challenge L.q =>
          ∀ s, C.rows c r₀ (L.query ch s) ∈ C.E) := by
      intro ch hch
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      exact fun s => hch r₀ s
    have hmap_eq : (Finset.univ.filter fun ch : L.spec.Challenge L.q =>
        ∀ s, C.rows c r₀ (L.query ch s) ∈ C.E).card =
        (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, C.rows c r₀ (q s) ∈ C.E).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr (L.query.subtypeEquiv fun _ => Iff.rfl)
    have hsound := Ligero.SubfieldTest.subfieldCheck_sound_exact C.E C.D_injective C.D_mem hf hbad hclose t
    have hsound' : (Finset.univ.filter fun q : Fin t ↪ Fin N => ∀ s, C.rows c r₀ (q s) ∈ C.E).card ≤
        (C.e + C.k).descFactorial t := by convert hsound
    have hnat := ((Finset.card_le_card hsub).trans_eq hmap_eq).trans hsound'
    have hpos : (0 : NNReal) < (N.descFactorial t : NNReal) := by
      exact_mod_cast Nat.descFactorial_pos.mpr htN
    rw [Ligero.SubfieldTest.queryError, hcard_eq, Fintype.card_embedding_eq,
      Fintype.card_fin, Fintype.card_fin, div_mul_cancel₀ _ (ne_of_gt hpos)]
    exact_mod_cast hnat
  · have hc0 : Fintype.card (L.spec.Challenge L.q) = 0 := by
      rw [hcard_eq, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
      exact Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge htN)
    have hle := (Finset.card_filter_le (Finset.univ : Finset (L.spec.Challenge L.q))
      (fun ch => ∀ r s, C.rows c r (L.query ch s) ∈ C.E)).trans_eq Finset.card_univ
    rw [hc0] at hle
    rw [Nat.le_zero.mp hle, Nat.cast_zero]
    exact zero_le

open Classical in
/-- **Ligero with the subfield check** proves the exact constraints and `pE`. The
verifier also checks that every opened entry of every packed row lies in `E`; the state
adds `pE`, or after the query round, that check. The query round's error grows by
`(e+k).descFactorial t / N.descFactorial t` (`Ligero.SubfieldTest.subfieldCheck_sound_exact`); the others are unchanged. -/
def IOP.LigeroQuery.withSubfield (L : LigeroQuery Ctx t N)
    (C : HashCircuit.Packed.SubfieldCheck (F := F) Ctx N R pE) :
    ClaimProof L.spec Ctx
      (fun i => L.ε i + if i = L.q then Ligero.SubfieldTest.queryError C.e C.k N t else 0) where
  claim c := L.proof.claim c ∧ pE c
  V c tr := L.proof.V c tr && decide (∀ r s, C.rows c r (L.queryOf tr (by simp) s) ∈ C.E)
  S m c tr := L.proof.S m c tr ∧
    (pE c ∨ ∃ h : (L.q.1 : ℕ) < m, ∀ r s, C.rows c r (L.queryOf tr h s) ∈ C.E)
  start c tr hc h := by
    obtain ⟨h1, h2⟩ := h
    have hpE : pE c := h2.resolve_right (fun ⟨hlt, _⟩ => by simp at hlt)
    exact hc ⟨L.proof.claim_of_S h1, hpE⟩
  next m hdir c tr msg hnot h := by
    obtain ⟨h1, h2⟩ := h
    have hqm : (L.q.1 : ℕ) ≠ (m : ℕ) := by
      intro heq
      have hEq : L.q.1 = m := Fin.ext heq
      have hcontra := L.q.2
      rw [hEq, hdir] at hcontra
      exact absurd hcontra (by decide)
    have hS1 : L.proof.S m.castSucc c tr := by
      by_contra hcon
      exact L.proof.next m hdir c tr msg hcon h1
    refine hnot ⟨hS1, ?_⟩
    rcases h2 with hpE | ⟨h', hall⟩
    · exact Or.inl hpE
    · have hlt : (L.q.1 : ℕ) < (m : ℕ) := by
        have hle : (L.q.1 : ℕ) < (m : ℕ) + 1 := by simpa [Fin.val_succ] using h'
        omega
      refine Or.inr ⟨hlt, ?_⟩
      have heq := L.queryOf_concat_of_lt tr msg hlt h'
      intro r s
      rw [← heq]
      exact hall r s
  full c tr hV := by
    rw [Bool.and_eq_true, decide_eq_true_eq] at hV
    exact ⟨L.proof.full c tr hV.1, Or.inr ⟨by simp, hV.2⟩⟩
  rbr c i tr := by
    by_cases hi : i = L.q
    · subst hi
      rw [if_pos rfl, add_mul]
      by_cases hbc : L.proof.S L.q.1.castSucc c tr
      · by_cases hpEc : pE c
        · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
              (t := (∅ : Finset (L.spec.Challenge L.q))) ?_)) (by simp)
          intro ch hch
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch
          exact (hch.1 ⟨hbc, Or.inl hpEc⟩).elim
        · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
              (t := Finset.univ.filter fun ch : L.spec.Challenge L.q =>
                ∀ r s, C.rows c r (L.query ch s) ∈ C.E) ?_))
              (le_trans (L.card_filter_queryE_le C hpEc) (CanonicallyOrderedAdd.le_add_self _ _))
          intro ch hch
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
          rcases hch.2.2 with hpE | ⟨h, hall⟩
          · exact absurd hpE hpEc
          · have heq : L.queryOf (L.spec.concat tr ch) h = L.query ch := by
              unfold LigeroQuery.queryOf
              congr 1
              exact ProtocolSpec.concat_apply_last tr ch
            rwa [heq] at hall
      · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
            (t := Finset.univ.filter fun ch : L.spec.Challenge L.q =>
              ¬ L.proof.S L.q.1.castSucc c tr ∧ L.proof.S L.q.1.succ c (L.spec.concat tr ch)) ?_))
            (le_trans (L.proof.rbr c L.q tr) le_self_add)
        intro ch hch
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
        exact ⟨hbc, hch.2.1⟩
    · have hzero : (if i = L.q then Ligero.SubfieldTest.queryError C.e C.k N t else 0) = 0 := if_neg hi
      rw [hzero, add_zero]
      have hqi : (L.q.1 : ℕ) ≠ (i.1 : ℕ) := by
        intro heq
        exact hi (Subtype.ext (Fin.ext heq)).symm
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
          (t := Finset.univ.filter fun ch : L.spec.Challenge i =>
            ¬ L.proof.S i.1.castSucc c tr ∧ L.proof.S i.1.succ c (L.spec.concat tr ch)) ?_))
          (L.proof.rbr c i tr)
      intro ch hch
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      have hB_before : pE c ∨ ∃ h : (L.q.1 : ℕ) < (i.1.castSucc : ℕ),
          ∀ r s, C.rows c r (L.queryOf tr h s) ∈ C.E := by
        rcases hch.2.2 with hpE | ⟨h', hall⟩
        · exact Or.inl hpE
        · have hle : (L.q.1 : ℕ) < (i.1 : ℕ) + 1 := by simpa [Fin.val_succ] using h'
          have hlt : (L.q.1 : ℕ) < (i.1 : ℕ) := by omega
          refine Or.inr ⟨hlt, ?_⟩
          have heq := L.queryOf_concat_of_lt tr ch hlt h'
          intro r s
          rw [← heq]
          exact hall r s
      exact ⟨fun hA => hch.1 ⟨hA, hB_before⟩, hch.2.1⟩

/-! ### The subfield check charged jointly with the low-degree test -/

/-- **The data of the subfield check charged jointly with the low-degree test**:
as `SubfieldCheck`, but when `pE c` fails some packed row agrees,
on a column set `agree c` fixed by the context (the agreement set of the low-degree test), with a
polynomial of degree `< k` with a coefficient outside `E`
(`Ligero.SubfieldTest.AgreesWithNonSubfield`). -/
structure HashCircuit.Packed.JointSubfieldCheck (Ctx : Type) (N R : ℕ) (pE : Ctx → Prop) where
  E : Subfield F
  /-- Membership in the subfield is decidable (for `fixedField`, the Frobenius test). -/
  [decMem : DecidablePred (· ∈ E)]
  D : Fin N → F
  D_injective : Function.Injective D
  D_mem : ∀ j, D j ∈ E
  /-- The packed rows' committed entries. -/
  rows : Ctx → Fin R → Fin N → F
  k : ℕ
  /-- The columns on which the rows are pinned. -/
  agree : Ctx → Finset (Fin N)
  decode : ∀ c, ¬ pE c → ∃ r f, Ligero.SubfieldTest.AgreesWithNonSubfield E D k (agree c) (rows c r) f

attribute [instance] HashCircuit.Packed.JointSubfieldCheck.decMem

/-- **Accepted queries lie in `S c`**: whenever the verifier of the Ligero proof phase accepts,
every queried column lies in the column set `S c`, a function of the context. -/
def IOP.LigeroQuery.AcceptsWithin (L : LigeroQuery Ctx t N) (S : Ctx → Finset (Fin N)) :
    Prop :=
  ∀ c tr, L.proof.V c tr = true → ∀ s, L.queryOf tr (by simp) s ∈ S c

open Classical in
/-- Among the query round's challenges, at most `(k - 1).descFactorial t / N.descFactorial t` of
them query only columns of `agree c` and keep every packed row's opened entries in the subfield,
when `c` fails the subfield check (`Ligero.SubfieldTest.card_filter_mem_le_of_agrees`, transported
along `L.query`). -/
theorem IOP.LigeroQuery.card_filter_queryJoint_le (L : LigeroQuery Ctx t N)
    (C : HashCircuit.Packed.JointSubfieldCheck (F := F) Ctx N R pE) {c : Ctx} (hnpE : ¬ pE c) :
    ((Finset.univ.filter fun ch : L.spec.Challenge L.q =>
        ∀ s, L.query ch s ∈ C.agree c ∧ ∀ r, C.rows c r (L.query ch s) ∈ C.E).card : ℝ≥0) ≤
      Ligero.SubfieldTest.jointSubfieldError C.k N t * Fintype.card (L.spec.Challenge L.q) := by
  have hcard_eq : Fintype.card (L.spec.Challenge L.q) = Fintype.card (Fin t ↪ Fin N) :=
    Fintype.card_congr L.query
  by_cases htN : t ≤ N
  · obtain ⟨r₀, f, hf⟩ := C.decode c hnpE
    have hsub : (Finset.univ.filter fun ch : L.spec.Challenge L.q =>
        ∀ s, L.query ch s ∈ C.agree c ∧ ∀ r, C.rows c r (L.query ch s) ∈ C.E) ⊆
        (Finset.univ.filter fun ch : L.spec.Challenge L.q =>
          ∀ s, L.query ch s ∈ C.agree c ∧ C.rows c r₀ (L.query ch s) ∈ C.E) := by
      intro ch hch
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      exact fun s => ⟨(hch s).1, (hch s).2 r₀⟩
    have hmap_eq : (Finset.univ.filter fun ch : L.spec.Challenge L.q =>
        ∀ s, L.query ch s ∈ C.agree c ∧ C.rows c r₀ (L.query ch s) ∈ C.E).card =
        (Finset.univ.filter fun q : Fin t ↪ Fin N =>
          ∀ s, q s ∈ C.agree c ∧ C.rows c r₀ (q s) ∈ C.E).card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr (L.query.subtypeEquiv fun _ => Iff.rfl)
    have hsound : (Finset.univ.filter fun q : Fin t ↪ Fin N =>
        ∀ s, q s ∈ C.agree c ∧ C.rows c r₀ (q s) ∈ C.E).card ≤ (C.k - 1).descFactorial t := by
      convert Ligero.SubfieldTest.card_filter_mem_le_of_agrees C.E C.D_injective C.D_mem hf t
    have hnat := ((Finset.card_le_card hsub).trans_eq hmap_eq).trans hsound
    have hpos : (0 : NNReal) < (N.descFactorial t : NNReal) := by
      exact_mod_cast Nat.descFactorial_pos.mpr htN
    rw [Ligero.SubfieldTest.jointSubfieldError, hcard_eq, Fintype.card_embedding_eq,
      Fintype.card_fin, Fintype.card_fin, div_mul_cancel₀ _ (ne_of_gt hpos)]
    exact_mod_cast hnat
  · have hc0 : Fintype.card (L.spec.Challenge L.q) = 0 := by
      rw [hcard_eq, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
      exact Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge htN)
    rw [hc0, Nat.cast_zero, mul_zero, nonpos_iff_eq_zero, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    exact fun ch _ => absurd (Fintype.card_pos (α := L.spec.Challenge L.q)
      (h := ⟨ch⟩)) (by omega)

open Classical in
/-- **Ligero with the subfield check charged jointly with the low-degree test** (a packing mask row
with a coefficient outside `E`): proves the exact constraints and `pE`, when accepted queries lie in
the column sets `C.agree` (`AcceptsWithin`). The verifier also checks that every opened entry of
every packed row lies in `E`; the state adds `pE`, or after the query round, that the queried
columns lie in `C.agree c` and pass that check. The query round's error grows by
`(k - 1).descFactorial t / N.descFactorial t` (`card_filter_queryJoint_le`); the others are
unchanged. -/
def IOP.LigeroQuery.withJointSubfield (L : LigeroQuery Ctx t N)
    (C : HashCircuit.Packed.JointSubfieldCheck (F := F) Ctx N R pE)
    (hagree : L.AcceptsWithin C.agree) :
    ClaimProof L.spec Ctx
      (fun i => L.ε i + if i = L.q then Ligero.SubfieldTest.jointSubfieldError C.k N t else 0) where
  claim c := L.proof.claim c ∧ pE c
  V c tr := L.proof.V c tr && decide (∀ r s, C.rows c r (L.queryOf tr (by simp) s) ∈ C.E)
  S m c tr := L.proof.S m c tr ∧
    (pE c ∨ ∃ h : (L.q.1 : ℕ) < m,
      ∀ s, L.queryOf tr h s ∈ C.agree c ∧ ∀ r, C.rows c r (L.queryOf tr h s) ∈ C.E)
  start c tr hc h := by
    obtain ⟨h1, h2⟩ := h
    have hpE : pE c := h2.resolve_right (fun ⟨hlt, _⟩ => by simp at hlt)
    exact hc ⟨L.proof.claim_of_S h1, hpE⟩
  next m hdir c tr msg hnot h := by
    obtain ⟨h1, h2⟩ := h
    have hS1 : L.proof.S m.castSucc c tr := by
      by_contra hcon
      exact L.proof.next m hdir c tr msg hcon h1
    refine hnot ⟨hS1, ?_⟩
    rcases h2 with hpE | ⟨h', hall⟩
    · exact Or.inl hpE
    · have hqm : (L.q.1 : ℕ) ≠ (m : ℕ) := by
        intro heq
        have hEq : L.q.1 = m := Fin.ext heq
        have hcontra := L.q.2
        rw [hEq, hdir] at hcontra
        exact absurd hcontra (by decide)
      have hlt : (L.q.1 : ℕ) < (m : ℕ) := by
        have hle : (L.q.1 : ℕ) < (m : ℕ) + 1 := by simpa [Fin.val_succ] using h'
        omega
      refine Or.inr ⟨hlt, ?_⟩
      have heq := L.queryOf_concat_of_lt tr msg hlt h'
      rw [← heq]
      exact hall
  full c tr hV := by
    rw [Bool.and_eq_true, decide_eq_true_eq] at hV
    exact ⟨L.proof.full c tr hV.1,
      Or.inr ⟨by simp, fun s => ⟨hagree c tr hV.1 s, fun r => hV.2 r s⟩⟩⟩
  rbr c i tr := by
    by_cases hi : i = L.q
    · subst hi
      rw [ite_eq_left rfl, add_mul]
      by_cases hbc : L.proof.S L.q.1.castSucc c tr
      · by_cases hpEc : pE c
        · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
              (t := (∅ : Finset (L.spec.Challenge L.q))) ?_)) (by simp)
          intro ch hch
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch
          exact (hch.1 ⟨hbc, Or.inl hpEc⟩).elim
        · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
              (t := Finset.univ.filter fun ch : L.spec.Challenge L.q =>
                ∀ s, L.query ch s ∈ C.agree c ∧ ∀ r, C.rows c r (L.query ch s) ∈ C.E) ?_))
              (le_trans (L.card_filter_queryJoint_le C hpEc)
                (CanonicallyOrderedAdd.le_add_self _ _))
          intro ch hch
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
          rcases hch.2.2 with hpE | ⟨h, hall⟩
          · exact absurd hpE hpEc
          · have heq : L.queryOf (L.spec.concat tr ch) h = L.query ch := by
              unfold LigeroQuery.queryOf
              congr 1
              exact ProtocolSpec.concat_apply_last tr ch
            rwa [heq] at hall
      · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
            (t := Finset.univ.filter fun ch : L.spec.Challenge L.q =>
              ¬ L.proof.S L.q.1.castSucc c tr ∧ L.proof.S L.q.1.succ c (L.spec.concat tr ch)) ?_))
            (le_trans (L.proof.rbr c L.q tr) le_self_add)
        intro ch hch
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
        exact ⟨hbc, hch.2.1⟩
    · rw [ite_eq_right hi, add_zero]
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
          (t := Finset.univ.filter fun ch : L.spec.Challenge i =>
            ¬ L.proof.S i.1.castSucc c tr ∧ L.proof.S i.1.succ c (L.spec.concat tr ch)) ?_))
          (L.proof.rbr c i tr)
      intro ch hch
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      have hB_before : pE c ∨ ∃ h : (L.q.1 : ℕ) < (i.1.castSucc : ℕ),
          ∀ s, L.queryOf tr h s ∈ C.agree c ∧ ∀ r, C.rows c r (L.queryOf tr h s) ∈ C.E := by
        rcases hch.2.2 with hpE | ⟨h', hall⟩
        · exact Or.inl hpE
        · have hle : (L.q.1 : ℕ) < (i.1 : ℕ) + 1 := by simpa [Fin.val_succ] using h'
          have hqi : (L.q.1 : ℕ) ≠ (i.1 : ℕ) := fun heq => hi (Subtype.ext (Fin.ext heq)).symm
          have hlt : (L.q.1 : ℕ) < (i.1 : ℕ) := by omega
          refine Or.inr ⟨hlt, ?_⟩
          have heq := L.queryOf_concat_of_lt tr ch hlt h'
          rw [← heq]
          exact hall
      exact ⟨fun hA => hch.1 ⟨hA, hB_before⟩, hch.2.1⟩

end GordieHowe
