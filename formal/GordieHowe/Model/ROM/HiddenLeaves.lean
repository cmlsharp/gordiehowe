-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.ProgEnv

@[expose] public section

/-!
# Hidden leaf digests against query-bounded classical adversaries

A generic identical-until-bad argument for the leaf digests of a Merkle commitment whose leaves
carry fresh salts, against classical adversaries all of whose queries are counted
(`IAlg.PostOracleFree`).

**The setting.** The oracle is `H : X → Y`; `nsalt x` is the salt in the leaf-salt slot of the input
`x` (`none` for an input without one). A **leaf kernel** (`LeafKernel`) computes a reply from a
proof query, the oracle in force, further coins `m`, a salt per position `ν : Pos → N` and a value per
position `d : Pos → Y`; the positions are split into hidden ones (`hidden req m p`) and the others.
Its two kernels are

- `kL` (honest digests): `d p` is the oracle at the leaf input `point req m p (ν p)`, whose salt is
  `ν p`;
- `kD` (uniform digests): `d` is drawn uniformly with the other coins.

The laws (`LeafKernel.Laws`): the reply reads `d` only at hidden positions, reads `ν` only at the
other positions, reads the oracle only at salt-free inputs and at inputs carrying the salt of a
position that is not hidden, and programs only salt-free inputs.

**The theorem** (`abs_toReal_acceptProb_progEnv_kL_sub_kD_le`): against every classical adversary
with a budget of `t` queries whose output does not read the final oracle, the games of `kL` and
`kD` with `Q` proof queries differ by at most

    Q · (4 t |Pos| + 4 Q |Pos|²) / |N|.

**The argument**, per proof query `j` of the hybrid (`kD` below `j`, `kL` from `j` on), from `j` to
`j + 1`, with `ν` the salts of proof query `j` and `T` the inputs carrying one of them:

1. (relabel, exact) The initial oracle is `H` with the inputs of `T` answered by a fresh `G`.
2. (identical until bad) Unless a query of the run before proof query `j` lies in `T` (`PreHit`) or
   two salts of the tape coincide (`SaltBad`), the run from the relabelled oracle and the run from
   `H` in which proof query `j` replaces `T` by `G` (`run_coupling`) have the same replies, in both
   hybrids.
3. (swap, exact) In the second run proof query `j` reads its hidden digests from `G` at the hidden
   points; swapping those values of `G` with the drawn digests `d` (`expect_fill`) turns `kL`'s
   reply into `kD`'s reply on an oracle that differs from `kD`'s at the hidden points only.
4. (identical until bad) The two runs agree unless a query after proof query `j` hits a hidden point,
   an event contained in `Hit` (some query of the run carries the salt of a hidden position), whose
   probability is computed in hybrid `j + 1`, where proof query `j`'s reply does not read the hidden
   salts.

Each of `PreHit` and `Hit` has probability at most `t |Pos| / |N|` (a query carries a given uniform
salt with probability `1 / |N|`), and `SaltBad` at most `Q |Pos|² / |N|`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type}

/-! ### Coins with a salt and a value per position -/

/-- **The coins of a leaf kernel**: further coins, a salt per position and a value per position (the
digest source of a hidden position). -/
@[ext]
structure LeafCoins (Cm Pos N Y : Type) where
  /-- The further coins. -/
  main : Cm
  /-- The salt of each position. -/
  salts : Pos → N
  /-- The value of each position. -/
  digests : Pos → Y

/-- Leaf coins as their three parts. -/
def LeafCoins.equivProd (Cm Pos N Y : Type) : LeafCoins Cm Pos N Y ≃ Cm × (Pos → N) × (Pos → Y) where
  toFun c := (c.main, c.salts, c.digests)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (Cm Pos N Y : Type) [Fintype Cm] [Fintype Pos] [DecidableEq Pos] [Fintype N]
    [Fintype Y] : Fintype (LeafCoins Cm Pos N Y) :=
  Fintype.ofEquiv _ (LeafCoins.equivProd Cm Pos N Y).symm

instance (Cm Pos N Y : Type) [Nonempty Cm] [Nonempty N] [Nonempty Y] :
    Nonempty (LeafCoins Cm Pos N Y) :=
  ⟨⟨Classical.arbitrary _, fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _⟩⟩

/-! ### Leaf kernels -/

/-- **A leaf kernel**: a reply from a proof query, the oracle in force, further coins, a salt per
position and a value per position; the hidden positions of a proof query at the further coins; and the
leaf input of a position with a given salt. -/
structure LeafKernel (X Y Stmt Wit Proof Cm Pos N : Type) where
  /-- The reply. -/
  run : ProofQuery Stmt Wit → (X → Y) → Cm → (Pos → N) → (Pos → Y) → NARG.SimOutput X Y Proof
  /-- The hidden positions. -/
  hidden : ProofQuery Stmt Wit → Cm → Pos → Bool
  /-- The leaf input of a position with a salt. -/
  point : ProofQuery Stmt Wit → Cm → Pos → N → X

namespace LeafKernel

variable {Cm Pos N : Type} (L : LeafKernel X Y Stmt Wit Proof Cm Pos N)

/-- **The kernel with uniform digests**: the drawn values are the values of the hidden
positions. -/
def kD : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y) :=
  fun req O c => L.run req O c.main c.salts c.digests

/-- **The kernel with honest digests**: the value of a position is the oracle at its leaf input. -/
def kL : Kernel X Y Stmt Wit Proof (LeafCoins Cm Pos N Y) :=
  fun req O c => L.run req O c.main c.salts fun p => O (L.point req c.main p (c.salts p))

/-- **The laws of a leaf kernel** for the salt slot `nsalt` and the public salts `pub` (salts of
fixed inputs that any reply may read, such as the default leaf of a padded tree). -/
structure Laws (nsalt : X → Option N) (pub : Finset N) : Prop where
  /-- The leaf input of a position carries its salt. -/
  point_salt : ∀ req m p a, nsalt (L.point req m p a) = some a
  /-- The reply reads the values only at hidden positions. -/
  run_digests : ∀ req O m ν d d', (∀ p, L.hidden req m p = true → d p = d' p) →
    L.run req O m ν d = L.run req O m ν d'
  /-- The reply reads the salts only at positions that are not hidden. -/
  run_salts : ∀ req O m ν ν' d, (∀ p, L.hidden req m p = false → ν p = ν' p) →
    L.run req O m ν d = L.run req O m ν' d
  /-- The reply reads the oracle only at salt-free inputs, at inputs carrying a public salt and at
  inputs carrying the salt of a position that is not hidden. -/
  run_oracle : ∀ req O O' m ν d,
    (∀ x, (nsalt x = none ∨ (∃ a ∈ pub, nsalt x = some a) ∨
      ∃ p, L.hidden req m p = false ∧ nsalt x = some (ν p)) → O x = O' x) →
    L.run req O m ν d = L.run req O' m ν d
  /-- The reply programs only salt-free inputs. -/
  assignment_salt : ∀ req O m ν d, ∀ a ∈ (L.run req O m ν d).assignments, nsalt a.input = none

/-- **A leaf kernel on proof queries read through `f`**: on `req` it is the leaf kernel on `f req`. -/
def comapReq {Stmt' Wit' : Type} (f : ProofQuery Stmt' Wit' → ProofQuery Stmt Wit) :
    LeafKernel X Y Stmt' Wit' Proof Cm Pos N where
  run req := L.run (f req)
  hidden req := L.hidden (f req)
  point req := L.point (f req)

/-- The laws of a leaf kernel hold for the leaf kernel on proof queries read through a map. -/
theorem Laws.comapReq {L : LeafKernel X Y Stmt Wit Proof Cm Pos N} {nsalt : X → Option N}
    {pub : Finset N} (h : L.Laws nsalt pub) {Stmt' Wit' : Type}
    (f : ProofQuery Stmt' Wit' → ProofQuery Stmt Wit) : (L.comapReq f).Laws nsalt pub where
  point_salt req := h.point_salt (f req)
  run_digests req := h.run_digests (f req)
  run_salts req := h.run_salts (f req)
  run_oracle req := h.run_oracle (f req)
  assignment_salt req := h.assignment_salt (f req)

end LeafKernel

/-! ### Oracles that agree off a set -/

/-- Two oracles agree off the set `Z`. -/
def AgreeOff (Z : Set X) (O O' : X → Y) : Prop :=
  ∀ x, x ∉ Z → O x = O' x

theorem AgreeOff.reprogram [DecidableEq X] {Z : Set X} {O O' : X → Y} (h : AgreeOff Z O O')
    (ass : List (Assignment X Y)) : AgreeOff Z (O.reprogram ass) (O'.reprogram ass) :=
  fun x hx => reprogram_apply_congr ass (h x hx)

/-- The inputs carrying one of the salts `ν`, as a salt slot with one value. -/
noncomputable def inSalts {N Pos : Type} (nsalt : X → Option N) (ν : Pos → N) : X → Option Unit :=
  open Classical in fun x => if ∃ p, nsalt x = some (ν p) then some () else none

theorem inSalts_eq_some_iff {N Pos : Type} {nsalt : X → Option N} {ν : Pos → N} {x : X} :
    inSalts nsalt ν x = some () ↔ ∃ p, nsalt x = some (ν p) := by
  classical
  unfold inSalts
  split_ifs with h <;> simp [h]

theorem inSalts_eq_none_of_salt_none {N Pos : Type} {nsalt : X → Option N} {ν : Pos → N} {x : X}
    (h : nsalt x = none) : inSalts nsalt ν x ≠ some () := by
  rw [Ne, inSalts_eq_some_iff]
  rintro ⟨p, hp⟩
  rw [h] at hp
  cases hp

/-! ### Relabelling and swapping uniform functions -/

section Relabel

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

theorem replaceSlice_replaceSlice_swap' {Sd : Type} [DecidableEq Sd] (s : X → Option Sd) (σ : Sd)
    (H F : X → Y) : replaceSlice s σ (replaceSlice s σ H F) (replaceSlice s σ F H) = H := by
  funext y
  by_cases h : s y = some σ <;> simp [replaceSlice, h]

/-- **Relabelling a slice of a uniform function** (exact): a uniform `H` with the slice of `σ`
answered by an independent uniform `G` is uniform. -/
theorem expect_replaceSlice {Sd : Type} [DecidableEq Sd] (s : X → Option Sd) (σ : Sd)
    (f : (X → Y) → ℝ) : 𝔼 H : X → Y, 𝔼 G : X → Y, f (replaceSlice s σ H G) = 𝔼 H, f H := by
  let g : (X → Y) × (X → Y) → (X → Y) × (X → Y) := fun p =>
    (replaceSlice s σ p.1 p.2, replaceSlice s σ p.2 p.1)
  have hg : Function.Involutive g := by
    rintro ⟨H, G⟩
    simp only [g, replaceSlice_replaceSlice_swap']
  rw [← expect_prod_eq (fun p : (X → Y) × (X → Y) => f (g p).1)]
  have h2 : 𝔼 H, f H = 𝔼 p : (X → Y) × (X → Y), f p.1 := by
    rw [expect_prod_eq]
    simp only [Fintype.expect_const]
  rw [h2]
  exact Fintype.expect_equiv hg.toPerm (fun p => f (g p).1) (fun p => f p.1) fun p => rfl

/-- **Filling points of a function from a vector**: `fill s pt G d` is `G` with the value at
`pt p` replaced by `d p` for each `p` with `s p`. -/
noncomputable def fill {ι : Type} (s : ι → Bool) (pt : ι → X) (G : X → Y) (d : ι → Y) : X → Y :=
  open Classical in fun x => if h : ∃ p, s p = true ∧ pt p = x then d h.choose else G x

theorem fill_apply_of_forall_ne {ι : Type} {s : ι → Bool} {pt : ι → X} (G : X → Y) (d : ι → Y) {x : X}
    (h : ∀ p, s p = true → pt p ≠ x) : fill s pt G d x = G x := by
  classical
  unfold fill
  rw [dif_neg]
  rintro ⟨p, hp, e⟩
  exact h p hp e

theorem fill_apply_pt {ι : Type} {s : ι → Bool} {pt : ι → X}
    (hinj : ∀ p q, s p = true → s q = true → pt p = pt q → p = q) (G : X → Y) (d : ι → Y) {p : ι}
    (hp : s p = true) : fill s pt G d (pt p) = d p := by
  classical
  unfold fill
  have h : ∃ q, s q = true ∧ pt q = pt p := ⟨p, hp, rfl⟩
  rw [dif_pos h]
  rw [hinj _ _ h.choose_spec.1 hp h.choose_spec.2]

/-- **Swapping the values of a uniform function at injective points with a uniform vector**
(exact): reading the values of `G` at the points `pt p` (`s p`) is the same as filling those
points of `G` from the vector `d` and reading `d`. -/
theorem expect_fill {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Bool) (pt : ι → X)
    (hinj : ∀ p q, s p = true → s q = true → pt p = pt q → p = q) (f : (X → Y) → (ι → Y) → ℝ) :
    𝔼 G : X → Y, 𝔼 d : ι → Y, f G (fun p => if s p then G (pt p) else d p) =
      𝔼 G : X → Y, 𝔼 d : ι → Y, f (fill s pt G d) d := by
  let g : (X → Y) × (ι → Y) → (X → Y) × (ι → Y) := fun q =>
    (fill s pt q.1 q.2, fun p => if s p then q.1 (pt p) else q.2 p)
  have hg : Function.Involutive g := by
    rintro ⟨G, d⟩
    simp only [g, Prod.mk.injEq]
    refine ⟨funext fun x => ?_, funext fun p => ?_⟩
    · by_cases hx : ∃ p, s p = true ∧ pt p = x
      · obtain ⟨p, hp, rfl⟩ := hx
        rw [fill_apply_pt hinj _ _ hp, if_pos hp]
      · push Not at hx
        rw [fill_apply_of_forall_ne _ _ hx, fill_apply_of_forall_ne _ _ hx]
    · by_cases hp : s p = true
      · rw [if_pos hp, fill_apply_pt hinj _ _ hp]
      · rw [if_neg hp, if_neg hp]
  rw [← expect_prod_eq (fun q : (X → Y) × (ι → Y) => f q.1 (g q).2),
    ← expect_prod_eq (fun q : (X → Y) × (ι → Y) => f (g q).1 q.2)]
  refine Fintype.expect_equiv hg.toPerm _ _ fun q => ?_
  change f q.1 (g q).2 = f (g (g q)).1 (g q).2
  rw [hg q]

end Relabel

/-! ### Runs that agree off a set after one proof query -/

section Post

variable [DecidableEq X]

/-- **The run with proof query `j` overridden is the run with a constant reply to it**: if the run
with proof query `j` answered by `g₀` makes proof query `j` at step `k₀` with `req₀`, then for every `g`
the run with proof query `j` answered by `g` is the run with proof query `j` answered by the constant
reply `g req₀ O₀`, `O₀` the oracle at step `k₀`. -/
theorem IAlg.run_override_eq_const {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (R : Responder X Y Stmt Wit Proof) (O : X → Y) {j : ℕ} (g₀ g : ReplyFn X Y Stmt Wit Proof)
    {k₀ : ℕ} {req₀ : ProofQuery Stmt Wit} (hk₀ : (A.run (override R j g₀) O k₀).nreq = j)
    (hreq₀ : A.next (A.run (override R j g₀) O k₀).hist = .request req₀) :
    ∀ k ≤ m, A.run (override R j g) O k =
      A.run (override R j (fun _ _ => g req₀ (A.run (override R j g₀) O k₀).oracle)) O k := by
  refine A.run_eq_of_forall_ne (j := j) (fun i hi => by
    rw [override_of_ne _ _ hi, override_of_ne _ _ hi]) (fun k _ req hk hreq => ?_)
  have hlt : ∀ i < j, override R j g i = override R j g₀ i := fun i hi => by
    rw [override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
  have hpre := A.run_eq_of_forall_lt (O := O) hlt k hk.le
  have hreq' : A.next (A.run (override R j g₀) O k).hist = .request req := by rw [hpre]; exact hreq
  have hkk : k = k₀ := A.eq_of_request_of_nreq_eq hreq' hreq₀ (by rw [hpre, hk, hk₀])
  subst hkk
  have hrr : req = req₀ := by
    rw [hreq'] at hreq₀
    exact Action.request.inj hreq₀
  subst hrr
  rw [override_self, override_self, hpre]

/-- **Runs whose oracles differ off `Z` only after proof query `j`**: let `R` and `R'` agree except at
proof query `j`, whose replies have equal responses and states that agree off `Z`; let the later
proof queries' replies keep responses and agreement off `Z`. If no query of the run of `R'` after
proof query `j` lies in `Z`, the two runs have the same replies and proof queries at every step, the same
oracle up to proof query `j` and oracles that agree off `Z` after it. -/
theorem IAlg.run_agreeOff {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {R R' : Responder X Y Stmt Wit Proof}
    {H : X → Y} {Z : Set X} {j : ℕ} (hR : ∀ i, i ≠ j → R i = R' i)
    (hj : ∀ req O, (R j req O).response = (R' j req O).response ∧
      AgreeOff Z (R j req O).state (R' j req O).state)
    (hlater : ∀ i, j < i → ∀ req O O', AgreeOff Z O O' →
      (R i req O).response = (R i req O').response ∧ AgreeOff Z (R i req O).state (R i req O').state)
    (hq : ∀ k < m, ∀ x, j < (A.run R' H k).nreq → A.next (A.run R' H k).hist = .query x → x ∉ Z) :
    ∀ k ≤ m, (A.run R H k).hist = (A.run R' H k).hist ∧ (A.run R H k).nreq = (A.run R' H k).nreq ∧
      AgreeOff Z (A.run R H k).oracle (A.run R' H k).oracle ∧
      ((A.run R' H k).nreq ≤ j → (A.run R H k).oracle = (A.run R' H k).oracle)
  | 0, _ => ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
  | k + 1, hk => by
    obtain ⟨hh, hn, ho, he⟩ := IAlg.run_agreeOff A hR hj hlater hq k (by omega)
    rw [IAlg.run_succ, IAlg.run_succ]
    set s := A.run R H k
    set s' := A.run R' H k
    cases hnext : A.next s'.hist with
    | query x =>
      have hnext₁ : A.next s.hist = .query x := by rw [hh]; exact hnext
      rw [IAlg.step_of_query hnext, IAlg.step_of_query hnext₁]
      have hx : s.oracle x = s'.oracle x := by
        by_cases hle : s'.nreq ≤ j
        · rw [he hle]
        · exact ho x (hq k (by omega) x (lt_of_not_ge hle) hnext)
      exact ⟨by simp only [hh, hx], hn, ho, he⟩
    | request req =>
      have hnext₁ : A.next s.hist = .request req := by rw [hh]; exact hnext
      rw [IAlg.step_of_request hnext, IAlg.step_of_request hnext₁]
      rcases lt_trichotomy s'.nreq j with hlt | heq | hgt
      · rw [hn, he hlt.le, hR _ hlt.ne, hh]
        exact ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
      · rw [hn, heq, he heq.le, hh]
        obtain ⟨hr, hs⟩ := hj req s'.oracle
        exact ⟨by rw [hr], rfl, hs, fun h => by simp only at h; omega⟩
      · rw [hn, hh]
        obtain ⟨hr, hs⟩ := hlater _ hgt req s.oracle s'.oracle ho
        rw [hR _ hgt.ne'] at hr hs ⊢
        exact ⟨by rw [hr], rfl, hs, fun h => by simp only at h; omega⟩

end Post

/-! ### Replies of local kernels -/

section Local

variable [DecidableEq X] {N Pos C : Type} (nsalt : X → Option N) (pub : Finset N)
  (rel : Stmt → Wit → Prop) [DecidableRel rel]

/-- **A kernel is local in its salts**: its reply reads the oracle only at salt-free inputs, at
inputs carrying a public salt and at inputs carrying one of its own salts `own c`, and programs only
salt-free inputs. -/
structure KernelLocal (K : Kernel X Y Stmt Wit Proof C) (own : C → Pos → N) : Prop where
  congr : ∀ req O O' c, (∀ x, (nsalt x = none ∨ (∃ a ∈ pub, nsalt x = some a) ∨
      ∃ p, nsalt x = some (own c p)) → O x = O' x) →
    K req O c = K req O' c
  assignment_salt : ∀ req O c, ∀ a ∈ (K req O c).assignments, nsalt a.input = none

variable {nsalt pub rel}

/-- **A local kernel's reply commutes with relabelling the inputs of foreign salts**: if none of
its own salts is among `ν`, its reply on the oracle with the inputs carrying a salt of `ν` answered
by `G` has the same response, and its state is the state on the original oracle relabelled. -/
theorem KernelLocal.reply_replaceSlice {K : Kernel X Y Stmt Wit Proof C} {own : C → Pos → N}
    (hK : KernelLocal nsalt pub K own) {Pos' : Type} {ν : Pos' → N} {c : C}
    (hd : ∀ p q, own c p ≠ ν q) (hpub : ∀ q, ν q ∉ pub) (req : ProofQuery Stmt Wit) (O G : X → Y) :
    (kernelReply rel K c req (replaceSlice (inSalts nsalt ν) () O G)).response =
        (kernelReply rel K c req O).response ∧
      (kernelReply rel K c req (replaceSlice (inSalts nsalt ν) () O G)).state =
        replaceSlice (inSalts nsalt ν) () (kernelReply rel K c req O).state G := by
  have hK' : K req (replaceSlice (inSalts nsalt ν) () O G) c = K req O c := by
    refine hK.congr req _ _ c fun x hx => ?_
    have : inSalts nsalt ν x ≠ some () := by
      rcases hx with hx | ⟨a, ha, hx⟩ | ⟨p, hp⟩
      · exact inSalts_eq_none_of_salt_none hx
      · rw [Ne, inSalts_eq_some_iff]
        rintro ⟨q, hq⟩
        rw [hx] at hq
        exact hpub q (Option.some_injective _ hq ▸ ha)
      · rw [Ne, inSalts_eq_some_iff]
        rintro ⟨q, hq⟩
        rw [hp] at hq
        exact hd p q (Option.some_injective _ hq)
    simp only [replaceSlice, this, if_false]
  unfold kernelReply
  split_ifs
  · rw [hK']
    refine ⟨rfl, funext fun y => ?_⟩
    dsimp only
    have hass : ∀ a ∈ (K req O c).assignments, inSalts nsalt ν a.input ≠ some () := fun a ha =>
      inSalts_eq_none_of_salt_none (hK.assignment_salt req O c a ha)
    by_cases hy : inSalts nsalt ν y = some ()
    · rw [reprogram_apply_of_forall_ne _ fun a ha e => hass a ha (e ▸ hy)]
      simp only [replaceSlice, hy, if_true]
    · rw [show replaceSlice (inSalts nsalt ν) () (O.reprogram (K req O c).assignments) G y =
        O.reprogram (K req O c).assignments y from if_neg hy]
      exact reprogram_apply_congr _ (if_neg hy)
  · exact ⟨rfl, rfl⟩

/-- **A local kernel's reply keeps agreement off a set of foreign inputs**: if every input of `Z`
carries a salt and none of the kernel's own salts is one of them, oracles that agree off `Z` give
equal responses and states that agree off `Z`. -/
theorem KernelLocal.reply_agreeOff {K : Kernel X Y Stmt Wit Proof C} {own : C → Pos → N}
    (hK : KernelLocal nsalt pub K own) {Z : Set X} {c : C}
    (hZ : ∀ x ∈ Z, nsalt x ≠ none ∧ (∀ a ∈ pub, nsalt x ≠ some a) ∧ ∀ p, nsalt x ≠ some (own c p))
    (req : ProofQuery Stmt Wit)
    {O O' : X → Y} (h : AgreeOff Z O O') :
    (kernelReply rel K c req O).response = (kernelReply rel K c req O').response ∧
      AgreeOff Z (kernelReply rel K c req O).state (kernelReply rel K c req O').state := by
  have hK' : K req O c = K req O' c := by
    refine hK.congr req _ _ c fun x hx => h x fun hxZ => ?_
    rcases hx with hx | ⟨a, ha, hx⟩ | ⟨p, hp⟩
    · exact (hZ x hxZ).1 hx
    · exact (hZ x hxZ).2.1 a ha hx
    · exact (hZ x hxZ).2.2 p hp
  unfold kernelReply
  split_ifs
  · rw [hK']
    exact ⟨rfl, h.reprogram _⟩
  · exact ⟨rfl, h⟩

end Local

namespace LeafKernel

variable [DecidableEq X] {Cm Pos N : Type} {L : LeafKernel X Y Stmt Wit Proof Cm Pos N}
  {nsalt : X → Option N} {pub : Finset N}

/-- The kernel with uniform digests is local in the salts of its coins. -/
theorem Laws.kernelLocal_kD (hL : L.Laws nsalt pub) :
    KernelLocal nsalt pub L.kD (fun c : LeafCoins Cm Pos N Y => c.salts) where
  congr req O O' c h := hL.run_oracle req O O' c.main c.salts c.digests fun x hx => h x (by
    rcases hx with hx | hx | ⟨p, -, hp⟩
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr ⟨p, hp⟩))
  assignment_salt req O c := hL.assignment_salt req O c.main c.salts c.digests

/-- The kernel with honest digests is local in the salts of its coins. -/
theorem Laws.kernelLocal_kL (hL : L.Laws nsalt pub) :
    KernelLocal nsalt pub L.kL (fun c : LeafCoins Cm Pos N Y => c.salts) where
  congr req O O' c h := by
    unfold kL
    rw [show (fun p => O (L.point req c.main p (c.salts p))) =
        fun p => O' (L.point req c.main p (c.salts p)) from funext fun p =>
      h _ (Or.inr (Or.inr ⟨p, hL.point_salt _ _ _ _⟩))]
    exact hL.run_oracle req O O' c.main c.salts _ fun x hx => h x (by
      rcases hx with hx | hx | ⟨p, -, hp⟩
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨p, hp⟩))
  assignment_salt req O c := hL.assignment_salt req O c.main c.salts _

end LeafKernel

/-! ### The hybrid step -/

section Step

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {Cm Pos N : Type} [Fintype Cm]
  [Nonempty Cm] [Fintype Pos] [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N]
  (rel : Stmt → Wit → Prop) [DecidableRel rel] (L : LeafKernel X Y Stmt Wit Proof Cm Pos N)
  (nsalt : X → Option N) (pub : Finset N)

/-- The tape of the leaf hybrids: the initial oracle and the coins of each proof query. -/
abbrev LTape (X Y Cm Pos N : Type) (Q : ℕ) : Type := (X → Y) × (Fin Q → LeafCoins Cm Pos N Y)

/-- **The probability that `A` outputs `true` in hybrid `j` of the leaf kernels** (`kD` below `j`,
`kL` from `j` on, on shared coins), over a uniform tape. -/
noncomputable def lHybProb {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q j : ℕ) : ℝ :=
  𝔼 ω : LTape X Y Cm Pos N Q, ind (A.accepts (kHyb rel L.kL L.kD j ω.2 ω.2) ω.1)

theorem toReal_acceptProb_progEnv_kL {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q : ℕ) :
    (A.acceptProb (progEnv rel L.kL Q)).toReal = lHybProb rel L A Q 0 := by
  rw [toReal_acceptProb_progEnv, lHybProb]
  refine Finset.expect_congr rfl fun ω _ => ?_
  rw [kHyb_zero rel L.kL L.kD ω.2 ω.2 ω.1]

theorem toReal_acceptProb_progEnv_kD {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q : ℕ) :
    (A.acceptProb (progEnv rel L.kD Q)).toReal = lHybProb rel L A Q Q := by
  rw [toReal_acceptProb_progEnv, lHybProb]
  refine Finset.expect_congr rfl fun ω _ => ?_
  rw [kHyb_Q rel L.kL L.kD ω.2 ω.2 ω.1]

variable {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Q j : ℕ} (hj : j < Q)

/-- The coins of proof query `j`. -/
abbrev cj (ω : LTape X Y Cm Pos N Q) : LeafCoins Cm Pos N Y := ω.2 ⟨j, hj⟩

/-- Hybrid `j` with proof query `j` refused: the common run of hybrids `j` and `j + 1` before
proof query `j`. -/
def lBase (ω : LTape X Y Cm Pos N Q) : Responder X Y Stmt Wit Proof :=
  override (kHyb rel L.kL L.kD j ω.2 ω.2) j refuseReply

/-- **A query of the run before proof query `j` carries a salt of proof query `j`.** -/
def PreHit (ω : LTape X Y Cm Pos N Q) : Prop :=
  ∃ k < m, ∃ x, A.next (A.run (lBase rel L ω (j := j)) ω.1 k).hist = .query x ∧
    ∃ p, nsalt x = some ((cj hj ω).salts p)

/-- **Two salts of the tape coincide, one of them a salt of proof query `j`, or a salt of proof query `j`
is public.** -/
def SaltBad (ω : LTape X Y Cm Pos N Q) : Prop :=
  (∃ i : Fin Q, ∃ p q : Pos, (i, p) ≠ (⟨j, hj⟩, q) ∧ (ω.2 i).salts p = (cj hj ω).salts q) ∨
    ∃ q, (cj hj ω).salts q ∈ pub

/-- **A query of a run carries the salt of a hidden position of proof query `j`**: the run of `R`
from `H₀` makes proof query `j` with `req`, and some query of the run carries the salt (in the coins
`c`) of a position hidden for `req`. -/
def HitRun (R : Responder X Y Stmt Wit Proof) (H₀ : X → Y) (c : LeafCoins Cm Pos N Y) : Prop :=
  ∃ k₀ < m, ∃ req, (A.run R H₀ k₀).nreq = j ∧ A.next (A.run R H₀ k₀).hist = .request req ∧
    ∃ p, L.hidden req c.main p = true ∧
      ∃ k < m, ∃ x, A.next (A.run R H₀ k).hist = .query x ∧ nsalt x = some (c.salts p)

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- `HitRun` depends on a run only through its replies and proof queries. -/
theorem hitRun_congr {R R' : Responder X Y Stmt Wit Proof} {H₀ H₀' : X → Y}
    (h : ∀ k ≤ m, (A.run R H₀ k).hist = (A.run R' H₀' k).hist ∧
      (A.run R H₀ k).nreq = (A.run R' H₀' k).nreq) (c : LeafCoins Cm Pos N Y) :
    HitRun L nsalt A (j := j) R H₀ c ↔ HitRun L nsalt A (j := j) R' H₀' c := by
  unfold HitRun
  constructor
  · rintro ⟨k₀, hk₀, req, hn, hr, p, hp, k, hk, x, hx, hs⟩
    exact ⟨k₀, hk₀, req, (h k₀ hk₀.le).2 ▸ hn, (h k₀ hk₀.le).1 ▸ hr, p, hp, k, hk, x,
      (h k hk.le).1 ▸ hx, hs⟩
  · rintro ⟨k₀, hk₀, req, hn, hr, p, hp, k, hk, x, hx, hs⟩
    exact ⟨k₀, hk₀, req, (h k₀ hk₀.le).2.symm ▸ hn, (h k₀ hk₀.le).1.symm ▸ hr, p, hp, k, hk, x,
      (h k hk.le).1.symm ▸ hx, hs⟩

/-! #### The hybrid's replies -/

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N] in
theorem kHyb_of_lt {C₁ C₂ : Type} (K₁ : Kernel X Y Stmt Wit Proof C₁) (K₂ : Kernel X Y Stmt Wit Proof C₂)
    {Q' i j' : ℕ} (c₁ : Fin Q' → C₁) (c₂ : Fin Q' → C₂) (hi : i < j') (hiQ : i < Q') :
    kHyb rel K₁ K₂ j' c₁ c₂ i = kernelReply rel K₂ (c₂ ⟨i, hiQ⟩) := by
  funext req O
  simp only [kHyb, dif_pos hiQ, if_pos hi]

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N] in
theorem kHyb_of_ge {C₁ C₂ : Type} (K₁ : Kernel X Y Stmt Wit Proof C₁) (K₂ : Kernel X Y Stmt Wit Proof C₂)
    {Q' i j' : ℕ} (c₁ : Fin Q' → C₁) (c₂ : Fin Q' → C₂) (hi : j' ≤ i) (hiQ : i < Q') :
    kHyb rel K₁ K₂ j' c₁ c₂ i = kernelReply rel K₁ (c₁ ⟨i, hiQ⟩) := by
  funext req O
  simp only [kHyb, dif_pos hiQ, if_neg (not_lt.2 hi)]

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N] in
theorem kHyb_of_Q_le {C₁ C₂ : Type} (K₁ : Kernel X Y Stmt Wit Proof C₁) (K₂ : Kernel X Y Stmt Wit Proof C₂)
    {Q' i j' : ℕ} (c₁ : Fin Q' → C₁) (c₂ : Fin Q' → C₂) (hiQ : ¬ i < Q') :
    kHyb rel K₁ K₂ j' c₁ c₂ i = fun _ O => ⟨none, O⟩ := by
  funext req O
  simp only [kHyb, dif_neg hiQ]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
theorem override_congr_of_ne {R R' : Responder X Y Stmt Wit Proof} {j' : ℕ}
    (h : ∀ i, i ≠ j' → R i = R' i) (g : ReplyFn X Y Stmt Wit Proof) :
    override R j' g = override R' j' g := by
  funext i
  by_cases hi : i = j'
  · simp only [override, if_pos hi]
  · simp only [override, if_neg hi, h i hi]

/-- The tape with the values of proof query `j` replaced by `d`. -/
def withDigests (ω : LTape X Y Cm Pos N Q) (d : Pos → Y) : LTape X Y Cm Pos N Q :=
  (ω.1, Function.update ω.2 ⟨j, hj⟩ { cj hj ω with digests := d })

/-- **The run that relabels at proof query `j`**: hybrid `j'` with proof query `j` answered on the oracle
in force with the inputs carrying a salt of proof query `j` answered by `G`. -/
noncomputable def relabelResp (j' : ℕ) (ω : LTape X Y Cm Pos N Q) (G : X → Y) : Responder X Y Stmt Wit Proof :=
  override (kHyb rel L.kL L.kD j' ω.2 ω.2) j fun req O =>
    kHyb rel L.kL L.kD j' ω.2 ω.2 j req (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G)

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- With `¬ SaltBad`, the proof queries other than `j` have no salt of proof query `j`. -/
theorem salts_ne_of_not_saltBad {ω : LTape X Y Cm Pos N Q} (hsb : ¬ SaltBad pub hj ω) {i : Fin Q}
    (hi : (i : ℕ) ≠ j) (p q : Pos) : (ω.2 i).salts p ≠ (cj hj ω).salts q := fun e =>
  hsb (Or.inl ⟨i, p, q, fun h => hi (by have := congrArg (fun z => (z.1 : ℕ)) h; simpa using this), e⟩)

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- With `¬ SaltBad`, no salt of proof query `j` is public. -/
theorem salts_not_pub_of_not_saltBad {ω : LTape X Y Cm Pos N Q} (hsb : ¬ SaltBad pub hj ω) (q : Pos) :
    (cj hj ω).salts q ∉ pub := fun h => hsb (Or.inr ⟨q, h⟩)

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- With `¬ SaltBad`, the salts of proof query `j` are distinct. -/
theorem salts_injective_of_not_saltBad {ω : LTape X Y Cm Pos N Q} (hsb : ¬ SaltBad pub hj ω) :
    Function.Injective (cj hj ω).salts := fun p q e => by
  by_contra hpq
  exact hsb (Or.inl ⟨⟨j, hj⟩, p, q, fun h => hpq (by simpa using h), e⟩)

variable {rel L nsalt pub}

/-- **The coupling of step 2**: unless `PreHit` or `SaltBad`, hybrid `j'` (`j' = j` or `j + 1`)
from the oracle with the inputs of proof query `j`'s salts answered by `G` has the replies and proof queries
of the run from the original oracle that relabels at proof query `j`. -/
theorem hist_relabel (hL : L.Laws nsalt pub) {j' : ℕ} (hj' : j' = j ∨ j' = j + 1)
    (ω : LTape X Y Cm Pos N Q) (G : X → Y) (hpre : ¬ PreHit rel L nsalt A hj ω)
    (hsb : ¬ SaltBad pub hj ω) :
    ∀ k ≤ m, (A.run (kHyb rel L.kL L.kD j' ω.2 ω.2)
        (replaceSlice (inSalts nsalt (cj hj ω).salts) () ω.1 G) k).hist =
        (A.run (relabelResp rel L nsalt hj j' ω G) ω.1 k).hist ∧
      (A.run (kHyb rel L.kL L.kD j' ω.2 ω.2)
        (replaceSlice (inSalts nsalt (cj hj ω).salts) () ω.1 G) k).nreq =
        (A.run (relabelResp rel L nsalt hj j' ω G) ω.1 k).nreq := by
  classical
  have hjj : j ≤ j' := by omega
  have h12 : ∀ i, i ≠ j → relabelResp rel L nsalt hj j' ω G i = kHyb rel L.kL L.kD j' ω.2 ω.2 i :=
    fun i hi => override_of_ne _ _ hi
  have hlt : ∀ i < j, ∀ req O,
      (kHyb rel L.kL L.kD j' ω.2 ω.2 i req (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G)).response =
          (kHyb rel L.kL L.kD j' ω.2 ω.2 i req O).response ∧
        (kHyb rel L.kL L.kD j' ω.2 ω.2 i req (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G)).state =
          replaceSlice (inSalts nsalt (cj hj ω).salts) () (kHyb rel L.kL L.kD j' ω.2 ω.2 i req O).state G :=
      fun i hi req O => by
    have hiQ : i < Q := hi.trans hj
    rw [kHyb_of_lt rel L.kL L.kD ω.2 ω.2 (hi.trans_le hjj) hiQ]
    exact hL.kernelLocal_kD.reply_replaceSlice
      (fun p q => salts_ne_of_not_saltBad _ hj hsb (i := ⟨i, hiQ⟩) hi.ne p q)
      (salts_not_pub_of_not_saltBad _ hj hsb) req O G
  have hjrep : ∀ req O, relabelResp rel L nsalt hj j' ω G j req O =
      kHyb rel L.kL L.kD j' ω.2 ω.2 j req (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G) :=
      fun req O => by
    rw [relabelResp, override_self]
  have hbase : ∀ i < j, relabelResp rel L nsalt hj j' ω G i = lBase rel L ω (j := j) i := fun i hi => by
    rw [lBase, relabelResp, override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
    rcases hj' with rfl | rfl
    · rfl
    · exact kHyb_succ_of_ne rel L.kL L.kD ω.2 ω.2 hi.ne
  have hq : ∀ k < m, ∀ x, (A.run (relabelResp rel L nsalt hj j' ω G) ω.1 k).nreq ≤ j →
      A.next (A.run (relabelResp rel L nsalt hj j' ω G) ω.1 k).hist = .query x →
      inSalts nsalt (cj hj ω).salts x ≠ some () := fun k hk x hn hx e => by
    have he := A.run_eq_of_forall_lt (O := ω.1) hbase k hn
    rw [inSalts_eq_some_iff] at e
    exact hpre ⟨k, hk, x, by rw [he]; exact hx, e⟩
  intro k hk
  rcases run_coupling (inSalts nsalt (cj hj ω).salts) A h12 hlt hjrep hq k hk with
    ⟨-, hrel⟩ | ⟨-, heq⟩
  · exact ⟨hrel.hist, hrel.nreq⟩
  · rw [heq]
    exact ⟨rfl, rfl⟩

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N] in
theorem cj_withDigests (ω : LTape X Y Cm Pos N Q) (d : Pos → Y) :
    cj hj (withDigests hj ω d) = { cj hj ω with digests := d } := by
  simp [withDigests, cj]

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- Hybrid `j`'s relabelling run at any values of proof query `j`: proof query `j` is answered by `kL`
on the relabelled oracle, which does not read the values. -/
theorem relabelResp_withDigests_self (ω : LTape X Y Cm Pos N Q) (d : Pos → Y) (G : X → Y) :
    relabelResp rel L nsalt hj j (withDigests hj ω d) G =
      override (kHyb rel L.kL L.kD j ω.2 ω.2) j fun req O =>
        kernelReply rel L.kL (cj hj ω) req (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G) := by
  unfold relabelResp
  rw [cj_withDigests]
  unfold withDigests
  rw [override_kHyb_update rel L.kL L.kD hj j ω.2 ω.2]
  congr 1
  funext req O
  rw [kHyb_of_ge rel L.kL L.kD _ _ le_rfl hj]
  simp only [Function.update_self]
  rfl

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- Hybrid `j + 1`'s relabelling run at the values `d` of proof query `j`: proof query `j` is answered by
`kD` with the values `d` on the relabelled oracle. -/
theorem relabelResp_withDigests_succ (ω : LTape X Y Cm Pos N Q) (d : Pos → Y) (G : X → Y) :
    relabelResp rel L nsalt hj (j + 1) (withDigests hj ω d) G =
      override (kHyb rel L.kL L.kD j ω.2 ω.2) j fun req O =>
        kernelReply rel L.kD { cj hj ω with digests := d } req
          (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G) := by
  unfold relabelResp
  rw [cj_withDigests]
  unfold withDigests
  rw [override_kHyb_update rel L.kL L.kD hj (j + 1) ω.2 ω.2,
    override_congr_of_ne (fun i hi => kHyb_succ_of_ne rel L.kL L.kD ω.2 ω.2 hi)]
  congr 1
  funext req O
  rw [kHyb_of_lt rel L.kL L.kD _ _ (Nat.lt_succ_self j) hj]
  simp only [Function.update_self]

open Classical in
/-- **Steps 3 and 4** at the override form of the relabelling runs. -/
theorem abs_expect_override_sub_le (hL : L.Laws nsalt pub) (hpost : A.PostOracleFree)
    (ω : LTape X Y Cm Pos N Q) (hsb : ¬ SaltBad pub hj ω) :
    |𝔼 d : Pos → Y, 𝔼 G : X → Y,
        (ind (A.accepts (override (kHyb rel L.kL L.kD j ω.2 ω.2) j fun req O =>
            kernelReply rel L.kL (cj hj ω) req (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G)) ω.1) -
          ind (A.accepts (override (kHyb rel L.kL L.kD j ω.2 ω.2) j fun req O =>
            kernelReply rel L.kD { cj hj ω with digests := d } req
              (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G)) ω.1))| ≤
      𝔼 d : Pos → Y, 𝔼 G : X → Y,
        (if HitRun L nsalt A (j := j) (override (kHyb rel L.kL L.kD j ω.2 ω.2) j fun req O =>
            kernelReply rel L.kD { cj hj ω with digests := d } req
              (replaceSlice (inSalts nsalt (cj hj ω).salts) () O G)) ω.1 (cj hj ω)
          then (1 : ℝ) else 0) := by
  set c := cj hj ω with hc
  set R := kHyb rel L.kL L.kD j ω.2 ω.2 with hR
  set T := inSalts nsalt c.salts with hT
  have hnn : 0 ≤ 𝔼 d : Pos → Y, 𝔼 G : X → Y,
      (if HitRun L nsalt A (j := j) (override R j fun req O =>
          kernelReply rel L.kD { c with digests := d } req (replaceSlice T () O G)) ω.1 c
        then (1 : ℝ) else 0) :=
    Finset.expect_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hM : ∃ k₀ < m, ∃ req, (A.run (override R j refuseReply) ω.1 k₀).nreq = j ∧
      A.next (A.run (override R j refuseReply) ω.1 k₀).hist = .request req
  swap
  · push Not at hM
    have hz : ∀ g : ReplyFn X Y Stmt Wit Proof,
        A.accepts (override R j g) ω.1 = A.accepts (override R j refuseReply) ω.1 := fun g =>
      A.accepts_override_eq_of_not_made R ω.1 refuseReply g fun k hk req hn => hM k hk req hn
    simp only [hz, sub_self, Finset.expect_const_zero, abs_zero]
    exact hnn
  obtain ⟨k₀, hk₀, req₀, hn₀, hr₀⟩ := hM
  set O₀ := (A.run (override R j refuseReply) ω.1 k₀).oracle with hO₀
  have hconst : ∀ g : ReplyFn X Y Stmt Wit Proof,
      A.accepts (override R j g) ω.1 = A.accepts (override R j (fun _ _ => g req₀ O₀)) ω.1 :=
    fun g => A.accepts_override_eq R ω.1 refuseReply g hn₀ hr₀
  by_cases hrel : ¬ rel req₀.stmt req₀.wit
  · have heq : ∀ (d : Pos → Y) (G : X → Y), kernelReply rel L.kL c req₀ (replaceSlice T () O₀ G) =
        kernelReply rel L.kD { c with digests := d } req₀ (replaceSlice T () O₀ G) := fun d G => by
      simp only [kernelReply, if_neg hrel]
    have hz : ∀ (d : Pos → Y) (G : X → Y),
        ind (A.accepts (override R j fun req O => kernelReply rel L.kL c req (replaceSlice T () O G)) ω.1) -
          ind (A.accepts (override R j fun req O =>
            kernelReply rel L.kD { c with digests := d } req (replaceSlice T () O G)) ω.1) = 0 :=
      fun d G => by rw [hconst, hconst (fun req O => kernelReply rel L.kD _ req _), heq, sub_self]
    simp only [hz, Finset.expect_const_zero, abs_zero]
    exact hnn
  push Not at hrel
  set s : Pos → Bool := fun p => L.hidden req₀ c.main p with hs
  set pt : Pos → X := fun p => L.point req₀ c.main p (c.salts p) with hpt
  have hinj : ∀ p q, s p = true → s q = true → pt p = pt q → p = q := fun p q _ _ e => by
    have := congrArg nsalt e
    simp only [pt, hL.point_salt] at this
    exact salts_injective_of_not_saltBad _ hj hsb (Option.some_injective _ this)
  have hptT : ∀ p, T (pt p) = some () := fun p =>
    inSalts_eq_some_iff.2 ⟨p, hL.point_salt _ _ _ _⟩
  -- the reply at proof query `j` with values `e` on the relabelled oracle with `G'`
  let rD : (X → Y) → (Pos → Y) → EnvReply Proof (X → Y) := fun G' e =>
    ⟨some (L.run req₀ (replaceSlice T () O₀ G') c.main c.salts e).proof,
      (replaceSlice T () O₀ G').reprogram (L.run req₀ (replaceSlice T () O₀ G') c.main c.salts e).assignments⟩
  let F : (X → Y) → (Pos → Y) → ℝ := fun G' e => ind (A.accepts (override R j fun _ _ => rD G' e) ω.1)
  have hFL : ∀ (d : Pos → Y) (G : X → Y), ind (A.accepts (override R j fun req O =>
      kernelReply rel L.kL c req (replaceSlice T () O G)) ω.1) =
      F G (fun p => if s p then G (pt p) else d p) := fun d G => by
    rw [hconst]
    simp only [F, rD, kernelReply, if_pos hrel, LeafKernel.kL]
    rw [hL.run_digests req₀ _ c.main c.salts _ (fun p => if s p then G (pt p) else d p) fun p hp => by
      have hp' : s p = true := hp
      simp only [hp', if_true]
      exact if_pos (hptT p)]
  have hFD : ∀ (d : Pos → Y) (G : X → Y), ind (A.accepts (override R j fun req O =>
      kernelReply rel L.kD { c with digests := d } req (replaceSlice T () O G)) ω.1) = F G d :=
    fun d G => by
      rw [hconst]
      simp only [F, rD, kernelReply, if_pos hrel, LeafKernel.kD]
  have hgoal : ∀ (d : Pos → Y) (G : X → Y), |F (fill s pt G d) d - F G d| ≤
      (if HitRun L nsalt A (j := j) (override R j fun req O =>
          kernelReply rel L.kD { c with digests := d } req (replaceSlice T () O G)) ω.1 c
        then (1 : ℝ) else 0) := fun d G => by
    by_cases hH : HitRun L nsalt A (j := j) (override R j fun req O =>
        kernelReply rel L.kD { c with digests := d } req (replaceSlice T () O G)) ω.1 c
    · rw [if_pos hH]
      exact abs_ind_sub_ind_le _ _
    rw [if_neg hH]
    set Z : Set X := {x | ∃ p, s p = true ∧ pt p = x}
    have hagree : AgreeOff Z (replaceSlice T () O₀ (fill s pt G d)) (replaceSlice T () O₀ G) :=
      fun x hx => by
        simp only [replaceSlice]
        split_ifs
        · exact fill_apply_of_forall_ne G d fun p hp e => hx ⟨p, hp, e⟩
        · rfl
    have hrun : L.run req₀ (replaceSlice T () O₀ (fill s pt G d)) c.main c.salts d =
        L.run req₀ (replaceSlice T () O₀ G) c.main c.salts d :=
      hL.run_oracle req₀ _ _ c.main c.salts d fun x hx => by
        refine hagree x ?_
        rintro ⟨p, hp, rfl⟩
        rcases hx with hx | ⟨a, ha, hx⟩ | ⟨q, hq, hx⟩
        · simp only [pt, hL.point_salt] at hx
          cases hx
        · simp only [pt, hL.point_salt] at hx
          exact salts_not_pub_of_not_saltBad _ hj hsb p (Option.some_injective _ hx ▸ ha)
        · simp only [pt, hL.point_salt] at hx
          have hpq := salts_injective_of_not_saltBad _ hj hsb (Option.some_injective _ hx)
          subst hpq
          have hp' : L.hidden req₀ c.main p = true := hp
          rw [hp'] at hq
          cases hq
    -- the run with proof query `j` answered by `kD` is the run with the constant reply `rD G d`
    have hRD : ∀ k ≤ m, A.run (override R j fun req O =>
        kernelReply rel L.kD { c with digests := d } req (replaceSlice T () O G)) ω.1 k =
        A.run (override R j fun _ _ => rD G d) ω.1 k := fun k hk => by
      rw [A.run_override_eq_const R ω.1 refuseReply _ hn₀ hr₀ k hk]
      congr 2
      funext _ _
      simp only [rD, kernelReply, if_pos hrel]
      rfl
    have hpre : ∀ k, (A.run (override R j refuseReply) ω.1 k).nreq ≤ j →
        A.run (override R j fun req O =>
          kernelReply rel L.kD { c with digests := d } req (replaceSlice T () O G)) ω.1 k =
          A.run (override R j refuseReply) ω.1 k :=
      A.run_eq_of_forall_lt fun i hi => by rw [override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
    have hAO := IAlg.run_agreeOff A (R := override R j fun _ _ => rD (fill s pt G d) d)
      (R' := override R j fun _ _ => rD G d) (H := ω.1) (Z := Z) (j := j)
      (fun i hi => by rw [override_of_ne _ _ hi, override_of_ne _ _ hi])
      (fun req O => by
        simp only [override_self, rD]
        rw [hrun]
        exact ⟨rfl, hagree.reprogram _⟩)
      (fun i hi req O O' h => by
        rw [override_of_ne _ _ hi.ne']
        by_cases hiQ : i < Q
        · rw [hR, kHyb_of_ge rel L.kL L.kD _ _ hi.le hiQ]
          refine hL.kernelLocal_kL.reply_agreeOff (fun x hx => ?_) req h
          obtain ⟨p, -, rfl⟩ := hx
          refine ⟨by simp only [pt, hL.point_salt]; simp, fun a ha e => ?_, fun p' e => ?_⟩
          · simp only [pt, hL.point_salt] at e
            exact salts_not_pub_of_not_saltBad _ hj hsb p (Option.some_injective _ e ▸ ha)
          simp only [pt, hL.point_salt] at e
          exact salts_ne_of_not_saltBad _ hj hsb (i := ⟨i, hiQ⟩) hi.ne' p' p
            (Option.some_injective _ e).symm
        · rw [hR, kHyb_of_Q_le rel L.kL L.kD _ _ hiQ]
          exact ⟨rfl, h⟩)
      (fun k hk x _ hx hxZ => by
        obtain ⟨p, hp, rfl⟩ := hxZ
        refine hH ⟨k₀, hk₀, req₀, ?_, ?_, p, hp, k, hk, pt p, ?_, hL.point_salt _ _ _ _⟩
        · rw [hpre k₀ hn₀.le]
          exact hn₀
        · rw [hpre k₀ hn₀.le]
          exact hr₀
        · rw [hRD k hk.le]
          exact hx)
    exact (abs_eq_zero.2 (sub_eq_zero.2 (congrArg ind
      (A.accepts_eq_of_hist_eq hpost (hAO m le_rfl).1)))).le
  rw [Finset.expect_congr rfl fun d _ => Finset.expect_congr rfl fun G _ => by rw [hFL d G, hFD d G]]
  conv_lhs => rw [Finset.expect_comm]
  conv_rhs => rw [Finset.expect_comm]
  have hsplit : 𝔼 G : X → Y, 𝔼 d : Pos → Y, (F G (fun p => if s p then G (pt p) else d p) - F G d) =
      𝔼 G : X → Y, 𝔼 d : Pos → Y, (F (fill s pt G d) d - F G d) := by
    simp_rw [Finset.expect_sub_distrib]
    rw [expect_fill s pt hinj F]
  rw [hsplit]
  refine (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun G _ => ?_)
  exact (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun d _ => hgoal d G)

open Classical in
/-- **Steps 3 and 4**: with distinct salts, the relabelling runs of hybrids `j` and `j + 1`,
averaged over the values of proof query `j` and the relabelling function, differ by at most the
probability of `HitRun` in the second. -/
theorem abs_expect_relabel_sub_le (hL : L.Laws nsalt pub) (hpost : A.PostOracleFree)
    (ω : LTape X Y Cm Pos N Q) (hsb : ¬ SaltBad pub hj ω) :
    |𝔼 d : Pos → Y, 𝔼 G : X → Y,
        (ind (A.accepts (relabelResp rel L nsalt hj j (withDigests hj ω d) G) ω.1) -
          ind (A.accepts (relabelResp rel L nsalt hj (j + 1) (withDigests hj ω d) G) ω.1))| ≤
      𝔼 d : Pos → Y, 𝔼 G : X → Y,
        (if HitRun L nsalt A (j := j) (relabelResp rel L nsalt hj (j + 1) (withDigests hj ω d) G) ω.1
          (cj hj ω) then (1 : ℝ) else 0) := by
  simpa only [relabelResp_withDigests_self, relabelResp_withDigests_succ] using
    abs_expect_override_sub_le A hj hL hpost ω hsb

/-! #### Lenses on the tape -/

/-- The tape with the salt of position `p` of proof query `j` replaced by `a`. -/
def withSalt (ω : LTape X Y Cm Pos N Q) (p : Pos) (a : N) : LTape X Y Cm Pos N Q :=
  (ω.1, Function.update ω.2 ⟨j, hj⟩ { cj hj ω with salts := Function.update (cj hj ω).salts p a })

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
theorem cj_withSalt (ω : LTape X Y Cm Pos N Q) (p : Pos) (a : N) :
    cj hj (withSalt hj ω p a) = { cj hj ω with salts := Function.update (cj hj ω).salts p a } := by
  simp [withSalt, cj]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
theorem withSalt_salt (ω : LTape X Y Cm Pos N Q) (p : Pos) (a : N) :
    (cj hj (withSalt hj ω p a)).salts p = a := by
  rw [cj_withSalt]
  exact Function.update_self _ _ _

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
theorem withSalt_self (ω : LTape X Y Cm Pos N Q) (p : Pos) :
    withSalt hj ω p ((cj hj ω).salts p) = ω := by
  unfold withSalt
  rw [Function.update_eq_self]
  have : { cj hj ω with salts := (cj hj ω).salts } = cj hj ω := rfl
  rw [this, Function.update_eq_self]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
theorem withSalt_withSalt (ω : LTape X Y Cm Pos N Q) (p : Pos) (a b : N) :
    withSalt hj (withSalt hj ω p a) p b = withSalt hj ω p b := by
  rw [show withSalt hj (withSalt hj ω p a) p b = ((withSalt hj ω p a).1,
      Function.update (withSalt hj ω p a).2 ⟨j, hj⟩ { cj hj (withSalt hj ω p a) with
        salts := Function.update (cj hj (withSalt hj ω p a)).salts p b }) from rfl, cj_withSalt]
  unfold withSalt
  simp only [Function.update_idem]

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
@[simp] theorem withSalt_fst (ω : LTape X Y Cm Pos N Q) (p : Pos) (a : N) :
    (withSalt hj ω p a).1 = ω.1 := rfl

omit [Nonempty Y] [Nonempty Cm] [DecidableEq N] in
theorem expect_withSalt (p : Pos) (f : LTape X Y Cm Pos N Q → ℝ) :
    𝔼 ω, 𝔼 a : N, f (withSalt hj ω p a) = 𝔼 ω, f ω :=
  expect_lens (withSalt hj · p) (fun ω => (cj hj ω).salts p) (withSalt_salt hj · p)
    (withSalt_self hj · p) (withSalt_withSalt hj · p) f

omit [Nonempty Cm] [DecidableEq N] [Nonempty N] in
theorem expect_withDigests (f : LTape X Y Cm Pos N Q → ℝ) :
    𝔼 ω, 𝔼 d : Pos → Y, f (withDigests hj ω d) = 𝔼 ω, f ω :=
  expect_lens (withDigests hj) (fun ω => (cj hj ω).digests)
    (fun ω a => by simp only [withDigests, cj, Function.update_self])
    (fun ω => by
      refine Prod.ext rfl (funext fun i => ?_)
      by_cases hi : i = ⟨j, hj⟩
      · subst hi
        simp only [withDigests, cj, Function.update_self]
      · simp only [withDigests, Function.update_of_ne hi])
    (fun ω a b => by
      refine Prod.ext rfl (funext fun i => ?_)
      by_cases hi : i = ⟨j, hj⟩
      · subst hi
        simp only [withDigests, cj, Function.update_self]
      · simp only [withDigests, Function.update_of_ne hi]) f

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- Away from proof query `j` the hybrids do not read proof query `j`'s coins. -/
theorem kHyb_update_of_ne {j' i : ℕ} (hi : i ≠ j) (c : Fin Q → LeafCoins Cm Pos N Y)
    (x : LeafCoins Cm Pos N Y) :
    kHyb rel L.kL L.kD j' (Function.update c ⟨j, hj⟩ x) (Function.update c ⟨j, hj⟩ x) i =
      kHyb rel L.kL L.kD j' c c i := by
  have := congrFun (override_kHyb_update rel L.kL L.kD hj j' c c x x refuseReply) i
  simpa only [override, if_neg hi] using this

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
theorem lBase_update (c : Fin Q → LeafCoins Cm Pos N Y) (H₀ : X → Y) (x : LeafCoins Cm Pos N Y) :
    lBase rel L (Q := Q) (j := j) (H₀, Function.update c ⟨j, hj⟩ x) = lBase rel L (j := j) (H₀, c) :=
  override_kHyb_update rel L.kL L.kD hj j c c x x refuseReply

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq Pos]
  [Fintype N] [DecidableEq N] [Nonempty N] in
/-- Hybrid `j + 1` agrees with the base responder below proof query `j`. -/
theorem kHyb_succ_eq_lBase {i : ℕ} (hi : i < j) (ω : LTape X Y Cm Pos N Q) :
    kHyb rel L.kL L.kD (j + 1) ω.2 ω.2 i = lBase rel L ω (j := j) i := by
  rw [lBase, override_of_ne _ _ hi.ne, kHyb_succ_of_ne rel L.kL L.kD ω.2 ω.2 hi.ne]

/-! #### The bad events -/

/-- The indicator of an event implying some `P i` is at most the sum of the indicators of the
`P i`. -/
theorem ite_le_sum_of_imp {ι : Type*} [Fintype ι] {E : Prop} [Decidable E] (P : ι → Prop)
    [DecidablePred P] (h : E → ∃ i, P i) :
    (if E then (1 : ℝ) else 0) ≤ ∑ i, if P i then (1 : ℝ) else 0 := by
  split_ifs with hE
  · obtain ⟨i, hi⟩ := h hE
    calc (1 : ℝ) = if P i then 1 else 0 := by rw [if_pos hi]
      _ ≤ ∑ i, if P i then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun i => if P i then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

open Classical in
/-- **`PreHit` has probability at most `t |Pos| / |N|`**: the run before proof query `j` does not read
proof query `j`'s salts. -/
theorem expect_preHit_le (hA : A.Budget t) :
    𝔼 ω : LTape X Y Cm Pos N Q, (if PreHit rel L nsalt A hj ω then (1 : ℝ) else 0) ≤
      t * Fintype.card Pos / Fintype.card N := by
  have hpt : ∀ ω : LTape X Y Cm Pos N Q, (if PreHit rel L nsalt A hj ω then (1 : ℝ) else 0) ≤
      ∑ p, (if ∃ k < m, ∃ x, A.next (A.run (lBase rel L ω (j := j)) ω.1 k).hist = .query x ∧
        nsalt x = some ((cj hj ω).salts p) then (1 : ℝ) else 0) := fun ω => by
    exact ite_le_sum_of_imp _ fun ⟨k, hk, x, hx, p, hp⟩ => ⟨p, k, hk, x, hx, hp⟩
  have hp1 : ∀ p : Pos, 𝔼 ω : LTape X Y Cm Pos N Q,
      (if ∃ k < m, ∃ x, A.next (A.run (lBase rel L ω (j := j)) ω.1 k).hist = .query x ∧
        nsalt x = some ((cj hj ω).salts p) then (1 : ℝ) else 0) ≤ t / Fintype.card N := fun p => by
    rw [← expect_withSalt hj p]
    refine (Finset.expect_le_expect fun ω _ => ?_).trans_eq (Finset.expect_const Finset.univ_nonempty _)
    have hb : ∀ a, lBase rel L (withSalt hj ω p a) (j := j) = lBase rel L ω (j := j) := fun a =>
      lBase_update hj ω.2 ω.1 _
    simp only [hb, withSalt_salt, withSalt_fst]
    refine (expect_ite_exists_query_le nsalt
      (fun k => A.next (A.run (lBase rel L ω (j := j)) ω.1 k).hist) m).trans ?_
    gcongr
    exact_mod_cast hA _ _
  calc 𝔼 ω : LTape X Y Cm Pos N Q, (if PreHit rel L nsalt A hj ω then (1 : ℝ) else 0)
      ≤ 𝔼 ω : LTape X Y Cm Pos N Q, ∑ p, (if ∃ k < m, ∃ x,
          A.next (A.run (lBase rel L ω (j := j)) ω.1 k).hist = .query x ∧
            nsalt x = some ((cj hj ω).salts p) then (1 : ℝ) else 0) :=
        Finset.expect_le_expect fun ω _ => hpt ω
    _ = ∑ p, 𝔼 ω : LTape X Y Cm Pos N Q, (if ∃ k < m, ∃ x,
          A.next (A.run (lBase rel L ω (j := j)) ω.1 k).hist = .query x ∧
            nsalt x = some ((cj hj ω).salts p) then (1 : ℝ) else 0) := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _p : Pos, (t : ℝ) / Fintype.card N := Finset.sum_le_sum fun p _ => hp1 p
    _ = t * Fintype.card Pos / Fintype.card N := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

open Classical in
/-- **A salt of proof query `j` collides with another salt of the tape** with probability at most
`Q |Pos|² / |N|`. -/
theorem expect_collide_le :
    𝔼 ω : LTape X Y Cm Pos N Q, (if ∃ i : Fin Q, ∃ p q : Pos, (i, p) ≠ (⟨j, hj⟩, q) ∧
      (ω.2 i).salts p = (cj hj ω).salts q then (1 : ℝ) else 0) ≤
      Q * Fintype.card Pos ^ 2 / Fintype.card N := by
  have hpt : ∀ ω : LTape X Y Cm Pos N Q, (if ∃ i : Fin Q, ∃ p q : Pos, (i, p) ≠ (⟨j, hj⟩, q) ∧
      (ω.2 i).salts p = (cj hj ω).salts q then (1 : ℝ) else 0) ≤
      ∑ q : Pos, ∑ ip : Fin Q × Pos, (if ip ≠ (⟨j, hj⟩, q) ∧
        (ω.2 ip.1).salts ip.2 = (cj hj ω).salts q then (1 : ℝ) else 0) := fun ω => by
    refine (ite_le_sum_of_imp (fun q : Pos => ∃ ip : Fin Q × Pos,
      ip ≠ (⟨j, hj⟩, q) ∧ (ω.2 ip.1).salts ip.2 = (cj hj ω).salts q)
      fun ⟨i, p, q, h, e⟩ => ⟨q, (i, p), h, e⟩).trans
      (Finset.sum_le_sum fun q _ => ite_le_sum_of_imp _ fun h => h)
  have hp1 : ∀ (q : Pos) (ip : Fin Q × Pos), 𝔼 ω : LTape X Y Cm Pos N Q,
      (if ip ≠ (⟨j, hj⟩, q) ∧ (ω.2 ip.1).salts ip.2 = (cj hj ω).salts q then (1 : ℝ) else 0) ≤
        1 / Fintype.card N := fun q ip => by
    rw [← expect_withSalt hj q]
    refine (Finset.expect_le_expect fun ω _ => ?_).trans_eq (Finset.expect_const Finset.univ_nonempty _)
    by_cases hne : ip = (⟨j, hj⟩, q)
    · simp only [hne, ne_eq, not_true_eq_false, false_and, if_false, Finset.expect_const_zero]
      positivity
    have hsame : ∀ a, ((withSalt hj ω q a).2 ip.1).salts ip.2 = (ω.2 ip.1).salts ip.2 := fun a => by
      by_cases hi : ip.1 = ⟨j, hj⟩
      · have hp : ip.2 ≠ q := fun e => hne (Prod.ext hi e)
        simp [withSalt, hi, Function.update_of_ne hp, cj]
      · simp [withSalt, Function.update_of_ne hi]
    simp only [hsame, withSalt_salt, ne_eq, hne, not_false_eq_true, true_and]
    have := expect_ite_eq_some_le (some ((ω.2 ip.1).salts ip.2))
    simpa only [Option.some.injEq] using this
  calc 𝔼 ω : LTape X Y Cm Pos N Q, (if ∃ i : Fin Q, ∃ p q : Pos, (i, p) ≠ (⟨j, hj⟩, q) ∧
        (ω.2 i).salts p = (cj hj ω).salts q then (1 : ℝ) else 0)
      ≤ 𝔼 ω : LTape X Y Cm Pos N Q, ∑ q : Pos, ∑ ip : Fin Q × Pos, (if ip ≠ (⟨j, hj⟩, q) ∧
          (ω.2 ip.1).salts ip.2 = (cj hj ω).salts q then (1 : ℝ) else 0) :=
        Finset.expect_le_expect fun ω _ => hpt ω
    _ = ∑ q : Pos, ∑ ip : Fin Q × Pos, 𝔼 ω : LTape X Y Cm Pos N Q, (if ip ≠ (⟨j, hj⟩, q) ∧
          (ω.2 ip.1).salts ip.2 = (cj hj ω).salts q then (1 : ℝ) else 0) := by
        rw [Finset.expect_sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _q : Pos, ∑ _ip : Fin Q × Pos, (1 : ℝ) / Fintype.card N :=
        Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun ip _ => hp1 q ip
    _ = Q * Fintype.card Pos ^ 2 / Fintype.card N := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

open Classical in
/-- **A salt of proof query `j` is public** with probability at most `|Pos| |pub| / |N|`. -/
theorem expect_pubSalt_le :
    𝔼 ω : LTape X Y Cm Pos N Q, (if ∃ q, (cj hj ω).salts q ∈ pub then (1 : ℝ) else 0) ≤
      Fintype.card Pos * pub.card / Fintype.card N := by
  have hp1 : ∀ q : Pos, 𝔼 ω : LTape X Y Cm Pos N Q,
      (if (cj hj ω).salts q ∈ pub then (1 : ℝ) else 0) = pub.card / Fintype.card N := fun q => by
    rw [← expect_withSalt hj q]
    simp only [withSalt_salt]
    rw [Finset.expect_const Finset.univ_nonempty, Fintype.expect_eq_sum_div_card, Finset.sum_boole]
    congr 2
    simp
  calc 𝔼 ω : LTape X Y Cm Pos N Q, (if ∃ q, (cj hj ω).salts q ∈ pub then (1 : ℝ) else 0)
      ≤ 𝔼 ω : LTape X Y Cm Pos N Q, ∑ q, (if (cj hj ω).salts q ∈ pub then (1 : ℝ) else 0) :=
        Finset.expect_le_expect fun ω _ => ite_le_sum_of_imp _ fun h => h
    _ = ∑ q, 𝔼 ω : LTape X Y Cm Pos N Q, (if (cj hj ω).salts q ∈ pub then (1 : ℝ) else 0) :=
        Finset.expect_sum_comm _ _ _
    _ = Fintype.card Pos * pub.card / Fintype.card N := by
        simp only [hp1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

open Classical in
/-- **`SaltBad` has probability at most `(Q |Pos|² + |Pos| |pub|) / |N|`.** -/
theorem expect_saltBad_le :
    𝔼 ω : LTape X Y Cm Pos N Q, (if SaltBad pub hj ω then (1 : ℝ) else 0) ≤
      (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card) / Fintype.card N := by
  rw [add_div]
  refine (Finset.expect_le_expect fun ω _ => (?_ : (if SaltBad pub hj ω then (1 : ℝ) else 0) ≤
    (if ∃ i : Fin Q, ∃ p q : Pos, (i, p) ≠ (⟨j, hj⟩, q) ∧ (ω.2 i).salts p = (cj hj ω).salts q
      then (1 : ℝ) else 0) + (if ∃ q, (cj hj ω).salts q ∈ pub then (1 : ℝ) else 0))).trans ?_
  · unfold SaltBad
    split_ifs <;> simp_all
  · rw [Finset.expect_add_distrib]
    exact add_le_add (expect_collide_le hj) (expect_pubSalt_le (pub := pub) hj)

open Classical in
/-- **`HitRun` in hybrid `j + 1` has probability at most `t |Pos| / |N|`**: proof query `j`'s reply
there does not read the salts of its hidden positions, so the run does not depend on them. -/
theorem expect_hitRun_le (hL : L.Laws nsalt pub) (hA : A.Budget t) :
    𝔼 ω : LTape X Y Cm Pos N Q, (if HitRun L nsalt A (j := j)
      (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) ω.1 (cj hj ω) then (1 : ℝ) else 0) ≤
      t * Fintype.card Pos / Fintype.card N := by
  set Hp : Pos → LTape X Y Cm Pos N Q → Prop := fun p ω =>
    ∃ k₀ < m, ∃ req, (A.run (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) ω.1 k₀).nreq = j ∧
      A.next (A.run (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) ω.1 k₀).hist = .request req ∧
      L.hidden req (cj hj ω).main p = true ∧
      ∃ k < m, ∃ x, A.next (A.run (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) ω.1 k).hist = .query x ∧
        nsalt x = some ((cj hj ω).salts p) with hHp
  have hpt : ∀ ω : LTape X Y Cm Pos N Q, (if HitRun L nsalt A (j := j)
      (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) ω.1 (cj hj ω) then (1 : ℝ) else 0) ≤
      ∑ p, (if Hp p ω then (1 : ℝ) else 0) := fun ω =>
    ite_le_sum_of_imp _ fun ⟨k₀, hk₀, req, hn, hr, p, hp, k, hk, x, hx, hs⟩ =>
      ⟨p, k₀, hk₀, req, hn, hr, hp, k, hk, x, hx, hs⟩
  have hp1 : ∀ p : Pos, 𝔼 ω : LTape X Y Cm Pos N Q, (if Hp p ω then (1 : ℝ) else 0) ≤
      t / Fintype.card N := fun p => by
    rw [← expect_withSalt hj p]
    refine (Finset.expect_le_expect fun ω _ => ?_).trans_eq (Finset.expect_const Finset.univ_nonempty _)
    set R := kHyb rel L.kL L.kD (j + 1) ω.2 ω.2 with hR
    have hRa : ∀ a, kHyb rel L.kL L.kD (j + 1) (withSalt hj ω p a).2 (withSalt hj ω p a).2 =
        kHyb rel L.kL L.kD (j + 1) (Function.update ω.2 ⟨j, hj⟩
          { cj hj ω with salts := Function.update (cj hj ω).salts p a })
          (Function.update ω.2 ⟨j, hj⟩ { cj hj ω with salts := Function.update (cj hj ω).salts p a }) :=
      fun a => rfl
    -- the base run, common to every value of the salt
    have hbaseR : ∀ k, (A.run R ω.1 k).nreq ≤ j → A.run (lBase rel L ω (j := j)) ω.1 k = A.run R ω.1 k :=
      A.run_eq_of_forall_lt fun i hi => kHyb_succ_eq_lBase hi ω
    have hbaseRa : ∀ a k, (A.run (kHyb rel L.kL L.kD (j + 1) (withSalt hj ω p a).2
        (withSalt hj ω p a).2) ω.1 k).nreq ≤ j →
        A.run (lBase rel L ω (j := j)) ω.1 k =
          A.run (kHyb rel L.kL L.kD (j + 1) (withSalt hj ω p a).2 (withSalt hj ω p a).2) ω.1 k :=
      fun a => A.run_eq_of_forall_lt fun i hi => by
        rw [kHyb_succ_eq_lBase hi (withSalt hj ω p a)]
        exact congrFun (lBase_update hj ω.2 ω.1 _) i
    by_cases hc : ∃ k₀ < m, ∃ req, (A.run (lBase rel L ω (j := j)) ω.1 k₀).nreq = j ∧
        A.next (A.run (lBase rel L ω (j := j)) ω.1 k₀).hist = .request req ∧
        L.hidden req (cj hj ω).main p = true
    · obtain ⟨k₀, hk₀, req₀, hn₀, hr₀, hh₀⟩ := hc
      -- the run does not depend on the salt
      have hinv : ∀ a, ∀ k ≤ m,
          A.run R ω.1 k = A.run (kHyb rel L.kL L.kD (j + 1) (withSalt hj ω p a).2
            (withSalt hj ω p a).2) ω.1 k := fun a => by
        refine A.run_eq_of_forall_ne (j := j) (fun i hi => ?_) (fun k _ req hn hr => ?_)
        · rw [hRa, kHyb_update_of_ne hj hi]
        · have hb := hbaseR k hn.le
          have hkk : k = k₀ := A.eq_of_request_of_nreq_eq (by rw [hb]; exact hr) hr₀
            (by rw [hb, hn, hn₀])
          subst hkk
          have hrr : req = req₀ := by
            rw [← hb, hr₀] at hr
            exact (Action.request.inj hr).symm
          subst hrr
          rw [hRa, hR, kHyb_of_lt rel L.kL L.kD _ _ (Nat.lt_succ_self j) hj,
            kHyb_of_lt rel L.kL L.kD _ _ (Nat.lt_succ_self j) hj]
          simp only [Function.update_self]
          unfold kernelReply LeafKernel.kD
          rw [hL.run_salts req _ (cj hj ω).main (cj hj ω).salts (Function.update (cj hj ω).salts p a)
            (cj hj ω).digests fun q hq => ?_]
          have hqp : q ≠ p := fun e => by rw [e, hh₀] at hq; cases hq
          rw [Function.update_of_ne hqp]
      have hle : ∀ a, (if Hp p (withSalt hj ω p a) then (1 : ℝ) else 0) ≤
          (if ∃ k < m, ∃ x, A.next (A.run R ω.1 k).hist = .query x ∧ nsalt x = some a
            then (1 : ℝ) else 0) := fun a => by
        by_cases h : Hp p (withSalt hj ω p a)
        · obtain ⟨-, -, -, -, -, -, k, hk, x, hx, hs⟩ := h
          rw [withSalt_fst] at hx
          have h2 : ∃ k < m, ∃ x, A.next (A.run R ω.1 k).hist = .query x ∧ nsalt x = some a :=
            ⟨k, hk, x, by rw [hinv a k hk.le]; exact hx, by rwa [withSalt_salt] at hs⟩
          rw [if_pos h2]
          split_ifs <;> norm_num
        · rw [if_neg h]
          split_ifs <;> norm_num
      refine (Finset.expect_le_expect fun a _ => hle a).trans ?_
      refine (expect_ite_exists_query_le nsalt (fun k => A.next (A.run R ω.1 k).hist) m).trans ?_
      gcongr
      exact_mod_cast hA _ _
    · have hz : ∀ a, ¬ Hp p (withSalt hj ω p a) := fun a h => by
        obtain ⟨k₀, hk₀, req, hn, hr, hh, -⟩ := h
        rw [withSalt_fst] at hn hr
        have hb := hbaseRa a k₀ hn.le
        refine hc ⟨k₀, hk₀, req, by rw [hb]; exact hn, by rw [hb]; exact hr, ?_⟩
        rwa [cj_withSalt] at hh
      simp only [hz, if_false, Finset.expect_const_zero]
      positivity
  calc 𝔼 ω : LTape X Y Cm Pos N Q, (if HitRun L nsalt A (j := j)
        (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) ω.1 (cj hj ω) then (1 : ℝ) else 0)
      ≤ 𝔼 ω : LTape X Y Cm Pos N Q, ∑ p, (if Hp p ω then (1 : ℝ) else 0) :=
        Finset.expect_le_expect fun ω _ => hpt ω
    _ = ∑ p, 𝔼 ω : LTape X Y Cm Pos N Q, (if Hp p ω then (1 : ℝ) else 0) :=
        Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _p : Pos, (t : ℝ) / Fintype.card N := Finset.sum_le_sum fun p _ => hp1 p
    _ = t * Fintype.card Pos / Fintype.card N := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

omit [Fintype Cm] [Nonempty Cm] [Fintype Pos] [DecidableEq N] [Nonempty N] in
/-- **Relabelling the inputs of proof query `j`'s salts on the tape** (exact). -/
theorem expect_relabel_tape [Fintype Cm] [Fintype Pos] (f : (Fin Q → LeafCoins Cm Pos N Y) → (X → Y) → ℝ) :
    𝔼 ω : LTape X Y Cm Pos N Q, 𝔼 G : X → Y,
        f ω.2 (replaceSlice (inSalts nsalt (cj hj ω).salts) () ω.1 G) =
      𝔼 ω : LTape X Y Cm Pos N Q, f ω.2 ω.1 := by
  rw [expect_prod_eq, expect_prod_eq, Finset.expect_comm, Finset.expect_comm (f := fun H c => f c H)]
  refine Finset.expect_congr rfl fun c _ => ?_
  exact expect_replaceSlice (inSalts nsalt (c ⟨j, hj⟩).salts) () (f c)

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Cm] [Nonempty Cm] [Fintype Pos]
  [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N] in
theorem hitRun_withDigests (R : Responder X Y Stmt Wit Proof) (H₀ : X → Y)
    (c : LeafCoins Cm Pos N Y) (d : Pos → Y) :
    HitRun L nsalt A (j := j) R H₀ { c with digests := d } ↔ HitRun L nsalt A (j := j) R H₀ c :=
  Iff.rfl

include hj in
open Classical in
/-- **One step of the leaf hybrid**: hybrids `j` and `j + 1` differ by at most
`(4 t |Pos| + 4 Q |Pos|²) / |N|` for an algorithm with a budget of `t` queries and an output that
does not read the final oracle. -/
theorem abs_lHybProb_sub_le (hL : L.Laws nsalt pub) (hA : A.Budget t) (hpost : A.PostOracleFree) :
    |lHybProb rel L A Q j - lHybProb rel L A Q (j + 1)| ≤
      (4 * t * Fintype.card Pos + 4 * (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card)) /
        Fintype.card N := by
  set rep : LTape X Y Cm Pos N Q → (X → Y) → X → Y := fun ω G =>
    replaceSlice (inSalts nsalt (cj hj ω).salts) () ω.1 G with hrep
  set Bad : LTape X Y Cm Pos N Q → Prop := fun ω => PreHit rel L nsalt A hj ω ∨ SaltBad pub hj ω
  set a : LTape X Y Cm Pos N Q → (X → Y) → ℝ := fun ω G =>
    ind (A.accepts (kHyb rel L.kL L.kD j ω.2 ω.2) (rep ω G))
  set b : LTape X Y Cm Pos N Q → (X → Y) → ℝ := fun ω G =>
    ind (A.accepts (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) (rep ω G))
  set aL : LTape X Y Cm Pos N Q → (X → Y) → ℝ := fun ω G =>
    ind (A.accepts (relabelResp rel L nsalt hj j ω G) ω.1)
  set bD : LTape X Y Cm Pos N Q → (X → Y) → ℝ := fun ω G =>
    ind (A.accepts (relabelResp rel L nsalt hj (j + 1) ω G) ω.1)
  set Hit : LTape X Y Cm Pos N Q → Prop := fun ω =>
    HitRun L nsalt A (j := j) (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) ω.1 (cj hj ω)
  have ha : lHybProb rel L A Q j = 𝔼 ω, 𝔼 G, a ω G :=
    (expect_relabel_tape (nsalt := nsalt) hj fun c H' => ind (A.accepts (kHyb rel L.kL L.kD j c c) H')).symm
  have hb : lHybProb rel L A Q (j + 1) = 𝔼 ω, 𝔼 G, b ω G :=
    (expect_relabel_tape (nsalt := nsalt) hj fun c H' => ind (A.accepts (kHyb rel L.kL L.kD (j + 1) c c) H')).symm
  have hcouple : ∀ {j'} (hj' : j' = j ∨ j' = j + 1) (ω : LTape X Y Cm Pos N Q) (G : X → Y),
      ¬ Bad ω → ind (A.accepts (kHyb rel L.kL L.kD j' ω.2 ω.2) (rep ω G)) =
        ind (A.accepts (relabelResp rel L nsalt hj j' ω G) ω.1) := fun hj' ω G hB => by
    have hB' : ¬ PreHit rel L nsalt A hj ω ∧ ¬ SaltBad pub hj ω := not_or.1 hB
    rw [A.accepts_eq_of_hist_eq hpost (hist_relabel A hj hL hj' ω G hB'.1 hB'.2 m le_rfl).1]
  have hpa : ∀ ω G, |a ω G - aL ω G| ≤ if Bad ω then (1 : ℝ) else 0 := fun ω G => by
    by_cases hB : Bad ω
    · rw [if_pos hB]
      exact abs_ind_sub_ind_le _ _
    · rw [if_neg hB, show a ω G = aL ω G from hcouple (Or.inl rfl) ω G hB, sub_self, abs_zero]
  have hpb : ∀ ω G, |bD ω G - b ω G| ≤ if Bad ω then (1 : ℝ) else 0 := fun ω G => by
    by_cases hB : Bad ω
    · rw [if_pos hB]
      exact abs_ind_sub_ind_le _ _
    · rw [if_neg hB, show b ω G = bD ω G from hcouple (Or.inr rfl) ω G hB, sub_self, abs_zero]
  -- the middle term
  have hHit : ∀ ω (d : Pos → Y) G,
      (if HitRun L nsalt A (j := j) (relabelResp rel L nsalt hj (j + 1) (withDigests hj ω d) G) ω.1
        (cj hj ω) then (1 : ℝ) else 0) ≤
      (if HitRun L nsalt A (j := j) (kHyb rel L.kL L.kD (j + 1) (withDigests hj ω d).2
          (withDigests hj ω d).2) (rep (withDigests hj ω d) G) (cj hj (withDigests hj ω d))
        then (1 : ℝ) else 0) + (if Bad (withDigests hj ω d) then (1 : ℝ) else 0) := fun ω d G => by
    by_cases hB : Bad (withDigests hj ω d)
    · rw [if_pos hB]
      split_ifs <;> norm_num
    rw [if_neg hB, add_zero]
    have hB' : ¬ PreHit rel L nsalt A hj (withDigests hj ω d) ∧ ¬ SaltBad pub hj (withDigests hj ω d) :=
      not_or.1 hB
    have hh := hist_relabel A hj hL (Or.inr rfl) (withDigests hj ω d) G hB'.1 hB'.2
    have hiff := hitRun_congr L nsalt A (j := j) hh (cj hj ω)
    split_ifs with h1 h2
    · exact le_rfl
    · rw [cj_withDigests] at h2
      exact absurd ((hitRun_withDigests (L := L) (nsalt := nsalt) A (j := j) _ _ (cj hj ω) d).2 (hiff.2 h1)) h2
    · norm_num
    · norm_num
  have hmid : |𝔼 ω, 𝔼 G, (aL ω G - bD ω G)| ≤
      𝔼 ω, ((if SaltBad pub hj ω then (1 : ℝ) else 0) + (if Bad ω then (1 : ℝ) else 0) +
        (if Hit ω then (1 : ℝ) else 0)) := by
    rw [← expect_withDigests hj (fun ω => 𝔼 G, (aL ω G - bD ω G))]
    have hstep : ∀ ω : LTape X Y Cm Pos N Q,
        |𝔼 d : Pos → Y, 𝔼 G : X → Y, (aL (withDigests hj ω d) G - bD (withDigests hj ω d) G)| ≤
          (if SaltBad pub hj ω then (1 : ℝ) else 0) + 𝔼 d : Pos → Y, 𝔼 G : X → Y,
            (if HitRun L nsalt A (j := j) (relabelResp rel L nsalt hj (j + 1) (withDigests hj ω d) G)
              ω.1 (cj hj ω) then (1 : ℝ) else 0) := fun ω => by
      have hnn : 0 ≤ 𝔼 d : Pos → Y, 𝔼 G : X → Y,
          (if HitRun L nsalt A (j := j) (relabelResp rel L nsalt hj (j + 1) (withDigests hj ω d) G)
            ω.1 (cj hj ω) then (1 : ℝ) else 0) :=
        Finset.expect_nonneg fun _ _ => Finset.expect_nonneg fun _ _ => by split_ifs <;> norm_num
      by_cases hsb : SaltBad pub hj ω
      · rw [if_pos hsb]
        refine le_trans ?_ (le_add_of_nonneg_right hnn)
        refine (Finset.abs_expect_le _ _).trans ?_
        refine (Finset.expect_le_expect fun d _ => (Finset.abs_expect_le _ _).trans
          (Finset.expect_le_expect fun G _ => abs_ind_sub_ind_le _ _ :
            𝔼 G : X → Y, |aL (withDigests hj ω d) G - bD (withDigests hj ω d) G| ≤ 𝔼 _G : X → Y, (1 : ℝ))).trans ?_
        simp only [Finset.expect_const Finset.univ_nonempty, le_refl]
      · rw [if_neg hsb, zero_add]
        exact abs_expect_relabel_sub_le A hj hL hpost ω hsb
    refine (Finset.abs_expect_le _ _).trans ((Finset.expect_le_expect fun ω _ => hstep ω).trans ?_)
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib, Finset.expect_add_distrib, add_assoc]
    gcongr
    -- the `HitRun` term
    calc 𝔼 ω : LTape X Y Cm Pos N Q, 𝔼 d : Pos → Y, 𝔼 G : X → Y,
          (if HitRun L nsalt A (j := j) (relabelResp rel L nsalt hj (j + 1) (withDigests hj ω d) G)
            ω.1 (cj hj ω) then (1 : ℝ) else 0)
        ≤ 𝔼 ω : LTape X Y Cm Pos N Q, 𝔼 d : Pos → Y, 𝔼 G : X → Y,
          ((if HitRun L nsalt A (j := j) (kHyb rel L.kL L.kD (j + 1) (withDigests hj ω d).2
              (withDigests hj ω d).2) (rep (withDigests hj ω d) G) (cj hj (withDigests hj ω d))
            then (1 : ℝ) else 0) + (if Bad (withDigests hj ω d) then (1 : ℝ) else 0)) :=
          Finset.expect_le_expect fun ω _ => Finset.expect_le_expect fun d _ =>
            Finset.expect_le_expect fun G _ => hHit ω d G
      _ = 𝔼 ω : LTape X Y Cm Pos N Q, 𝔼 G : X → Y,
          ((if HitRun L nsalt A (j := j) (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) (rep ω G) (cj hj ω)
            then (1 : ℝ) else 0) + (if Bad ω then (1 : ℝ) else 0)) :=
          expect_withDigests hj (fun ω => 𝔼 G : X → Y,
            ((if HitRun L nsalt A (j := j) (kHyb rel L.kL L.kD (j + 1) ω.2 ω.2) (rep ω G) (cj hj ω)
              then (1 : ℝ) else 0) + (if Bad ω then (1 : ℝ) else 0)))
      _ = 𝔼 ω : LTape X Y Cm Pos N Q, ((if Bad ω then (1 : ℝ) else 0) + (if Hit ω then (1 : ℝ) else 0)) := by
          simp_rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
          rw [expect_relabel_tape (nsalt := nsalt) hj (fun c H' => if HitRun L nsalt A (j := j)
            (kHyb rel L.kL L.kD (j + 1) c c) H' (c ⟨j, hj⟩) then (1 : ℝ) else 0), add_comm]
      _ = _ := by rw [Finset.expect_add_distrib]
  -- assembling
  have hsplit : 𝔼 ω, 𝔼 G, a ω G - 𝔼 ω, 𝔼 G, b ω G =
      𝔼 ω, 𝔼 G, (a ω G - aL ω G) + 𝔼 ω, 𝔼 G, (aL ω G - bD ω G) + 𝔼 ω, 𝔼 G, (bD ω G - b ω G) := by
    simp only [← Finset.expect_add_distrib, ← Finset.expect_sub_distrib]
    refine Finset.expect_congr rfl fun ω _ => Finset.expect_congr rfl fun G _ => ?_
    ring
  have hbad : 𝔼 ω : LTape X Y Cm Pos N Q, (if Bad ω then (1 : ℝ) else 0) ≤
      t * Fintype.card Pos / Fintype.card N +
        (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card) / Fintype.card N := by
    refine (Finset.expect_le_expect fun ω _ => (?_ : (if Bad ω then (1 : ℝ) else 0) ≤
      (if PreHit rel L nsalt A hj ω then (1 : ℝ) else 0) + (if SaltBad pub hj ω then (1 : ℝ) else 0))).trans ?_
    · by_cases h1 : PreHit rel L nsalt A hj ω <;> by_cases h2 : SaltBad pub hj ω <;>
        simp [Bad, h1, h2]
    · rw [Finset.expect_add_distrib]
      exact add_le_add (expect_preHit_le A hj hA) (expect_saltBad_le (pub := pub) hj)
  have hE1 : |𝔼 ω, 𝔼 G, (a ω G - aL ω G)| ≤ 𝔼 ω : LTape X Y Cm Pos N Q, (if Bad ω then (1 : ℝ) else 0) :=
    (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun ω _ =>
      (Finset.abs_expect_le _ _).trans ((Finset.expect_le_expect fun G _ => hpa ω G).trans_eq
        (Finset.expect_const Finset.univ_nonempty _)))
  have hE3 : |𝔼 ω, 𝔼 G, (bD ω G - b ω G)| ≤ 𝔼 ω : LTape X Y Cm Pos N Q, (if Bad ω then (1 : ℝ) else 0) :=
    (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun ω _ =>
      (Finset.abs_expect_le _ _).trans ((Finset.expect_le_expect fun G _ => hpb ω G).trans_eq
        (Finset.expect_const Finset.univ_nonempty _)))
  have hsb := expect_saltBad_le (X := X) (Y := Y) (Cm := Cm) (Pos := Pos) (N := N) (pub := pub) hj
  have hhit := expect_hitRun_le (rel := rel) (L := L) (nsalt := nsalt) A hj hL hA
  rw [ha, hb, hsplit]
  refine (abs_add_three _ _ _).trans ?_
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib] at hmid
  have hfin : (4 * t * Fintype.card Pos + 4 * (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card) : ℝ) /
      Fintype.card N =
      3 * (t * Fintype.card Pos / Fintype.card N +
        (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card) / Fintype.card N) +
        (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card) / Fintype.card N +
          t * Fintype.card Pos / Fintype.card N := by
    ring
  rw [hfin]
  linarith

/-- The sum of `Q` equal step errors. -/
theorem abs_lHybProb_zero_sub_le (hL : L.Laws nsalt pub) {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (hA : A.Budget t) (hpost : A.PostOracleFree) (Q : ℕ) :
    |lHybProb rel L A Q 0 - lHybProb rel L A Q Q| ≤
      Q * ((4 * t * Fintype.card Pos + 4 * (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card)) /
        Fintype.card N) := by
  rw [← Finset.sum_range_sub' (fun j => lHybProb rel L A Q j)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun j hj => abs_lHybProb_sub_le A (Finset.mem_range.1 hj) hL hA hpost).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Hidden leaf digests against query-bounded classical adversaries** (module docstring): for a
leaf kernel with its laws, every classical algorithm with a budget of `t` queries whose output
does not read the final oracle outputs `true` against the games of the honest-digest kernel `kL`
and the uniform-digest kernel `kD`, with `Q` proof queries, with probabilities at most
`Q (4 t |Pos| + 4 Q |Pos|²) / |N|` apart. -/
theorem abs_toReal_acceptProb_progEnv_kL_sub_kD_le (hL : L.Laws nsalt pub) {m t : ℕ}
    (A : IAlg X Y Stmt Wit Proof m) (hA : A.Budget t) (hpost : A.PostOracleFree) (Q : ℕ) :
    |(A.acceptProb (progEnv rel L.kL Q)).toReal - (A.acceptProb (progEnv rel L.kD Q)).toReal| ≤
      Q * ((4 * t * Fintype.card Pos + 4 * (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card)) /
        Fintype.card N) := by
  rw [toReal_acceptProb_progEnv_kL, toReal_acceptProb_progEnv_kD]
  exact abs_lHybProb_zero_sub_le hL A hA hpost Q

end Step

end GordieHowe.ROM.NIZK
