-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseSplit
public import GordieHowe.Applications.Ring.KeyFreeChain
public import GordieHowe.Applications.Ring.KeyFreeRelayB
public import GordieHowe.Applications.Ring.KeyFreeFactors

@[expose] public section

/-!
# The side conditions of the key-free chain for the ML-DSA ring publishing `w₁`

The side conditions of `RingSignature.KeyFree.kfChain_le` at the ML-DSA ring publishing
`w₁`, with the key-free signer `w1KFSign` factoring as `w1KFFactors`, the statement program
`w1StmtP` and the proof requests `w1ToR`. At the ring level (`w1SideRing`) the forgery's
statement lists its members' hashes at the final oracle and no ring signing request collides
with a member's message representative at `ω`. At the main level (`w1Side`) each listed hash is
the hash at `ω` (case U) or the hash a main signing request lists for its signer at an equal
message-representative point and the same `w₁` (case S).

- `w1StmtPω`, `run_w1StmtP_eq_w1StmtPω`, `w1StmtPω_eq`: the statement program at a base component.
- `w1CollRing`: a collision of message representatives with a ring signing request.
- `w1SideRing`, `w1SideRing_of`, `w1_hEside`: the ring-level side condition and its proof from an
  event giving no collision at the base oracle and the statement at the final oracle.
- `w1Side`: the main-level side condition.
- `w1Side_of_sideRing` (**the side conditions are carried through the relay**): `hside` of
  `kfChain_le`.
- `bverify_join_of_w1Side`: case U at the extracted member gives base verification.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Side

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {Mo : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg))
    (RingSignature.RingWitOf (FIPSSignature p prims)) ⟨Pf, PC⟩}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {Frg : Type}

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt prims RMsg N

attribute [local instance] admDecF

variable (prims O Mo βmin tol enc k D bmsg) in
/-- **The statement program at a base component** `ω` (the `stmtPω` of `kfChain_le`). -/
noncomputable def w1StmtPω (sp : Y ≃+ Y₁ × Y₂) (ω : X → Y₁) (x : RingSignature.RingStmt Bf) : X₀f :=
  (w1StmtProg sp prims O bmsg x).run ω

omit [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The statement program reads only the base component** (`hstω`). -/
theorem run_w1StmtP_eq_w1StmtPω (sp : Y ≃+ Y₁ × Y₂) (x : RingSignature.RingStmt Bf) (G : X → Y) :
    (w1StmtP sp x).run G = w1StmtPω prims O Mo βmin tol enc k D bmsg sp (base sp G) x :=
  run_w1StmtP sp x G

/-- **The statement at a base component**: the ring statement with its members' hashes
`w1HashAt` at `ω`. -/
theorem w1StmtPω_eq (sp : Y ≃+ Y₁ × Y₂) (ω : X → Y₁) (x : RingSignature.RingStmt Bf) :
    w1StmtPω prims O Mo βmin tol enc k D bmsg sp ω x =
      (x, x.ring.1.map fun pk => w1HashAt O sp ω pk (bmsg x.ring x.msg) x.pub) :=
  run_w1StmtProg prims ω x

variable (O) in
/-- **A collision of message representatives with a ring signing request**: a member `pk` of the
ring `R` and a signing request `sign s R' m'` of `rs` with distinct message-representative points
and equal message representatives at `ω`. -/
def w1CollRing (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (ω : X → Y₁)
    (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (rs : List (RingSignature.Insider.Req Bf PSf adm n)) : Prop :=
  ∃ pk ∈ R.1, ∃ s R' m',
    (UnforgeRequest.sign s R' m' : RingSignature.Insider.Req Bf PSf adm n) ∈ rs ∧
    O.muPt (pubTr prims pk, bmsg R m) ≠ O.muPt (pubTr prims (pks s), bmsg R' m') ∧
    w1MuAt O sp ω pk (bmsg R m) = w1MuAt O sp ω (pks s) (bmsg R' m')

variable (O) in
/-- **The ring-level side condition** at the final oracle `G` and the base component `ω`, for a
forgery `f` with program statement `f.2 = (x, cs)` and ring requests `rs`: no collision of
message representatives at `ω` with a ring signing request (`w1CollRing`), and `cs` lists the
members' hashes `w1HashAt` at the base component of `G`. -/
def w1SideRing (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (G : X → Y) (ω : X → Y₁)
    (f : Frg × X₀f) (rs : List (RingSignature.Insider.Req Bf PSf adm n)) : Prop :=
  ¬ w1CollRing (adm := adm) O sp pks ω f.2.1.ring f.2.1.msg rs ∧
    f.2.2 = f.2.1.ring.1.map fun pk =>
      w1HashAt O sp (base sp G) pk (bmsg f.2.1.ring f.2.1.msg) f.2.1.pub

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The ring-level side condition** from no collision at `ω` and a program statement that is
the statement program's output at `G`. -/
theorem w1SideRing_of (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (G : X → Y)
    (ω : X → Y₁) (f : Frg × X₀f) (rs : List (RingSignature.Insider.Req Bf PSf adm n))
    (x : RingSignature.RingStmt Bf)
    (hc : ¬ w1CollRing (adm := adm) O sp pks ω f.2.1.ring f.2.1.msg rs)
    (hx : f.2 = (w1StmtP sp x).run G) :
    w1SideRing O sp pks G ω f rs := by
  refine ⟨hc, ?_⟩
  rw [run_w1StmtP_eq_w1StmtPω, w1StmtPω_eq] at hx
  rw [hx]

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **`hEside` of `kfChain_le`** for an event `Ev` giving no collision at the base component
of the base oracle `H` (`hcoll`) and a program statement that is the statement program's output at
the final oracle `G` (`hx`). -/
theorem w1_hEside (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims)
    (Ev : (X → Y) → (Frg × X₀f) × List (RingSignature.Insider.Req Bf PSf adm n) × (X → Y) → Prop)
    (hcoll : ∀ H f rs G, Ev H (f, rs, G) →
      ¬ w1CollRing (adm := adm) O sp pks (base sp H) f.2.1.ring f.2.1.msg rs)
    (hx : ∀ H f rs G, Ev H (f, rs, G) → ∃ x : RingSignature.RingStmt Bf, f.2 = (w1StmtP sp x).run G) :
    ∀ H f rs G, Ev H (f, rs, G) → w1SideRing O sp pks G (base sp H) f rs := fun H f rs G h =>
  let ⟨x, hx'⟩ := hx H f rs G h
  w1SideRing_of sp pks G _ f rs x (hcoll H f rs G h) hx'

variable (O) in
/-- **The main-level side condition** at the base component `ω`, for a forgery `f` with program
statement `f.2 = (x, cs)` and main requests `rs`, read only from statements: no collision of
message representatives at `ω` with a main signing request (`w1Coll`), and every hash `c` that
`cs` lists for a member `pk` (position `i`) is the hash `w1HashAt` at `ω` (case U), or a main
signing request `(s, R', m', xb)` of `rs` has the message-representative point of `pk`, the ring
statement `(R', m', x.pub)` and lists `c` for its signer (case S). -/
def w1Side (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (ω : X → Y₁) (f : Frg × X₀f)
    (rs : List (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q)) : Prop :=
  ¬ w1Coll (adm := adm) O sp pks ω f.2.1.ring f.2.1.msg rs ∧
    ∀ i (hi : i < f.2.1.ring.1.length) c, f.2.2[i]? = some c →
      c = w1HashAt O sp ω (f.2.1.ring.1[i]'hi) (bmsg f.2.1.ring f.2.1.msg) f.2.1.pub ∨
      ∃ e ∈ rs, ∃ s R' m' xb, w1SignEntry e = some (s, R', m', xb) ∧
        O.muPt (pubTr prims (f.2.1.ring.1[i]'hi), bmsg f.2.1.ring f.2.1.msg) =
          O.muPt (pubTr prims (pks s), bmsg R' m') ∧
        xb.1.ring = R' ∧ xb.1.msg = m' ∧ xb.1.pub = f.2.1.pub ∧
        xb.2.val[R'.1.idxOf (pks s)]? = some c

omit [AddGroup Y] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **A main signing request made by the relay is tagged with its ring request**. -/
theorem w1SignEntry_reqOf (c : ℕ) (r : RingSignature.Insider.Req Bf PSf adm n)
    (o : Option (BucketVec p × FIPSSignature p prims × List (Assignment X Y)))
    (x : Option X₀f) {s : Fin n} {R' : KeyRing (PubKey p prims) N} {m' : RMsg}
    {xb : W1BStmt prims RMsg N}
    (h : w1SignEntry (reqOf Bf (w1ToR (Q := Q)) (w1DummyR (Q := Q)) c r o x) =
      some (s, R', m', xb)) :
    r = .sign s R' m' := by
  rcases r with i | ⟨s₀, R₀, m₀⟩ | ⟨i, bm⟩ <;> rcases o with _ | o <;> rcases x with _ | x <;>
    simp [reqOf, w1SignEntry, w1ToR, w1DummyR] at h ⊢
  obtain ⟨rfl, h2⟩ := h
  cases h2
  simp_all

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **A base component read through a table of commitment-hash points** reads `ω` at every
message-representative point, for disjoint point sets (`hmc`). -/
theorem ωT_muPt (sp : Y ≃+ Y₁ × Y₂) (hmc : ∀ a b, O.muPt a ≠ O.chPt b) (ω : X → Y₁)
    {T' : X → Option Y} (hT' : ∀ z y, T' z = some y → ∃ b, z = O.chPt b)
    (a : Bytes 64 × Msg) : ωT sp ω T' (O.muPt a) = ω (O.muPt a) := by
  cases h : T' (O.muPt a) with
  | none => simp [ωT, h]
  | some y =>
    obtain ⟨b, hb⟩ := hT' _ _ h
    exact absurd hb (hmc a b)

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The message representative at a base component read through a table of commitment-hash
points** is the one at `ω`. -/
theorem w1MuAt_ωT (sp : Y ≃+ Y₁ × Y₂) (hmc : ∀ a b, O.muPt a ≠ O.chPt b) (ω : X → Y₁)
    {T' : X → Option Y} (hT' : ∀ z y, T' z = some y → ∃ b, z = O.chPt b)
    (pk : PubKey p prims) (bm : Msg) : w1MuAt O sp (ωT sp ω T') pk bm = w1MuAt O sp ω pk bm := by
  simp only [w1MuAt, ωT_muPt sp hmc ω hT']

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The commitment hash at a base component read through a table of commitment-hash points**:
the hash decoded at the commitment-hash point of the message representative at `ω`. -/
theorem w1HashAt_ωT (sp : Y ≃+ Y₁ × Y₂) (hmc : ∀ a b, O.muPt a ≠ O.chPt b) (ω : X → Y₁)
    {T' : X → Option Y} (hT' : ∀ z y, T' z = some y → ∃ b, z = O.chPt b)
    (pk : PubKey p prims) (bm : Msg) (w₁ : BucketVec p) :
    w1HashAt O sp (ωT sp ω T') pk bm w₁ =
      O.chAt sp (ωT sp ω T' (O.chPt (w1MuAt O sp ω pk bm, w₁))) := by
  rw [w1HashAt, w1MuAt_ωT sp hmc ω hT']

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **The side conditions are carried through the relay at the base component** (`hside` of
`kfChain_le` at the ML-DSA ring publishing `w₁`): at the base component `ω = base sp H`,
from the ring-level side condition at `reprogT Tb H`, the origin of the absorbed tables
(`KFTableFacts`) and the origin of the main requests (`CanAsk`), the main-level side condition
holds, for disjoint message-representative and commitment-hash points (`hmc`), injective
commitment-hash points (`hci`) and an idle request that is not a signing request (`hidle`). -/
theorem w1Side_of_sideRing [DecidableEq X] [Inhabited X] (sp : Y ≃+ Y₁ × Y₂)
    (hO : O.ReadsFst sp)
    (hmc : ∀ a b, O.muPt a ≠ O.chPt b) (hci : Function.Injective O.chPt)
    (S : KFStmt (w1StmtPω prims O Mo βmin tol enc k D bmsg sp))
    (pks : Fin n → PubKey p prims) {Q : ℕ} (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (idle : MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (hidle : w1SignEntry idle = none) (H : X → Y) (Tb : X → Option Y)
    (hP : List (AssignRelay.TaggedReq X Y (RingSignature.Insider.Req Bf PSf adm n) Q))
    (hist' : List (HistoryEntry (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) (MUResponse (Bf).core ⊕ Pf)))
    (f : Frg × X₀f)
    (hR : w1SideRing O sp pks (reprogT Tb H) (base sp H) f (hP.map AssignRelay.TaggedReq.req))
    (hex : (kfRelaySide sp Bf pks (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO) S
      w1ToR w1DummyR sc (base sp H) idle).Explains Q H Tb hP hist') :
    w1Side O sp pks (base sp H) f (hist'.map HistoryEntry.request) := by
  have hF := kfTableFacts_of_explains (base sp H) idle H Tb hP hist' hex
  set F := w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO with hFdef
  have hA : ∀ T' s Rg msg q z y',
      lastAssign (kfAsg sp Bf pks F (base sp H) T' H s Rg msg q) z = some y' →
      w1KFKept prims O sp bmsg (ωT sp (base sp H) T') (pks s) Rg msg q = z := by
    intro T' s Rg msg q z y' hl
    simp only [kfAsg, hFdef, w1KFFactors, lastAssign, List.foldl_cons, List.foldl_nil] at hl
    split_ifs at hl with hz
    exact hz
  have hent : ∀ z y, KFEntryFrom sp Bf pks F (w1StmtPω prims O Mo βmin tol enc k D bmsg sp)
      w1ToR sc (base sp H) H hP hist' z y → ∃ b, z = O.chPt b := by
    rintro z y ⟨p', -, s, Rg, msg, q, σ, -, -, -, hl, -⟩
    exact ⟨_, (hA _ _ _ _ _ _ _ hl).symm⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨pk, hpk, e, he, s, R', m', xb, hse, hne, heq⟩
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    rcases reqOf_of_explains (base sp H) idle H Tb hP hist' hex he' with h | ⟨q, hq', o, x, hx⟩
    · rw [h, hidle] at hse
      cases hse
    · rw [hx] at hse
      have hqs := w1SignEntry_reqOf _ _ _ _ hse
      exact hR.1 ⟨pk, hpk, s, R', m', hqs ▸ List.mem_map_of_mem hq', hne, heq⟩
  · intro i hi c hc
    have hTb : ∀ z y, Tb z = some y → ∃ b, z = O.chPt b := fun z y h => hent z y (hF.1 z y h)
    have hmap : ∀ {α β : Type} (l : List α) (g : α → β) (hi : i < l.length),
        (l.map g)[i]? = some (g (l[i]'hi)) := fun l g hi => by simp [hi]
    have hc2 := (hc.symm.trans ((congrArg (fun l => l[i]?) hR.2).trans (hmap _ _ hi)))
    have hc3 : c = O.chAt sp (ωT sp (base sp H) Tb (O.chPt (w1MuAt O sp (base sp H)
        (f.2.1.ring.1[i]'hi) (bmsg f.2.1.ring f.2.1.msg), f.2.1.pub))) := by
      rw [Option.some.inj hc2, base_reprogT]
      exact w1HashAt_ωT sp hmc _ hTb _ _ _
    subst hc3
    cases hT : Tb (O.chPt (w1MuAt O sp (base sp H) (f.2.1.ring.1[i]'hi) (bmsg f.2.1.ring f.2.1.msg),
        f.2.1.pub)) with
    | none =>
      left
      simp [ωT, hT, w1HashAt]
    | some y =>
      right
      obtain ⟨p', hp', s, Rg, msg, q, σ, hcd, hr, -, hl, e', he', hreq⟩ := hF.1 _ _ hT
      have hp2 : ∀ z y, p'.2 z = some y → ∃ b, z = O.chPt b := fun z y h =>
        hent z y (hF.2 p' hp' z y h)
      have hkp : O.chPt (w1MuAt O sp (base sp H) (pks s) (bmsg Rg msg), q.1) =
          O.chPt (w1MuAt O sp (base sp H) (f.2.1.ring.1[i]'hi) (bmsg f.2.1.ring f.2.1.msg),
            f.2.1.pub) := by
        rw [← w1MuAt_ωT sp hmc (base sp H) hp2]
        exact hA _ _ _ _ _ _ _ hl
      obtain ⟨hmuEq, hq1⟩ := Prod.mk.inj (hci hkp)
      have hmupt : O.muPt (pubTr prims (f.2.1.ring.1[i]'hi), bmsg f.2.1.ring f.2.1.msg) =
          O.muPt (pubTr prims (pks s), bmsg Rg msg) := by
        by_contra hne
        refine hR.1 ⟨_, List.getElem_mem hi, s, Rg, msg, ?_, hne, hmuEq.symm⟩
        rw [← hr]
        exact List.mem_map_of_mem (f := AssignRelay.TaggedReq.req) hp'
      set T' := overT p'.2 (lastAssign (kfAsg sp Bf pks F (base sp H) p'.2 H s Rg msg q))
        with hT'def
      have hT' : ∀ z y, T' z = some y → ∃ b, z = O.chPt b := by
        intro z y' h
        simp only [hT'def, overT] at h
        cases hz : lastAssign (kfAsg sp Bf pks F (base sp H) p'.2 H s Rg msg q) z with
        | none =>
          rw [hz] at h
          exact hp2 z y' h
        | some y'' => exact ⟨_, (hA _ _ _ _ _ _ _ hz).symm⟩
      have hidx : Rg.1.idxOf (pks s) < Rg.1.length := List.idxOf_lt_length_iff.2 hcd.2.1
      refine ⟨e'.request, List.mem_map_of_mem he', s, Rg, msg,
        w1Bnd (w1StmtPω prims O Mo βmin tol enc k D bmsg sp (ωT sp (base sp H) T')
          ⟨Rg, msg, q.1⟩), ?_, hmupt, ?_, ?_, ?_, ?_⟩
      · rw [hreq, hr]
        rfl
      · simp only [w1Bnd, w1StmtPω_eq]
      · simp only [w1Bnd, w1StmtPω_eq]
      · simp only [w1Bnd, w1StmtPω_eq]
        exact hq1
      · simp only [w1Bnd, w1StmtPω_eq]
        have hmap' : ∀ {α β : Type} (l : List α) (g : α → β) (j : ℕ) (hj : j < l.length),
            (l.map g)[j]? = some (g (l[j]'hj)) := fun l g j hj => by simp [hj]
        refine (congrArg (fun l => l[Rg.1.idxOf (pks s)]?)
          (List.take_of_length_le ((List.length_map _).trans_le Rg.2))).trans ?_
        refine (hmap' _ _ _ hidx).trans (congrArg some ?_)
        refine (congrArg (fun pk => w1HashAt O sp (ωT sp (base sp H) T') pk (bmsg Rg msg) q.1)
          (List.getElem_idxOf hidx)).trans ?_
        refine (w1HashAt_ωT sp hmc (base sp H) hT' _ _ _).trans ?_
        rw [hmuEq, hq1]
        have h1 : T' (O.chPt (w1MuAt O sp (base sp H) (f.2.1.ring.1[i]'hi)
            (bmsg f.2.1.ring f.2.1.msg), f.2.1.pub)) = some y := by
          rw [← hkp] at hl
          rw [← hkp]
          simp only [hT'def, overT, hl]
          rfl
        simp [ωT, h1, hT]

omit hadm in
/-- **Case U at the extracted member gives base verification** (`bverify_join_of_hashAt`): a
witness of `w1ExpRel` for the program statement of a forgery satisfying `w1Side` at `ω`, whose
member's listed hash is in case U, verifies at `join sp ω h`. -/
theorem bverify_join_of_w1Side (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp) (ω : X → Y₁)
    (h : X → Y₂) (q : X₀f × RingSignature.RingWitOf (FIPSSignature p prims))
    (hq : q ∈ w1ExpRel prims enc bmsg adm)
    (hU : ∀ (hi : q.2.idx < q.1.1.ring.1.length) c, q.1.2[q.2.idx]? = some c →
      c = w1HashAt O sp ω (q.1.1.ring.1[q.2.idx]'hi) (bmsg q.1.1.ring q.1.1.msg) q.1.1.pub) :
    ∃ hi : q.2.idx < q.1.1.ring.1.length,
      (w1BaseSigner prims O βmin tol enc Lf bmsg).bverify (join sp ω h)
        (q.1.1.ring.1[q.2.idx]'hi) (bmsg q.1.1.ring q.1.1.msg) q.2.sig = true :=
  bverify_join_of_hashAt sp hO ω h q hq fun hi => by
    obtain ⟨-, -, c, hc, -⟩ := hq
    rw [hc, hU hi c hc]

variable (O) in
/-- **The named message-representative points of a forgery**: the points of the ring's members on
the forgery's base message, then the points of the logged signing requests. -/
def w1MuPts (pks : Fin n → PubKey p prims) (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (rs : List (RingSignature.Insider.Req Bf PSf adm n)) : List X :=
  R.1.map (fun pk => O.muPt (pubTr prims pk, bmsg R m)) ++
    rs.filterMap fun r => match r with
      | .sign s R' m' => some (O.muPt (pubTr prims (pks s), bmsg R' m'))
      | _ => none

omit [AddGroup Y] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- There are at most `N + |rs|` named points. -/
theorem length_w1MuPts_le (pks : Fin n → PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (rs : List (RingSignature.Insider.Req Bf PSf adm n)) :
    (w1MuPts O pks R m rs).length ≤ N + rs.length := by
  rw [w1MuPts, List.length_append, List.length_map]
  exact Nat.add_le_add R.2 (List.length_filterMap_le _ _)

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **A ring-level collision is a collision of the message representatives at the named points**:
two distinct message-representative points among `w1MuPts` with equal decodings at `H`, for
decodings reading only the first component. -/
theorem collides_of_w1CollRing (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (pks : Fin n → PubKey p prims) (H : X → Y) (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (rs : List (RingSignature.Insider.Req Bf PSf adm n))
    (h : w1CollRing O sp pks (base sp H) R m rs) :
    ∃ x ∈ w1MuPts O pks R m rs, ∃ x' ∈ w1MuPts O pks R m rs, x ∈ Set.range O.muPt ∧
      x' ∈ Set.range O.muPt ∧ x ≠ x' ∧ O.muAns (H x) = O.muAns (H x') := by
  obtain ⟨pk, hpk, s, R', m', hr, hne, heq⟩ := h
  refine ⟨_, List.mem_append_left _ (List.mem_map_of_mem hpk), _,
    List.mem_append_right _ (List.mem_filterMap.2 ⟨_, hr, rfl⟩), ⟨_, rfl⟩, ⟨_, rfl⟩, hne, ?_⟩
  rw [hO.muAns_eq_muAt, hO.muAns_eq_muAt]
  exact heq

end Side

end GordieHowe.Ring.MLDSAW1
