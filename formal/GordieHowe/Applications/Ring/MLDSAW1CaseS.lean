-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1SignLogs
public import GordieHowe.Applications.Ring.MLDSAW1CaseU
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeGuess

@[expose] public section

/-!
# Case S of the key-free route for the ML-DSA ring publishing `w₁`

Case S of the key-free route at the ML-DSA ring publishing `w₁` (`w1CaseS`,
`GordieHowe/Applications/Ring/MLDSAW1CaseU.lean`): the hash listed for a member of the forgery's
ring is that of a logged signing request with the member's message-representative point. A logged
signing request of the side-mode key-free relay (`KFSignedAsk`) carries the key-free signer's
signature `σ_j`, accepted at the oracle constantly its listed hash at its commitment; so a forged
signature `σ* ≠ σ_j` at the same key, message, commitment and hash is a second signature, a
Module-SIS solution at the signer's seed (`keyGenKernel_secondSigVec`,
`GordieHowe/Applications/MLDSA/Signing/SecondSignature.lean`), and `σ* = σ_j` is a guess of
`σ_j`.

- `hash_eq_cTilde_of_ringVerify`, `ringVerify_const_cTilde`, `ringVerify_of_w1KFOut`,
  `w1Bnd_listed_of_w1KFOut`: the key-free signer's signature is accepted at the oracle constantly
  its commitment hash, which its statement lists for the signer.
- `w1EntrySig`, `W1SecondSig`, `w1EntrySig_of_w1SignEntry`, `w1CaseS_guess_or_second`: the
  signature of a signing entry; case S with a second signature; case S at a canonical witness
  splits into a guess and a second signature.
- `keyGenKernel_of_signEntry`, `keyGenKernel_of_w1SecondSig`: a second signature is a Module-SIS
  solution at the signer's seed, at an approved parameter set, when the users' keys with equal
  key hashes are equal.
- `w1MsisReadout`, `sum_w1SecondSig_le_keyGenMsisMultiWinProb`,
  **`tsum_w1SecondSig_le_keyGenMsisMultiWinProb`**: the Module-SIS reduction
  `B₂` reading out a second signature, and the bound by its win probability
  (`Lattice.sum_le_winProb_map`).
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The honest signature of a signing request -/

section Honest

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {Mo : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

omit [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- **An accepted signature's commitment hash is the one verification reads**: `H` at
`((tr, m), w₁)`, with `tr` the hash of the key. -/
theorem hash_eq_cTilde_of_ringVerify {H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p}
    {pk : PublicKey p prims} {m : Msg} {w1 : BucketVec p} {σ : FIPSSignature p prims}
    (h : ringVerify prims H enc pk m w1 σ = true) :
    H ((prims.hashPublicKey pk.rho pk.t1, m), w1) = σ.cTilde := by
  simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

omit [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- **An accepted signature is accepted at the oracle constantly its commitment hash.** -/
theorem ringVerify_const_cTilde {H : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p}
    {pk : PublicKey p prims} {m : Msg} {w1 : BucketVec p} {σ : FIPSSignature p prims}
    (h : ringVerify prims H enc pk m w1 σ = true) :
    ringVerify prims (fun _ => σ.cTilde) enc pk m w1 σ = true := by
  simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨h.1.1, trivial⟩, h.2⟩

/-- **The key-free signer's signature is accepted at the oracle constantly its commitment
hash**, at its published value `w₁ = w1Of pk σ`: for a public part and signature `q` of
`w1KFOut` at any base component. -/
theorem ringVerify_of_w1KFOut [DecidableEq X] (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) {ω : X → Y₁} {pk : PubKey p prims}
    {R : KeyRing (PubKey p prims) N} {c : ℕ} {m : RMsg} {s : KFCoins (p := p) (T := T) k D Y₁}
    {q : (BucketVec p × Y₁) × FIPSSignature p prims}
    (hq : w1KFOut (T := T) prims O sp βmin tol enc k D bmsg ω pk R c m s = some q) :
    ringVerify prims (fun _ => q.2.cTilde) enc (pubPk prims pk) (bmsg R m) q.1.1 q.2 = true ∧
      q.1.1 = w1Of prims enc pk q.2 := by
  unfold w1KFOut at hq
  split_ifs at hq with h1 hi
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 hq
  refine ⟨ringVerify_const_cTilde (ringVerify_kfLoop sp hO hdisj pk R ⟨_, hi⟩ _ s hs'
    (fun _ => 0) (bmsg R m)), rfl⟩

omit [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The key-free signer's statement lists its commitment hash for the signer**: the program
statement `w1StmtPω` of `(R, m, w₁)` at the base component `ω` read through `Tb` overridden at
the kept point by the published value `v`, truncated by `w1Bnd`, lists at the signer's position
the commitment hash `c̃` of the signature, for a public part and signature `q` of `w1KFOut` at `ω`
read through `Tb`, at every position of the signer in the ring. -/
theorem w1Bnd_listed_of_w1KFOut [DecidableEq X] (sp : Y ≃+ Y₁ × Y₂)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) {ω : X → Y₁} {Tb : X → Option Y}
    {pk : PubKey p prims} {R : KeyRing (PubKey p prims) N} {c : ℕ} {m : RMsg}
    {s : KFCoins (p := p) (T := T) k D Y₁} {q : (BucketVec p × Y₁) × FIPSSignature p prims}
    (hq : w1KFOut (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω Tb) pk R c m s = some q)
    (y : Y) {j : ℕ} (hj : R.1[j]? = some pk) :
    (w1Bnd (w1StmtPω prims O Mo βmin tol enc k D bmsg sp (ωT sp ω (overT Tb
      (lastAssign [⟨w1KFKept prims O sp bmsg (ωT sp ω Tb) pk R m q.1,
        sp.symm (q.1.2, (sp y).2)⟩]))) ⟨R, m, q.1.1⟩)).2.val[j]? =
      some q.2.cTilde := by
  unfold w1KFOut at hq
  split_ifs at hq with h1 hi
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.1 hq
  have hlt : j < R.1.length := (List.getElem?_eq_some_iff.1 hj).1
  have hN : j < N := lt_of_lt_of_le hlt R.2
  simp only [w1Bnd, w1StmtPω, w1StmtProg, OracleProg.run_mapOutput, run_hashesProg]
  rw [List.getElem?_take_of_lt hN, List.getElem?_map, hj]
  simp only [Option.map_some, Option.some.injEq]
  -- the base component read at the signer's message-representative point is not overridden
  have hmu : ωT sp ω (overT Tb (lastAssign [⟨w1KFKept prims O sp bmsg (ωT sp ω Tb) pk R m
      ((w1Of prims enc pk s'.2.1, s'.2.2)), sp.symm (s'.2.2, (sp y).2)⟩]))
        (O.muPt (pubTr prims pk, bmsg R m)) = ωT sp ω Tb (O.muPt (pubTr prims pk, bmsg R m)) := by
    have : lastAssign [⟨w1KFKept prims O sp bmsg (ωT sp ω Tb) pk R m
        ((w1Of prims enc pk s'.2.1, s'.2.2)), sp.symm (s'.2.2, (sp y).2)⟩]
          (O.muPt (pubTr prims pk, bmsg R m)) = none := by
      simp only [lastAssign, List.foldl_cons, List.foldl_nil, w1KFKept]
      rw [if_neg fun h => hdisj _ _ h.symm]
    simp only [ωT, overT, this, Option.none_or]
  rw [hmu]
  -- the kept point reads the published value
  set xk := O.chPt (O.muAt sp (ωT sp ω Tb (O.muPt (pubTr prims pk, bmsg R m))),
    w1Of prims enc pk s'.2.1) with hxk
  have hL : lastAssign [⟨w1KFKept prims O sp bmsg (ωT sp ω Tb) pk R m
      ((w1Of prims enc pk s'.2.1, s'.2.2)), sp.symm (s'.2.2, (sp y).2)⟩] xk =
        some (sp.symm (s'.2.2, (sp y).2)) := by
    simp [lastAssign, w1KFKept, hxk]
  have hkept : ωT sp ω (overT Tb (lastAssign [⟨w1KFKept prims O sp bmsg (ωT sp ω Tb) pk R m
      ((w1Of prims enc pk s'.2.1, s'.2.2)), sp.symm (s'.2.2, (sp y).2)⟩])) xk = s'.2.2 := by
    simp only [ωT, overT, hL, Option.some_or, AddEquiv.apply_symm_apply]
  rw [hkept]
  exact (cTilde_of_kfLoop_eq_some pk R ⟨_, hi⟩ _ s hs').symm

end Honest

/-! ### Case S at a canonical witness -/

section Split

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {Mo : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {Frg : Type}

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt prims RMsg N

attribute [local instance] admDecF

/-- **The signature of a signing entry**: the base signature of a relayed signing request; none
for other main requests. -/
def w1EntrySig :
    MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q →
    Option (FIPSSignature p prims)
  | .inr (.inl (_, (.sign _ _ _, _), σ)) => some σ
  | _ => none

variable [DecidableEq X] (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)

/-- **Case S with a second signature** at the side coins `sc`, the base component `ω`, the
forgery `f`, the main requests `rs` and the witness `w` of the users with seeds `ξ`: the witness
is in the relation at an uncorrupted member `i` of the ring; a main request `e` of `rs` is a
signed request of the side-mode key-free relay (`KFSignedAsk`) and a signing entry with the
member's message-representative point, the ring statement and the listed hash of the witness's
position (`w1CaseS`); and its signature `σe` differs from the witness's. -/
def W1SecondSig (ξ : Fin n → Bytes 32) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (ω : X → Y₁) (f : Frg × X₀f)
    (rs : List (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q))
    (w : RingSignature.RingWitOf (FIPSSignature p prims)) (i : Fin n) (σe : FIPSSignature p prims) : Prop :=
  letI : DecidablePred (α := KeyRing (PubKey p prims) N) adm := hadm
  (f.2, w) ∈ w1ExpRel prims enc bmsg adm ∧
    f.2.1.ring.1[w.idx]? = some ((Bf).pk (ξ i)) ∧
    ∃ hi : w.idx < f.2.1.ring.1.length, ∃ c, f.2.2[w.idx]? = some c ∧
      ∃ e ∈ rs, ∃ s R' m' xb, w1SignEntry e = some (s, R', m', xb) ∧
        KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω e ∧
        O.muPt (pubTr prims (f.2.1.ring.1[w.idx]'hi), bmsg f.2.1.ring f.2.1.msg) =
          O.muPt (pubTr prims ((Bf).pk (ξ s)), bmsg R' m') ∧
        xb.1.ring = R' ∧ xb.1.msg = m' ∧ xb.1.pub = f.2.1.pub ∧
        xb.2.val[List.idxOf (α := PubKey p prims) ((Bf).pk (ξ s)) R'.1]? = some c ∧
        w1EntrySig e = some σe ∧ w.sig ≠ σe

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
theorem w1EntrySig_of_w1SignEntry
    {e : MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q}
    {s : Fin n} {R : KeyRing (PubKey p prims) N} {m : RMsg}
    {xb : W1BStmt prims RMsg N}
    (h : w1SignEntry e = some (s, R, m, xb)) : ∃ σ, w1EntrySig e = some σ := by
  rcases e with _ | (⟨_, ⟨_ | _ | _, _⟩, σ⟩ | _) <;> simp [w1SignEntry] at h
  exact ⟨σ, rfl⟩

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **Case S at a canonical witness splits** into a guess and a second signature: for a witness
in the relation at an uncorrupted member (`w1Ok`) in case S (`w1CaseS`), with every signing entry
of the main requests a signed request of the side-mode key-free relay (`hsigned`), either a signing
entry's signature is the witness's (the guess), or the witness is in case S with a second
signature (`W1SecondSig`). -/
theorem w1CaseS_guess_or_second {ξ : Fin n → Bytes 32}
    {sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁} {ω : X → Y₁} {f : Frg × X₀f}
    {rs : List (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q)}
    {w : RingSignature.RingWitOf (FIPSSignature p prims)}
    (hok : w1Ok prims O Mo βmin tol enc k D bmsg adm (fun j => (Bf).pk (ξ j)) f rs w)
    (hS : w1CaseS (adm := adm) (fun j => (Bf).pk (ξ j)) f rs w)
    (hsigned : ∀ r' ∈ rs, (w1SignEntry r').isSome = true →
      letI : DecidablePred (α := KeyRing (PubKey p prims) N) adm := hadm
      KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
        (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
        (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω r') :
    (∃ e ∈ rs, (w1SignEntry e).isSome = true ∧ w1EntrySig e = some w.sig ∧
        letI : DecidablePred (α := KeyRing (PubKey p prims) N) adm := hadm
        KFSignedAsk (PS := PSf) (adm := adm) sp Bf (fun j => (Bf).pk (ξ j))
          (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
          (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω e) ∨
      ∃ i σe, W1SecondSig sp hO ξ sc ω f rs w i σe := by
  obtain ⟨hrel, i, hmem, -⟩ := hok
  obtain ⟨hi, c, hc, e, he, s, R', m', xb, hse, hpt, hR, hm, hpub, hlist⟩ := hS
  obtain ⟨σe, hσe⟩ := w1EntrySig_of_w1SignEntry hse
  have hsome : (w1SignEntry e).isSome = true := by rw [hse]; rfl
  by_cases hσ : w.sig = σe
  · exact .inl ⟨e, he, hsome, hσ ▸ hσe, hsigned e he hsome⟩
  · exact .inr ⟨i, σe, hrel, hmem, hi, c, hc, e, he, s, R', m', xb, hse, hsigned e he hsome, hpt,
      hR, hm, hpub, hlist, hσe, hσ⟩

end Split

/-! ### A second signature at the signer's commitment -/

section Msis

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [NeZero (bucketCount p)] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Nonempty (MaskBox p)]
  {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps} {Mo : MaskOracle X Y p T Msg}
  {βmin : ℚ≥0} {tol : ℕ} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

/-- **A forged signature at the commitment and the listed hash of an honest signing request gives a
Module-SIS solution** (`keyGenKernel_secondSigVec`): for a signature `σ` accepted under the key
`pk` of the seed `ξ` on `bmsg R m` at the oracle constantly `c` with commitment `w₁`, and a signing
request of `pk` with the same message-representative point whose statement `xb` (the key-free
signer's, `w1Bnd` of `w1StmtPω`, for its public part and signature `q` of `w1KFOut`) lists `c` for
the signer and publishes `w₁`, a signature `σ ≠ q.2` gives a solution at `ξ`, at an approved
parameter set. -/
theorem keyGenKernel_of_signEntry (hp : p.isApproved) [DecidableEq X] (sp : Y ≃+ Y₁ × Y₂)
    (hO : O.ReadsFst sp) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (hmu : Function.Injective O.muPt) (ξ
        : Bytes 32)
    {pk : PubKey p (concretePrimitivesKeyGen p)}
    (hξ : pubPk (concretePrimitivesKeyGen p) pk =
      (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1)
    {R R' : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N} {m m' : RMsg}
    {σ : FIPSSignature p (concretePrimitivesKeyGen p)} {c : CommitHashBytes p}
    {w₁ : BucketVec p}
    (hv : ringVerify (concretePrimitivesKeyGen p) (fun _ => c) (concreteEnc p)
      (pubPk (concretePrimitivesKeyGen p) pk) (bmsg R m)
      (w1Of (concretePrimitivesKeyGen p) (concreteEnc p) pk σ) σ = true)
    (hw₁ : w1Of (concretePrimitivesKeyGen p) (concreteEnc p) pk σ = w₁)
    (hpt : O.muPt (pubTr (concretePrimitivesKeyGen p) pk, bmsg R m) =
      O.muPt (pubTr (concretePrimitivesKeyGen p) pk, bmsg R' m'))
    {ω : X → Y₁} {Tb : X → Option Y} {c' : ℕ} {s : KFCoins (p := p) (T := T) k D Y₁}
    {q : (BucketVec p × Y₁) × FIPSSignature p (concretePrimitivesKeyGen p)}
    (hq : w1KFOut (T := T) (concretePrimitivesKeyGen p) O sp βmin tol (concreteEnc p) k D bmsg
      (ωT sp ω Tb) pk R' c' m' s = some q) (y : Y) {j : ℕ} (hj : R'.1[j]? = some pk)
    {xb : W1BStmt (concretePrimitivesKeyGen p) RMsg N}
    (hxb : xb = w1Bnd (w1StmtPω (concretePrimitivesKeyGen p) O Mo βmin tol (concreteEnc p) k D
      bmsg sp (ωT sp ω (overT Tb (lastAssign
        [⟨w1KFKept (concretePrimitivesKeyGen p) O sp bmsg (ωT sp ω Tb) pk R' m' q.1,
          sp.symm (q.1.2, (sp y).2)⟩]))) ⟨R', m', q.1.1⟩))
    (hlist : xb.2.val[j]? = some c) (hpub : xb.1.pub = w₁) (hne : σ ≠ q.2) :
    Lattice.KeyGenKernel p (concretePrimitivesKeyGen p) (Lattice.msisStrictBoundZ p)
      (Lattice.msisBoundU p) ξ
      (secondSigVec p (keyGenFromSeed p (concretePrimitivesKeyGen p) ξ).1 σ q.2) := by
  -- the listed hash is the honest signature's
  have hc : c = q.2.cTilde := by
    have h := w1Bnd_listed_of_w1KFOut (Mo := Mo) sp hdisj hq y hj
    rw [← hxb, hlist] at h
    exact Option.some.inj h
  -- the published value is the honest signature's commitment
  have hpub' : xb.1.pub = q.1.1 := by
    rw [hxb]
    simp only [w1Bnd, w1StmtPω, w1StmtProg, OracleProg.run_mapOutput]
  obtain ⟨hv', -⟩ := ringVerify_of_w1KFOut sp hO hdisj hq
  have hbm : bmsg R m = bmsg R' m' := (Prod.mk.inj (hmu hpt)).2
  rw [hc, hw₁, ← hpub, hpub', hbm, hξ] at hv
  rw [hξ] at hv'
  exact keyGenKernel_secondSigVec hp ξ hne hv hv'

end Msis

/-! ### Case S with a second signature: the Module-SIS reduction -/

section Reduction

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [NeZero (bucketCount p)] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Nonempty (MaskBox p)]
  {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps} {Mo : MaskOracle X Y p T Msg}
  {βmin : ℚ≥0} {tol : ℕ} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase (concretePrimitivesKeyGen p) O Mo βmin
      tol (concreteEnc p) k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [hadm : DecidablePred adm] {n Q : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {Frg : Type}

local notation "Pc" => concretePrimitivesKeyGen p
local notation "Bf" => freshBase (concretePrimitivesKeyGen p) O Mo βmin tol (concreteEnc p) k D bmsg
local notation "Lf" => freshLoop (concretePrimitivesKeyGen p) O Mo βmin k D
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt (concretePrimitivesKeyGen p) RMsg N

attribute [local instance] admDecF

variable [DecidableEq X] (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **Case S with a second signature gives a Module-SIS solution at the member's seed**
(`keyGenKernel_of_signEntry`), when the users' keys with equal message-representative key hashes
are equal (`hcoll`, off `trCollAt`) and the message-representative points are injective. -/
theorem keyGenKernel_of_w1SecondSig (hp : p.isApproved) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hmu : Function.Injective O.muPt) {ξ : Fin n → Bytes 32}
    (hcoll : ∀ i j, pubTr Pc ((Bf).pk (ξ i)) = pubTr Pc ((Bf).pk (ξ j)) →
      (Bf).pk (ξ i) = (Bf).pk (ξ j))
    {sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁} {ω : X → Y₁} {f : Frg × X₀f}
    {rs : List (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq Pc O Mo βmin tol (concreteEnc p) k D bmsg PS adm n Q)}
    {w : RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))} {i : Fin n} {σe : FIPSSignature p Pc}
    (h : W1SecondSig sp hO ξ sc ω f rs w i σe) :
    Lattice.KeyGenKernel p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) (ξ i)
      (secondSigVec p (keyGenFromSeed p Pc (ξ i)).1 w.sig σe) := by
  obtain ⟨⟨-, hi₀, c₀, hc₀, hv, hw₁⟩, hmem, hi, c, hc, e, -, s, R', m', xb, hse, hask, hpt, hR,
    hm, hpub, hlist, hσe, hne⟩ := h
  obtain ⟨c', hc', Tb, q, y, hpk, -, hq, hxb, he⟩ :=
    w1SignEntry_of_kfSignedAsk (Mo := Mo) sp hO _ sc ω hask hse
  -- the entry's signature is the honest one
  have hσ : σe = q.2 := by
    rw [he] at hσe
    exact (Option.some.inj hσe).symm
  subst hσ
  -- the member is user `i`, and user `s` is user `i`
  have hmi : f.2.1.ring.1[w.idx]'hi = (Bf).pk (ξ i) := by
    rw [List.getElem?_eq_getElem hi] at hmem
    exact Option.some.inj hmem
  have hsi : (Bf).pk (ξ s) = (Bf).pk (ξ i) := by
    have := (Prod.mk.inj (hmu hpt)).1
    rw [hmi] at this
    exact (hcoll i s this).symm
  -- the listed hashes agree
  have hcc : c₀ = c := by
    rw [hc] at hc₀
    exact (Option.some.inj hc₀).symm
  subst hcc
  rw [hmi] at hv hw₁ hpt
  rw [hsi] at hpt hq hpk hlist hxb
  subst hR hm
  exact keyGenKernel_of_signEntry (Mo := Mo) hp sp hO hdisj hmu (ξ i) rfl hv hw₁ hpt hq y
    (List.getElem?_idxOf (α := PubKey p Pc) hpk) hxb hlist hpub hne

open Classical in
/-- **The readout of the Module-SIS reduction `B₂`** at the users' seeds `ξ` and an outcome `d` of
the key-free extraction run (the canonical witness, the side coins, the base component, the
forgery and the first main requests): `(i, secondSigVec pk_i σ* σe)` for a forged signature `σ*`
of the canonical witness and the signature `σe` of a logged signing request in case S with a
second signature (`W1SecondSig`) at user `i`, when it is a solution at user `i`'s seed; none
otherwise. -/
noncomputable def w1MsisReadout (ξ : Fin n → Bytes 32)
    (d : Option (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) × (Fin Q → KFCoins (p := p) (T := T) k D Y₁) ×
      (X → Y₁) × (Frg × X₀f) ×
      List (MURequest (SignOracle.none (Bf).core) n ⊕
        W1Rq Pc O Mo βmin tol (concreteEnc p) k D bmsg PS adm n Q)) :
    Option (Fin n × (RqVec p.l × RqVec p.k)) :=
  if h : ∃ a : Fin n × (RqVec p.l × RqVec p.k),
      Lattice.KeyGenKernel p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) (ξ a.1) a.2 ∧
        ∃ w σe, d.1 = some w ∧ W1SecondSig sp hO ξ d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2 w a.1 σe ∧
          a.2 = secondSigVec p (keyGenFromSeed p Pc (ξ a.1)).1 w.sig σe then
    some h.choose
  else none

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **Case S with a second signature is at most the Module-SIS win probability of `B₂`**
(`sum_le_winProb_map`): for laws `L ξ` of outcomes at the users' seeds `ξ` read by `dat`, the
average over uniform seeds of the probability that the seeds' keys with equal key hashes are equal
(`hcoll`, off `trCollAt`) and the canonical witness is in case S with a second signature is at
most `keyGenMsisMultiWinProb` of the reduction `ξ ↦ (L ξ).map (w1MsisReadout ξ ∘ dat)`, at an
approved parameter set. -/
theorem sum_w1SecondSig_le_keyGenMsisMultiWinProb (hp : p.isApproved)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (hmu : Function.Injective O.muPt) {Ω : Type}
    (L : (Fin n → Bytes 32) → PMF Ω)
    (dat : Ω → Option (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) × (Fin Q → KFCoins (p := p) (T := T) k D Y₁) ×
      (X → Y₁) × (Frg × X₀f) ×
      List (MURequest (SignOracle.none (Bf).core) n ⊕
        W1Rq Pc O Mo βmin tol (concreteEnc p) k D bmsg PS adm n Q)) :
    ∑ ξ, (Fintype.card (Fin n → Bytes 32) : ℝ≥0∞)⁻¹ * (L ξ).toOuterMeasure
        {o | (∀ i j, pubTr Pc ((Bf).pk (ξ i)) = pubTr Pc ((Bf).pk (ξ j)) →
            (Bf).pk (ξ i) = (Bf).pk (ξ j)) ∧
          ∃ w i σe, (dat o).1 = some w ∧
            W1SecondSig sp hO ξ (dat o).2.1 (dat o).2.2.1 (dat o).2.2.2.1 (dat o).2.2.2.2 w i σe} ≤
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        fun ξ => (L ξ).map (w1MsisReadout sp hO ξ ∘ dat) := by
  refine Lattice.sum_le_winProb_map _ L (fun ξ o => w1MsisReadout sp hO ξ (dat o)) _
    fun ξ o ho => ?_
  obtain ⟨hcoll, w, i, σe, hw, hS⟩ := ho
  have hex : ∃ a : Fin n × (RqVec p.l × RqVec p.k),
      Lattice.KeyGenKernel p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) (ξ a.1) a.2 ∧
        ∃ w σe, (dat o).1 = some w ∧ W1SecondSig sp hO ξ (dat o).2.1 (dat o).2.2.1 (dat o).2.2.2.1
          (dat o).2.2.2.2 w a.1 σe ∧
          a.2 = secondSigVec p (keyGenFromSeed p Pc (ξ a.1)).1 w.sig σe :=
    ⟨(i, secondSigVec p (keyGenFromSeed p Pc (ξ i)).1 w.sig σe),
      keyGenKernel_of_w1SecondSig sp hO hp hdisj hmu hcoll hS, w, σe, hw, hS, rfl⟩
  refine ⟨hex.choose, ?_, hex.choose_spec.1⟩
  simp only [w1MsisReadout, dif_pos hex]


omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **Case S with a second signature, averaged over the users' seeds, the side coins, the base
component and an auxiliary input, is at most the Module-SIS win probability of `B₂`**: for laws
`Lr ξ sc ω a` of outcomes read by `dat`, the average over uniform seeds `ξ` with the keys of equal
key hashes equal (`hcoll`), uniform side coins `sc`, uniform base components `ω` and auxiliary
inputs `a ∼ aux ξ sc ω`, of the probability that the outcome is in case S with a second signature,
is at most `keyGenMsisMultiWinProb` of the reduction reading out `w1MsisReadout` from the joint
law, at an approved parameter set. -/
theorem tsum_w1SecondSig_le_keyGenMsisMultiWinProb [Fintype Y₁] [Fintype X] (hp : p.isApproved)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (hmu : Function.Injective O.muPt) {Ω Aux : Type}
    (aux : (Fin n → Bytes 32) → (Fin Q → KFCoins (p := p) (T := T) k D Y₁) → (X → Y₁) → PMF Aux)
    (Lr : (Fin n → Bytes 32) → (Fin Q → KFCoins (p := p) (T := T) k D Y₁) → (X → Y₁) → Aux →
      PMF Ω)
    (dat : Ω → Option (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) × (Frg × X₀f) ×
      List (MURequest (SignOracle.none (Bf).core) n ⊕
        W1Rq Pc O Mo βmin tol (concreteEnc p) k D bmsg PS adm n Q)) :
    ∑' ξ, PMF.uniformOfFintype (Fin n → Bytes 32) ξ *
        {ξ : Fin n → Bytes 32 | ∀ i j, pubTr Pc ((Bf).pk (ξ i)) = pubTr Pc ((Bf).pk (ξ j)) →
          (Bf).pk (ξ i) = (Bf).pk (ξ j)}.indicator (fun ξ =>
        ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
          ∑' ω, PMF.uniformOfFintype (X → Y₁) ω *
            ∑' a, aux ξ sc ω a * (Lr ξ sc ω a).toOuterMeasure
              {o | ∃ w i σe, (dat o).1 = some w ∧
                W1SecondSig sp hO ξ sc ω (dat o).2.1 (dat o).2.2 w i σe}) ξ ≤
      Lattice.keyGenMsisMultiWinProb p Pc (Lattice.msisStrictBoundZ p) (Lattice.msisBoundU p) n
        fun ξ => ((PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁)).bind fun sc =>
          (PMF.uniformOfFintype (X → Y₁)).bind fun ω => (aux ξ sc ω).bind fun a =>
            (Lr ξ sc ω a).map fun o => ((dat o).1, sc, ω, (dat o).2.1, (dat o).2.2)).map
          (w1MsisReadout sp hO ξ) := by
  refine le_trans (le_of_eq ?_) (sum_w1SecondSig_le_keyGenMsisMultiWinProb sp hO hp hdisj hmu
    (fun ξ => (PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁)).bind fun sc =>
      (PMF.uniformOfFintype (X → Y₁)).bind fun ω => (aux ξ sc ω).bind fun a =>
        (Lr ξ sc ω a).map fun o => ((dat o).1, sc, ω, (dat o).2.1, (dat o).2.2)) id)
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [PMF.uniformOfFintype_apply]
  by_cases hc : ∀ i j, pubTr Pc ((Bf).pk (ξ i)) = pubTr Pc ((Bf).pk (ξ j)) →
      (Bf).pk (ξ i) = (Bf).pk (ξ j)
  · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hc]
    congr 1
    simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply, id]
    refine tsum_congr fun sc => congrArg _ (tsum_congr fun ω => congrArg _
      (tsum_congr fun a => congrArg _ (congrArg _ ?_)))
    ext o
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · simp only [Set.indicator, Set.mem_setOf_eq, if_neg hc, mul_zero]
    refine (mul_eq_zero_of_right _ ?_).symm
    exact MeasureTheory.measure_mono_null (fun o ho => (hc ho.1).elim) MeasureTheory.measure_empty

end Reduction

end GordieHowe.Ring.MLDSAW1
