-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.IOP
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Set.Finite.List
public import GordieHowe.Foundations.ToMathlib.ListLength

@[expose] public section

/-!
# Ring signatures from a signature scheme and a BCS argument: syntax and relation

The objects of the ring-signature construction, generic in the base signature scheme and in the IOP
(no circuit is fixed here).

- `SigScheme`: a signature scheme with key generation from uniform coins, signing from uniform
  coins (Falcon's salt `r` among them), a public value read off every signature (`pub`: Falcon's
  salt, `Unit` for ML-DSA, ML-DSA's `w₁` for the ring that publishes it), and a deterministic
  verifier. `SigScheme.CorrectWithin Sch ε`: an honest signature fails to verify with probability at
  most `ε` over the signing coins, for every key and message (`SigScheme.Correct`: never).
  `SigScheme.PubOfCoins Sch pubOf`: the public value of an honest signature is a function `pubOf` of
  the signing coins alone (Falcon's salt; `Unit`), so it can be drawn without the secret key.
- `RingStmt`, `RingWit`, `RingRel bind`: the statement `(R, m, ρ)` (a ring of public keys, a
  ring message, the public value of the signature, `ρ = pub σ`), the witness `(i, σ)`, and the ring
  relation `i < |R| ∧ pub σ = ρ ∧ Verify(R_i, bind R m, σ)`. A ring signature is the public value
  with the proof. The base message `bind R m` is the ring
  message itself for converted signatures (`bind R m = m`) or a message binding the ring.
  `ringRel adm bind` restricts the relation to the admissible rings `adm` (the ring sizes a
  circuit is compiled for).
- `RingOf PK N`: rings of at most `N` keys, the finite type of the rings in statements and
  requests.
- `BaseRequest`, `BaseResponse`, `baseAnswer`: the oracles of the multi-user signature game
  (public key, signature, corruption returning the key-generation coins), the signing oracle
  answering at signing coins drawn for the request.

## Sources

Ring-signature syntax: Bender, Katz, Morselli, "Ring Signatures: Stronger Definitions, and
Constructions without Random Oracles", TCC 2006 (BKM06), Definition 1 (ePrint 2005/304, p. 3):
`Gen`, `Sign_{s,SK}(M, R)` for a ring `R` containing the signer's key, `Vrfy_R(M, σ)`. Here
`Sign` draws a base signature `σ` on `bind R M` with the signer's key and fresh signing coins, and
outputs `(pub σ, π)` with `π` a proof of the ring relation for `(R, M, pub σ)` by the compiled
honest prover of the BCS transformation; `Vrfy_R(M, (ρ, π))` is the compiled verifier on the
statement `(R, M, ρ)`.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS
open scoped ENNReal

/-- **A digital signature scheme** (key generation, signing and verification; Goldwasser, Micali,
Rivest, SIAM J. Comput. 17(2), 1988, section 2; written with explicit coins). Key generation is a
function of uniform coins `KeyCoins`. Signing draws its coins `c : SignCoins` uniformly (for
Falcon these include the salt `r`, specification v1.2 Algorithm 10, p. 39, line 1) and computes
`signWith sk m c`. `pub σ` is the public value of a signature, read off the signature: the part of
it that the ring statement fixes (Falcon's salt, which `HashToPoint(r ‖ m)` needs outside the
circuit; `Unit` for ML-DSA; `w₁` for the ring that publishes it). Verification is deterministic.
The scheme holds types only: the finiteness, decidable equality and nonemptiness the games read
(messages are a finite type, of bounded length) are instance-implicit binders on its projections
(`[Fintype Sch.Msg]`), found by instance search on the named types of a concrete scheme. -/
structure SigScheme where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- Messages. -/
  Msg : Type
  /-- Signatures. -/
  Sig : Type
  /-- The public value of a signature (Falcon's salt). -/
  Pub : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- The coins of signing. -/
  SignCoins : Type
  /-- Key generation from its coins. -/
  keyGen : KeyCoins → PK × SK
  /-- The public value of a signature. -/
  pub : Sig → Pub
  /-- Signing with drawn coins. -/
  signWith : SK → Msg → SignCoins → Sig
  /-- Verification. -/
  verify : PK → Msg → Sig → Bool

namespace SigScheme

variable (Sch : SigScheme)

/-- The public key generated from the coins `kc`. -/
def pk (kc : Sch.KeyCoins) : Sch.PK := (Sch.keyGen kc).1

/-- The secret key generated from the coins `kc`. -/
def sk (kc : Sch.KeyCoins) : Sch.SK := (Sch.keyGen kc).2

/-- **The correctness error of the scheme is at most `ε`** (a property of the scheme): for every
key-generation coins `kc` and message `m`, a signature computed with the secret key of `kc` and
uniform signing coins fails to verify under the public key of `kc` with probability at most `ε`.
A bounded signer can fail: the vendored Falcon verifier rejects when the bounded `HashToPoint`
runs out of candidates for the drawn salt, and ML-DSA's rejection loop is truncated by the finite
signing coins. -/
def CorrectWithin [Fintype Sch.SignCoins] [Nonempty Sch.SignCoins] (ε : ℝ≥0∞) : Prop :=
  ∀ kc m, (PMF.uniformOfFintype Sch.SignCoins).toOuterMeasure
    {c | Sch.verify (Sch.pk kc) m (Sch.signWith (Sch.sk kc) m c) ≠ true} ≤ ε

/-- **Perfect correctness of the scheme**: a signature computed with an honestly generated secret
key verifies under the matching public key, for every message and coins. -/
def Correct : Prop :=
  ∀ kc m c, Sch.verify (Sch.pk kc) m (Sch.signWith (Sch.sk kc) m c) = true

variable {Sch} in
/-- A perfectly correct scheme has correctness error `0`. -/
theorem Correct.correctWithin [Fintype Sch.SignCoins] [Nonempty Sch.SignCoins] (h : Sch.Correct) :
    Sch.CorrectWithin 0 := fun kc m => by
  have : {c | Sch.verify (Sch.pk kc) m (Sch.signWith (Sch.sk kc) m c) ≠ true} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun c hc => hc (h kc m c)
  rw [this, MeasureTheory.measure_empty]

/-- **The public value of an honest signature is a function of the signing coins**: for every
key-generation coins `kc` and message `m`, `pub (signWith sk_kc m c) = pubOf c`. For Falcon `pubOf`
reads the salt from the coins; for `Pub = Unit` it holds for every scheme. The simulated ring
signatures of the unforgeability proof draw their public values this way, without a secret key. -/
def PubOfCoins (pubOf : Sch.SignCoins → Sch.Pub) : Prop :=
  ∀ kc m c, Sch.pub (Sch.signWith (Sch.sk kc) m c) = pubOf c

end SigScheme

variable {Sch : SigScheme}

/-- **Rings of at most `N` keys**, the finite type of the rings that statements and requests
carry. -/
abbrev RingOf (PK : Type) (N : ℕ) : Type := {l : List PK // l.length ≤ N}

/-- **The rings of at most `N` keys are a finite type**, enumerated through the vectors of each
length (`List.fintypeLengthLe`): compiled code, and no decision of equality on keys. -/
instance (PK : Type) [Fintype PK] (N : ℕ) : Fintype (RingOf PK N) :=
  List.fintypeLengthLe PK N

/-- **A ring statement** with rings of at most `N` keys: a ring of public keys, a ring message,
and the public value of the signature (Falcon's salt, which the statement fixes because
`HashToPoint(r ‖ m)` is computed outside the circuit; `Unit` for ML-DSA). The bound `N` makes the
statements a finite type, as a transcript format with bounded statement writes needs. -/
structure RingStmt (Sch : SigScheme) (RMsg : Type) (N : ℕ) where
  /-- The ring. -/
  ring : RingOf Sch.PK N
  /-- The ring message. -/
  msg : RMsg
  /-- The public value of the signature. -/
  pub : Sch.Pub

/-- **A ring witness**: the signer's position in the ring and a base signature. -/
structure RingWit (Sch : SigScheme) where
  /-- The position of the signer's key in the ring. -/
  idx : ℕ
  /-- The base signature. -/
  sig : Sch.Sig

/-! The decidable equality of statements and witnesses is the definition `deriving DecidableEq`
generates, written out: it reads the instances of the field types `Sch.PK`, `Sch.Pub` and `Sch.Sig`
from binders, which a deriving handler does not see. -/

section DecEq

/-- Decidable equality of ring statements, field by field. -/
def instDecidableEqRingStmt.decEq {RMsg : Type} {N : ℕ} [DecidableEq RMsg] [DecidableEq Sch.PK]
    [DecidableEq Sch.Pub] (x y : RingStmt Sch RMsg N) : Decidable (x = y) :=
  match x, y with
  | @RingStmt.mk _ _ _ a0 a1 a2, @RingStmt.mk _ _ _ b0 b1 b2 =>
    if h0 : @a0 = @b0 then by
      subst h0
      exact
        if h1 : @a1 = @b1 then by
          subst h1
          exact
            if h2 : @a2 = @b2 then by subst h2; exact isTrue rfl
            else isFalse (by intro n; injection n; apply h2 _; assumption)
        else isFalse (by intro n; injection n; apply h1 _; assumption)
    else isFalse (by intro n; injection n; apply h0 _; assumption)

instance instDecidableEqRingStmt {RMsg : Type} {N : ℕ} [DecidableEq RMsg] [DecidableEq Sch.PK]
    [DecidableEq Sch.Pub] : DecidableEq (RingStmt Sch RMsg N) :=
  instDecidableEqRingStmt.decEq

/-- Decidable equality of ring witnesses, field by field. -/
def instDecidableEqRingWit.decEq [DecidableEq Sch.Sig] (x y : RingWit Sch) : Decidable (x = y) :=
  match x, y with
  | @RingWit.mk _ a0 a1, @RingWit.mk _ b0 b1 =>
    if h0 : @a0 = @b0 then by
      subst h0
      exact
        if h1 : @a1 = @b1 then by subst h1; exact isTrue rfl
        else isFalse (by intro n; injection n; apply h1 _; assumption)
    else isFalse (by intro n; injection n; apply h0 _; assumption)

instance instDecidableEqRingWit [DecidableEq Sch.Sig] : DecidableEq (RingWit Sch) :=
  instDecidableEqRingWit.decEq

end DecEq

variable {RMsg : Type} {N : ℕ}

/-- **The ring relation** `R_ring((R, m, ρ), (i, σ))` for the base-message map `bind`: `i` is a
position of the ring, the signature carries the statement's public value, and it verifies on the
base message `bind R m` under the key at position `i`. -/
structure RingRel (bind : List Sch.PK → RMsg → Sch.Msg) (x : RingStmt Sch RMsg N)
    (w : RingWit Sch) :
    Prop where
  /-- The position is in the ring. -/
  idx_lt : w.idx < x.ring.1.length
  /-- The signature carries the statement's public value. -/
  pub_eq : Sch.pub w.sig = x.pub
  /-- The signature verifies under the key at the position. -/
  verify_eq : Sch.verify (x.ring.1[w.idx]'idx_lt) (bind x.ring.1 x.msg) w.sig = true

/-- **The ring relation on the admissible rings as a set of statement-witness pairs**: the ring
satisfies `adm` (the rings the scheme supports, for example exactly `256` keys for a circuit
compiled at that ring size; `fun _ => True` for all rings of at most `N` keys), and `RingRel`. -/
def ringRel (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg) :
    Set (RingStmt Sch RMsg N × RingWit Sch) :=
  {p | adm p.1.ring.1 ∧ RingRel bind p.1 p.2}

theorem mem_ringRel_iff {adm : List Sch.PK → Prop} {bind : List Sch.PK → RMsg → Sch.Msg}
    {x : RingStmt Sch RMsg N} {w : RingWit Sch} :
    (x, w) ∈ ringRel adm bind ↔ adm x.ring.1 ∧ RingRel bind x w :=
  Iff.rfl

/-- **An honest member's verifying signature is a ring witness**: a signature computed with the
secret key of honestly generated coins `kc`, whose public key is at position `i` of the ring, is a
witness for the statement with its public value, when it verifies (`hv`). -/
theorem RingRel.of_signWith {bind : List Sch.PK → RMsg → Sch.Msg}
    {R : RingOf Sch.PK N} {m : RMsg} {kc : Sch.KeyCoins} {i : ℕ} (hi : i < R.1.length)
    (hR : R.1[i] = Sch.pk kc) {c : Sch.SignCoins}
    (hv : Sch.verify (Sch.pk kc) (bind R.1 m) (Sch.signWith (Sch.sk kc) (bind R.1 m) c) = true) :
    RingRel bind ⟨R, m, Sch.pub (Sch.signWith (Sch.sk kc) (bind R.1 m) c)⟩
      ⟨i, Sch.signWith (Sch.sk kc) (bind R.1 m) c⟩ where
  idx_lt := hi
  pub_eq := rfl
  verify_eq := by
    simp only [hR]
    exact hv

variable (N) in
/-- **The base message binds the ring and the message** on the rings of at most `N` keys: on such
rings, `bind R m = bind R' m'` gives `R = R'` and `m = m'`. (Injectivity on all lists is
impossible: `Msg` is finite and `List PK` is not.) -/
def BindsRing (bind : List Sch.PK → RMsg → Sch.Msg) : Prop :=
  ∀ (R R' : RingOf Sch.PK N) (m m' : RMsg), bind R.1 m = bind R'.1 m' → R.1 = R'.1 ∧ m = m'

variable (N) in
/-- **The base message of an encoding** `enc` of a ring of at most `N` keys and a ring message (a
longer list is read as the empty ring). -/
def bindOfEncoding (enc : RingOf Sch.PK N × RMsg → Sch.Msg) (R : List Sch.PK) (m : RMsg) :
    Sch.Msg :=
  if h : R.length ≤ N then enc (⟨R, h⟩, m) else enc (⟨[], Nat.zero_le _⟩, m)

/-- **An injective encoding binds the ring**: `BindsRing` is satisfiable whenever `Msg` is large
enough to encode a ring of at most `N` keys and a ring message. -/
theorem bindsRing_bindOfEncoding {enc : RingOf Sch.PK N × RMsg → Sch.Msg}
    (henc : Function.Injective enc) : BindsRing N (bindOfEncoding N enc) := by
  intro R R' m m' h
  simp only [bindOfEncoding, dif_pos R.2, dif_pos R'.2] at h
  have h' := henc h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h'
  exact h'

/-- The key at the witness's position is a member of the ring. -/
theorem RingRel.mem_ring {bind : List Sch.PK → RMsg → Sch.Msg} {x : RingStmt Sch RMsg N}
    {w : RingWit Sch} (h : RingRel bind x w) : x.ring.1[w.idx]'h.idx_lt ∈ x.ring.1 :=
  List.getElem_mem _

/-! ### The oracles of the multi-user signature game -/

variable (Sch) (n : ℕ)

/-- **A request to the oracles of the multi-user signature game with corruption**: the public
key of user `i`, a signature by user `i` on a message, or the corruption of user `i`. -/
inductive BaseRequest where
  /-- The public key of user `i`. -/
  | publicKey (i : Fin n)
  /-- A signature by user `i` on `m`. -/
  | sign (i : Fin n) (m : Sch.Msg)
  /-- The corruption of user `i`. -/
  | corrupt (i : Fin n)

/-! The decidable equality and finiteness of requests are the definitions `deriving DecidableEq,
Fintype` generate, written out: they read the instances of `Sch.Msg` from binders. -/

section BaseRequestInstances

variable {Sch n}

/-- Decidable equality of requests, constructor by constructor and field by field. -/
def instDecidableEqBaseRequest.decEq [DecidableEq Sch.Msg] (x y : BaseRequest Sch n) :
    Decidable (x = y) :=
  match x, y with
  | @BaseRequest.publicKey _ _ a0, @BaseRequest.publicKey _ _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)
  | BaseRequest.publicKey .., BaseRequest.sign .. => isFalse (by intro h; injection h)
  | BaseRequest.publicKey .., BaseRequest.corrupt .. => isFalse (by intro h; injection h)
  | BaseRequest.sign .., BaseRequest.publicKey .. => isFalse (by intro h; injection h)
  | @BaseRequest.sign _ _ a0 a1, @BaseRequest.sign _ _ b0 b1 =>
    if h0 : @a0 = @b0 then by
      subst h0
      exact
        if h1 : @a1 = @b1 then by subst h1; exact isTrue rfl
        else isFalse (by intro n; injection n; apply h1 _; assumption)
    else isFalse (by intro n; injection n; apply h0 _; assumption)
  | BaseRequest.sign .., BaseRequest.corrupt .. => isFalse (by intro h; injection h)
  | BaseRequest.corrupt .., BaseRequest.publicKey .. => isFalse (by intro h; injection h)
  | BaseRequest.corrupt .., BaseRequest.sign .. => isFalse (by intro h; injection h)
  | @BaseRequest.corrupt _ _ a0, @BaseRequest.corrupt _ _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)

instance instDecidableEqBaseRequest [DecidableEq Sch.Msg] : DecidableEq (BaseRequest Sch n) :=
  instDecidableEqBaseRequest.decEq

instance instFintypeBaseRequest [Fintype Sch.Msg] : Fintype (BaseRequest Sch n) :=
  derive_fintype% _

end BaseRequestInstances

variable {Sch n} in
/-- The request is a signing request. -/
def BaseRequest.isSign : BaseRequest Sch n → Bool
  | .sign _ _ => true
  | _ => false

/-- **An answer of the oracles of the multi-user signature game.** -/
inductive BaseResponse where
  /-- A public key. -/
  | publicKey (pk : Sch.PK)
  /-- A signature. -/
  | signature (σ : Sch.Sig)
  /-- The key-generation coins of a corrupted user. -/
  | keyCoins (kc : Sch.KeyCoins)

/-! The decidable equality and finiteness of answers are the definitions `deriving DecidableEq,
Fintype` generate, written out: they read the instances of `Sch.PK`, `Sch.Sig` and `Sch.KeyCoins`
from binders. -/

section BaseResponseInstances

variable {Sch}

/-- Decidable equality of answers, constructor by constructor. -/
def instDecidableEqBaseResponse.decEq [DecidableEq Sch.PK] [DecidableEq Sch.Sig]
    [DecidableEq Sch.KeyCoins] (x y : BaseResponse Sch) : Decidable (x = y) :=
  match x, y with
  | @BaseResponse.publicKey _ a0, @BaseResponse.publicKey _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)
  | BaseResponse.publicKey .., BaseResponse.signature .. => isFalse (by intro h; injection h)
  | BaseResponse.publicKey .., BaseResponse.keyCoins .. => isFalse (by intro h; injection h)
  | BaseResponse.signature .., BaseResponse.publicKey .. => isFalse (by intro h; injection h)
  | @BaseResponse.signature _ a0, @BaseResponse.signature _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)
  | BaseResponse.signature .., BaseResponse.keyCoins .. => isFalse (by intro h; injection h)
  | BaseResponse.keyCoins .., BaseResponse.publicKey .. => isFalse (by intro h; injection h)
  | BaseResponse.keyCoins .., BaseResponse.signature .. => isFalse (by intro h; injection h)
  | @BaseResponse.keyCoins _ a0, @BaseResponse.keyCoins _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)

instance instDecidableEqBaseResponse [DecidableEq Sch.PK] [DecidableEq Sch.Sig]
    [DecidableEq Sch.KeyCoins] : DecidableEq (BaseResponse Sch) :=
  instDecidableEqBaseResponse.decEq

instance instFintypeBaseResponse [Fintype Sch.PK] [Fintype Sch.Sig] [Fintype Sch.KeyCoins] :
    Fintype (BaseResponse Sch) :=
  derive_fintype% _

end BaseResponseInstances

variable {Sch n}

/-- **The answer of the oracles** with the users' key-generation coins `keys`, at the signing coins
`c` drawn for the current request: the public key; a signature `signWith sk_i m c`; the
key-generation coins (corruption returns the coins, as in BKP20 p. 7 and CCLM22 Experiment 3,
p. 21; this reveals at least the secret key). -/
def baseAnswer (keys : Fin n → Sch.KeyCoins) (c : Sch.SignCoins) :
    BaseRequest Sch n → BaseResponse Sch
  | .publicKey i => .publicKey (Sch.pk (keys i))
  | .sign i m => .signature (Sch.signWith (Sch.sk (keys i)) m c)
  | .corrupt i => .keyCoins (keys i)

end GordieHowe.Ring
