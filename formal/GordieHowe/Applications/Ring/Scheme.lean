-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.IOP
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Set.Finite.List

@[expose] public section

/-!
# Ring signatures from a signature scheme and a BCS argument: syntax and relation

The objects of the ring-signature construction, generic in the base signature scheme and in the IOP
(no circuit is fixed here).

- `SigScheme`: a signature scheme with key generation from uniform coins, signing from a uniform
  public per-signature value (`Pub`: Falcon's salt `r`, `Unit` for ML-DSA) and uniform private
  coins, and a deterministic verifier. `SigScheme.Correct`: honest signatures carry the drawn
  public value and verify under honestly generated keys.
- `RingStmt`, `RingWit`, `RingRel bind`: the statement `(R, m, ρ)` (a ring of public keys, a
  ring message, the public value of the signature), the witness `(i, σ)`, and the ring relation
  `i < |R| ∧ pub σ = ρ ∧ Verify(R_i, bind R m, σ)`. The base message `bind R m` is the ring
  message itself for converted signatures (`bind R m = m`) or a message binding the ring.
  `ringRel adm bind` restricts the relation to the admissible rings `adm` (the ring sizes a
  circuit is compiled for).
- `RingOf PK N`: rings of at most `N` keys, the finite type of the rings in statements and
  requests.
- `BaseRequest`, `BaseResponse`, `baseAnswer`: the oracles of the multi-user signature game
  (public key, signature, corruption returning the key-generation coins).

## Sources

Ring-signature syntax: Bender, Katz, Morselli, "Ring Signatures: Stronger Definitions, and
Constructions without Random Oracles", TCC 2006 (BKM06), Definition 1 (ePrint 2005/304, p. 3):
`Gen`, `Sign_{s,SK}(M, R)` for a ring `R` containing the signer's key, `Vrfy_R(M, σ)`. Here
`Sign` draws a base signature on `bind R M` with the signer's key and proves the ring relation
with the compiled honest prover of the BCS transformation; `Vrfy_R(M, π)` is the compiled verifier
on the statement `(R, M, ρ)`.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS

/-- **A digital signature scheme** (key generation, signing and verification; Goldwasser, Micali,
Rivest, SIAM J. Comput. 17(2), 1988, section 2; written with explicit coins). Key generation is a
function of uniform coins `KeyCoins`. Signing draws a public value `ρ : Pub` uniformly (Falcon's
salt `r`, specification v1.2 Algorithm 10, p. 39, line 1; `Unit` for ML-DSA) and private coins
uniformly, and computes `signWith sk m ρ c`; `pub σ` reads the public value back from a signature.
Verification is deterministic. Messages are a finite type (messages of bounded length). -/
structure SigScheme where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- Messages. -/
  Msg : Type
  /-- Signatures. -/
  Sig : Type
  /-- The public per-signature value (Falcon's salt). -/
  Pub : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- The private coins of signing. -/
  SignCoins : Type
  [instFintypePK : Fintype PK]
  [instDecEqPK : DecidableEq PK]
  [instFintypeMsg : Fintype Msg]
  [instDecEqMsg : DecidableEq Msg]
  [instFintypeSig : Fintype Sig]
  [instDecEqSig : DecidableEq Sig]
  [instFintypePub : Fintype Pub]
  [instDecEqPub : DecidableEq Pub]
  [instNonemptyPub : Nonempty Pub]
  [instFintypeKeyCoins : Fintype KeyCoins]
  [instDecEqKeyCoins : DecidableEq KeyCoins]
  [instNonemptyKeyCoins : Nonempty KeyCoins]
  [instFintypeSignCoins : Fintype SignCoins]
  [instDecEqSignCoins : DecidableEq SignCoins]
  [instNonemptySignCoins : Nonempty SignCoins]
  /-- Key generation from its coins. -/
  keyGen : KeyCoins → PK × SK
  /-- The public value of a signature. -/
  pub : Sig → Pub
  /-- Signing with a drawn public value and private coins. -/
  signWith : SK → Msg → Pub → SignCoins → Sig
  /-- Verification. -/
  verify : PK → Msg → Sig → Bool

attribute [instance] SigScheme.instFintypePK SigScheme.instDecEqPK SigScheme.instFintypeMsg
  SigScheme.instDecEqMsg SigScheme.instFintypeSig SigScheme.instDecEqSig SigScheme.instFintypePub
  SigScheme.instDecEqPub SigScheme.instNonemptyPub SigScheme.instFintypeKeyCoins
  SigScheme.instDecEqKeyCoins SigScheme.instNonemptyKeyCoins SigScheme.instFintypeSignCoins
  SigScheme.instDecEqSignCoins SigScheme.instNonemptySignCoins

namespace SigScheme

variable (Sch : SigScheme)

/-- The public key generated from the coins `kc`. -/
def pk (kc : Sch.KeyCoins) : Sch.PK := (Sch.keyGen kc).1

/-- The secret key generated from the coins `kc`. -/
def sk (kc : Sch.KeyCoins) : Sch.SK := (Sch.keyGen kc).2

/-- **Perfect correctness of the scheme** (a property of the scheme, discharged for a concrete
scheme by its specification): a signature computed with an honestly generated secret key carries
the drawn public value and verifies under the matching public key, for every message, public
value and coins. Falcon and ML-DSA sign by rejection sampling until the signature passes their
verifier's checks, so their correctness has no failure probability. -/
structure Correct : Prop where
  /-- The public value of an honest signature is the drawn one. -/
  pub_signWith : ∀ kc m ρ c, Sch.pub (Sch.signWith (Sch.sk kc) m ρ c) = ρ
  /-- An honest signature verifies. -/
  verify_signWith : ∀ kc m ρ c, Sch.verify (Sch.pk kc) m (Sch.signWith (Sch.sk kc) m ρ c) = true

end SigScheme

variable {Sch : SigScheme}

/-- **Rings of at most `N` keys**, the finite type of the rings that statements and requests
carry. -/
abbrev RingOf (PK : Type) (N : ℕ) : Type := {l : List PK // l.length ≤ N}

noncomputable instance (PK : Type) [Finite PK] (N : ℕ) : Fintype (RingOf PK N) :=
  (List.finite_length_le PK N).fintype

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
deriving DecidableEq

/-- **A ring witness**: the signer's position in the ring and a base signature. -/
structure RingWit (Sch : SigScheme) where
  /-- The position of the signer's key in the ring. -/
  idx : ℕ
  /-- The base signature. -/
  sig : Sch.Sig
deriving DecidableEq

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

/-- **An honest member's signature is a ring witness**: a signature computed with the secret key
of honestly generated coins `kc`, whose public key is at position `i` of the ring, is a witness
for the statement with the drawn public value. -/
theorem RingRel.of_signWith (h : Sch.Correct) {bind : List Sch.PK → RMsg → Sch.Msg}
    {R : RingOf Sch.PK N} {m : RMsg} {kc : Sch.KeyCoins} {i : ℕ} (hi : i < R.1.length)
    (hR : R.1[i] = Sch.pk kc) (ρ : Sch.Pub) (c : Sch.SignCoins) :
    RingRel bind ⟨R, m, ρ⟩ ⟨i, Sch.signWith (Sch.sk kc) (bind R.1 m) ρ c⟩ where
  idx_lt := hi
  pub_eq := h.pub_signWith kc _ ρ c
  verify_eq := by
    simp only [hR]
    exact h.verify_signWith kc _ ρ c

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
deriving DecidableEq, Fintype

/-- **An answer of the oracles of the multi-user signature game.** -/
inductive BaseResponse where
  /-- A public key. -/
  | publicKey (pk : Sch.PK)
  /-- A signature. -/
  | signature (σ : Sch.Sig)
  /-- The key-generation coins of a corrupted user. -/
  | keyCoins (kc : Sch.KeyCoins)
deriving DecidableEq, Fintype

variable {Sch n}

/-- **The answer of the oracles** with the users' key-generation coins `keys`, at the public
value `ρ` and the private coins `c` drawn for the current request: the public key; a signature
`signWith sk_i m ρ c`; the key-generation coins (corruption returns the coins, as in BKP20 p. 7
and CCLM22 Experiment 3, p. 21; this reveals at least the secret key). -/
def baseAnswer (keys : Fin n → Sch.KeyCoins) (ρ : Sch.Pub) (c : Sch.SignCoins) :
    BaseRequest Sch n → BaseResponse Sch
  | .publicKey i => .publicKey (Sch.pk (keys i))
  | .sign i m => .signature (Sch.signWith (Sch.sk (keys i)) m ρ c)
  | .corrupt i => .keyCoins (keys i)

end GordieHowe.Ring
