-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.NARG.OracleProg
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Probability.Distributions.Uniform

public section

/-!
# Ring signature schemes in the random-oracle model

The one object every ring-signature game of the library takes (`RingScheme`), after Bender,
Katz, Morselli, "Ring Signatures: Stronger Definitions, and Constructions without Random
Oracles", TCC 2006 (BKM06), Definition 1 (ePrint 2005/304, p. 3): `Gen`, `Sign_{s,SK}(M, R)` and
`Vrfy_R(M, σ)`, here written with explicit coins and a random oracle `X → Y`.

- `KeyRing PK N`: rings, ordered lists of at most `N` public keys; a finite type for finite `PK`.
- `RingScheme X Y N`: keys from uniform key-generation coins; signing, a classical oracle program
  over the random oracle with at most `q` queries, from the signer's key pair, a ring, a message
  and uniform signing coins, which may refuse (`none`, BKM06's `⊥`); verification, a function of
  the oracle; and the rings the scheme supports (`Supported`, the ring sizes a circuit is compiled
  for). `RingScheme.pk`, `RingScheme.sk`: the keys generated from key-generation coins.
- `RingScheme.RefusesOutside`: the signer refuses every ring that does not hold its public key and
  every unsupported ring.
- `RingScheme.signLaw`: the law of the signer's output at an oracle.
- `OracleProg.QueriesLE.queryAll`, `OracleProg.QueriesLE.iterate`: query bounds of the program
  combinators the constructions use (those of `pure`, `bind`, `query` and `tabulate` are in
  `GordieHowe/Model/NARG/OracleProg.lean`).

## Comparison with BKM06 Definition 1

Each deliberate difference, and why it is made:

1. **Rings are ordered lists of at most `N` keys, unsorted, repetitions allowed.** BKM06 orders the
   keys lexicographically "without loss of generality" and assumes them distinct (p. 3, footnote
   3: the signer may pass to the sub-ring of distinct keys). Lists let every game quantify over
   the order and the repetitions too; BKM06's sorted repetition-free rings are among them. The
   bound `N` makes rings a finite type, which the requests of the
   interactive model need (`Quantum.Challenger`); a scheme's own size limits are `Supported`.
2. **The signer locates its own key.** BKM06's `Sign_{s,SK}` takes the index `s` with
   `(R[s], SK)` a key pair and then omits it (p. 3: "the signer can determine an index `s`").
   Here `sign` takes the signer's key pair `(PK, SK)` and finds its key in the ring itself, so
   the games never hand the signer a position; with repeated keys the scheme chooses which
   position to use.
3. **Signing may refuse.** BKM06's `Sign` assumes `R[s]` is the signer's key, `|R| ≥ 2` and
   distinct keys, and leaves other inputs unspecified. Here `sign` returns `none` (`⊥`) for rings
   it does not sign on: a ring without the signer's key, an unsupported ring (`RefusesOutside`),
   or one its own rule refuses (the public check of the ML-DSA ring publishing `w₁`). BKM06's
   `c`-user variant (p. 4) is `Supported` holding for the rings of size `c`. Rings of one key are
   allowed; `Supported` may exclude them.
4. **Explicit coins and a random oracle.** BKM06's algorithms are ppt; here key generation is a
   function of uniform finite coins (the games hand out these coins, BKM06's `ω_i` of Definition
   4), signing a function of uniform finite coins, and all algorithms read one random oracle
   `X → Y`. The signer makes at most `q` classical
   queries, the form in which the challengers of the interactive quantum model run it
   (`Quantum.Challenger.respond`); verification is a function of the whole oracle, read only in the
   games' final checks. There is no security parameter: the games are concrete.
5. **Completeness is a game with an error** (`GordieHowe/Model/RingSignature/Completeness.lean`).
-/

namespace GordieHowe

namespace OracleProg

variable {A B R S : Type*}

/-- **A query to each element of a list** makes as many queries as the list has elements. -/
theorem QueriesLE.queryAll (l : List A) :
    (queryAll l : OracleProg A B (List B)).QueriesLE l.length :=
  fun h => by rw [trace_queryAll]

/-- **The query bound of an iteration**: `m` steps with at most `q` queries each make at most
`m · q` queries. -/
theorem QueriesLE.iterate {step : ℕ → S → OracleProg A B S} {q : ℕ}
    (hs : ∀ r s, (step r s).QueriesLE q) (m : ℕ) (s : S) :
    (OracleProg.iterate step m s).QueriesLE (m * q) := fun h =>
  (length_trace_iterate_le h step (fun _ => q) (fun r s => hs r s h) m s).trans (by simp)

end OracleProg

namespace RingSignature

/-- **A ring**: an ordered list of at most `N` public keys (BKM06 p. 3, "an ordered list
`R = (PK_1, …, PK_n)` of public keys"; here unsorted, with repetitions allowed). -/
abbrev KeyRing (PK : Type) (N : ℕ) : Type := {l : List PK // l.length ≤ N}

/-- **The rings as a finite set**: the lists of the functions `Fin k → PK` for `k ≤ N`
(`List.ofFn`). Irreducible, so that unification does not evaluate the enumeration. -/
@[irreducible] def keyRingFinset (PK : Type) [Fintype PK] [DecidableEq PK] (N : ℕ) :
    Finset (KeyRing PK N) :=
  ((Finset.range (N + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → PK)).image List.ofFn).subtype (·.length ≤ N)

/-- **Every ring is in `keyRingFinset`.** -/
theorem mem_keyRingFinset (PK : Type) [Fintype PK] [DecidableEq PK] (N : ℕ) (R : KeyRing PK N) :
    R ∈ keyRingFinset PK N := by
  obtain ⟨l, hl⟩ := R
  rw [keyRingFinset, Finset.mem_subtype]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨l.length, Nat.lt_succ_of_le hl, fun i => l.get i, List.ofFn_get l⟩

/-- **The rings are finite** (`keyRingFinset`). -/
instance (PK : Type) [Fintype PK] [DecidableEq PK] (N : ℕ) : Fintype (KeyRing PK N) :=
  ⟨keyRingFinset PK N, mem_keyRingFinset PK N⟩

/-- **The types of a ring signature scheme**: public keys, secret keys, messages, signatures and
the coins of key generation and of signing. A `RingScheme` takes its types as this parameter, so the
types of a constructed scheme are computed from types data and never read back from the scheme.
The record holds types only: the finiteness and decidable equality the games read are
instance-implicit binders on its projections (`[Fintype T.PK]`), found by instance search on the
named types of a concrete record. -/
structure RingTypes where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- Messages. -/
  Msg : Type
  /-- Signatures. -/
  Sig : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- The coins of signing. -/
  SignCoins : Type

/-- **A ring signature scheme in the random-oracle model** (BKM06 Definition 1, ePrint 2005/304,
p. 3) with the random oracle `X → Y`, rings of at most `N` keys and the types `T`: key generation
from uniform coins; signing, a classical oracle program making at most `q` queries, from the
signer's key pair, a ring, a message and uniform signing coins, which returns a signature or
refuses (`none`); verification, a function of the oracle; and the rings the scheme supports. -/
structure RingScheme (X Y : Type) (N : ℕ) (T : RingTypes) where
  /-- Key generation from its coins. -/
  keyGen : T.KeyCoins → T.PK × T.SK
  /-- The bound on the signer's oracle queries. -/
  q : ℕ
  /-- Signing by the key pair `kp` on a ring and a message with drawn coins; `none` is a
  refusal. -/
  sign : T.PK × T.SK → KeyRing T.PK N → T.Msg → T.SignCoins → OracleProg X Y (Option T.Sig)
  /-- The signer makes at most `q` queries. -/
  sign_queries : ∀ kp R m c, (sign kp R m c).QueriesLE q
  /-- Verification at an oracle. -/
  verify : (X → Y) → KeyRing T.PK N → T.Msg → T.Sig → Bool
  /-- The rings the scheme supports. -/
  Supported : KeyRing T.PK N → Prop

namespace RingScheme

variable {X Y : Type} {N : ℕ} {T : RingTypes}

/-- Public keys: those of the types `T`. -/
abbrev PK (_ : RingScheme X Y N T) : Type := T.PK

/-- Secret keys: those of the types `T`. -/
abbrev SK (_ : RingScheme X Y N T) : Type := T.SK

/-- Messages: those of the types `T`. -/
abbrev Msg (_ : RingScheme X Y N T) : Type := T.Msg

/-- Signatures: those of the types `T`. -/
abbrev Sig (_ : RingScheme X Y N T) : Type := T.Sig

/-- The coins of key generation: those of the types `T`. -/
abbrev KeyCoins (_ : RingScheme X Y N T) : Type := T.KeyCoins

/-- The coins of signing: those of the types `T`. -/
abbrev SignCoins (_ : RingScheme X Y N T) : Type := T.SignCoins

variable (S : RingScheme X Y N T)

/-- The public key generated from the coins `kc`. -/
@[expose] def pk (kc : S.KeyCoins) : S.PK := (S.keyGen kc).1

/-- The secret key generated from the coins `kc`. -/
@[expose] def sk (kc : S.KeyCoins) : S.SK := (S.keyGen kc).2

/-- **The signer refuses outside its rings**: signing returns `none`, at every oracle, on every ring
that does not hold the signer's public key and on every unsupported ring. -/
def RefusesOutside : Prop :=
  ∀ (kp : S.PK × S.SK) (R : KeyRing S.PK N) (m : S.Msg) (c : S.SignCoins) (H : X → Y),
    (kp.1 ∉ R.1 ∨ ¬ S.Supported R) → (S.sign kp R m c).run H = none

/-- `RefusesOutside`, unfolded. -/
theorem refusesOutside_iff : S.RefusesOutside ↔
    ∀ (kp : S.PK × S.SK) (R : KeyRing S.PK N) (m : S.Msg) (c : S.SignCoins) (H : X → Y),
      (kp.1 ∉ R.1 ∨ ¬ S.Supported R) → (S.sign kp R m c).run H = none := by
  rw [RefusesOutside]

section Laws

variable [Fintype T.SignCoins] [Nonempty T.SignCoins]

/-- **The law of the signer's output** at the oracle `H`: the signing coins uniform. -/
noncomputable def signLaw (H : X → Y) (kp : S.PK × S.SK) (R : KeyRing S.PK N) (m : S.Msg) :
    PMF (Option S.Sig) :=
  (PMF.uniformOfFintype S.SignCoins).map fun c => (S.sign kp R m c).run H

/-- `signLaw`, unfolded. -/
theorem signLaw_eq (H : X → Y) (kp : S.PK × S.SK) (R : KeyRing S.PK N) (m : S.Msg) :
    S.signLaw H kp R m = (PMF.uniformOfFintype S.SignCoins).map fun c => (S.sign kp R m c).run H := by
  rw [signLaw]

end Laws

end RingScheme

end RingSignature

end GordieHowe
