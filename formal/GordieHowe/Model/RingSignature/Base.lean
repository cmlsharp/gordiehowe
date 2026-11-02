-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Scheme
public import GordieHowe.Model.NARG.Prover

public section

/-!
# Ring signatures from a base signer and a proof system

The construction of the library's ring signatures as one `RingScheme` (`ofBase`): a ring signature
on `(R, m)` is a public value `y` with a proof `π` of the ring relation for the statement `(R, m, y)`,
the witness being the signer's position and a base signature.

- `BaseSigner X Y N`: what a ring signature proves knowledge of: the base scheme's keys (FIPS 204,
  FIPS 206), the base message of a ring and a message (`bmsg`: `m`, or `m ‖ encode R`), the
  ring-aware base signer `bsign` (from the secret key, the ring, the signer's position, the message
  and coins; it may refuse), the base scheme's ordinary signer `ssign` on base messages (for the
  key-reuse game), base verification `bverify` at the oracle, and the public value of a base
  signature (`pub`: Falcon's salt, `Unit`, or ML-DSA's `w₁` recomputed from the key and the
  signature), a classical oracle program.
- `RingStmtOf`, `RingWitOf`: statements and witnesses, depending only on the base signer's key,
  message, public-value and signature types.
- `RingStmt B`, `RingWit B`, `RingRel B adm H`, `ringRel B adm H`: statements `(R, m, y)`, witnesses
  `(i, σ)` and the ring relation at the oracle `H` on the supported rings `adm`:
  `adm R ∧ i < |R| ∧ bverify_H(R_i, bmsg R m, σ) ∧ pub_H(R_i, σ) = y`.
  `ringRel_mono`: fewer supported rings give a smaller relation.
- `ProofSystem X Y Stmt Wit`: a non-interactive proof system with an honest prover (a classical
  oracle program from a statement, a witness and uniform coins) and a verifier at the oracle;
  `ProofSystem.prover`, `ProofSystem.ofProver`: as a `NARG.Prover` and back.
- `ofBase B adm PS`: the ring scheme. Signing locates the signer's key in the ring (its first
  position `i`), refuses rings without it and unsupported rings, runs `bsign` at `i`, computes
  `y = pub(R_i, σ)` and proves `(R, m, y)` with the witness `(i, σ)`; verification runs `PS`'s
  verifier on `(R, m, y)`.
- Sanity: `ofBase_refusesOutside`, `run_signAt_of_bsign` (an honest signature is the public value
  and the proof of the base signature), `ringRel_of_bsign` (a verifying base signature of the
  signer at its position is a witness of the statement it signs: the relation is satisfiable on
  honest signatures), `verify_ofBase`.

## Sources and deliberate differences

The construction is BKM06's generic one (ePrint 2005/304, section 5: a signature `σ'` of the
signer's standard scheme on `M ‖ PK_1 ‖ … ‖ PK_n` and a witness-indistinguishable proof that one of
the ring's keys signed it), with spBCS in place of ZAPs and encryption, and with the public value
`y` in the statement. The differences:

1. **The public value is in the statement.** A part `y` of the base signature leaves the circuit
   (Falcon's salt, which `HashToPoint` reads outside it; ML-DSA's `w₁` in the ring publishing it);
   `y = Unit` gives BKM06's shape.
2. **The base message may not bind the ring** (`bmsg R m = m`, converted signatures): BKM06 signs
   `M ‖ PK_1 ‖ … ‖ PK_n`. Which unforgeability holds depends on it (`KeyReuse.lean`).
3. **The base signer reads the ring** (`bsign` takes the ring and the position) and may refuse:
   the generic rings read it only through `bmsg`; the ML-DSA ring publishing `w₁` reads the members'
   published `t₀` and hashes for its keep decision and refuses rings failing the public check.
4. **The supported rings `adm`** are a parameter of the construction (the ring sizes the proof
   system's circuit is compiled for), enforced by the signer and by the relation.
5. **`pub` is a classical oracle program**, so the signer, itself an oracle program, can compute
   it; `bverify` is a function of the oracle, read only by the relation.
-/

namespace GordieHowe.RingSignature

open scoped ENNReal

/-- **The types of a base signer**: public keys, secret keys, the coins of key generation, ring
messages, base messages, base signatures, public values and the coins of signing, with the finiteness
and decidable equality the games read. A `BaseSigner` takes its types as this parameter. -/
structure BaseTypes where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- Ring messages. -/
  Msg : Type
  /-- Base messages. -/
  BMsg : Type
  /-- Base signatures. -/
  BSig : Type
  /-- Public values. -/
  Pub : Type
  /-- The coins of signing. -/
  Coins : Type
  [instFintypePK : Fintype PK]
  [instDecEqPK : DecidableEq PK]
  [instFintypeKeyCoins : Fintype KeyCoins]
  [instDecEqKeyCoins : DecidableEq KeyCoins]
  [instNonemptyKeyCoins : Nonempty KeyCoins]
  [instFintypeMsg : Fintype Msg]
  [instDecEqMsg : DecidableEq Msg]
  [instFintypeBMsg : Fintype BMsg]
  [instDecEqBMsg : DecidableEq BMsg]
  [instFintypeBSig : Fintype BSig]
  [instDecEqBSig : DecidableEq BSig]
  [instFintypePub : Fintype Pub]
  [instDecEqPub : DecidableEq Pub]
  [instFintypeCoins : Fintype Coins]
  [instDecEqCoins : DecidableEq Coins]
  [instNonemptyCoins : Nonempty Coins]

attribute [instance] BaseTypes.instFintypePK BaseTypes.instDecEqPK
  BaseTypes.instFintypeKeyCoins BaseTypes.instDecEqKeyCoins BaseTypes.instNonemptyKeyCoins
  BaseTypes.instFintypeMsg BaseTypes.instDecEqMsg BaseTypes.instFintypeBMsg
  BaseTypes.instDecEqBMsg BaseTypes.instFintypeBSig BaseTypes.instDecEqBSig
  BaseTypes.instFintypePub BaseTypes.instDecEqPub BaseTypes.instFintypeCoins
  BaseTypes.instDecEqCoins BaseTypes.instNonemptyCoins

/-- **A base signer** with the random oracle `X → Y` for rings of at most `N` keys and the types `T`:
the base scheme's keys from uniform coins; the base message of a ring and a ring message; the
ring-aware base signer from the secret key, the ring, the signer's position, the message and uniform
coins (at most `q` queries; it may refuse); the ordinary base signer on base messages (at most `q`
queries); base verification at the oracle; and the public value of a base signature under a key (a
program with at most `qPub` queries). -/
structure BaseSigner (X Y : Type) (N : ℕ) (T : BaseTypes) where
  /-- Key generation from its coins. -/
  keyGen : T.KeyCoins → T.PK × T.SK
  /-- The base message of a ring and a ring message. -/
  bmsg : KeyRing T.PK N → T.Msg → T.BMsg
  /-- The bound on the signers' queries. -/
  q : ℕ
  /-- The ring-aware base signer at a position of the ring; `none` is a refusal. -/
  bsign : T.SK → KeyRing T.PK N → ℕ → T.Msg → T.Coins → OracleProg X Y (Option T.BSig)
  /-- It makes at most `q` queries. -/
  bsign_queries : ∀ sk R i m c, (bsign sk R i m c).QueriesLE q
  /-- The ordinary base signer on base messages. -/
  ssign : T.SK → T.BMsg → T.Coins → OracleProg X Y (Option T.BSig)
  /-- It makes at most `q` queries. -/
  ssign_queries : ∀ sk bm c, (ssign sk bm c).QueriesLE q
  /-- Base verification at an oracle. -/
  bverify : (X → Y) → T.PK → T.BMsg → T.BSig → Bool
  /-- The bound on the queries of the public value. -/
  qPub : ℕ
  /-- The public value of a base signature under a key. -/
  pub : T.PK → T.BSig → OracleProg X Y T.Pub
  /-- It makes at most `qPub` queries. -/
  pub_queries : ∀ pk σ, (pub pk σ).QueriesLE qPub

/-- **`List.idxOf` is the same at every lawful `BEq` instance**: the one from a decidable equality
(the one generic code over a types record uses) and the one a concrete key type has (a product's
componentwise `BEq`). -/
theorem idxOf_decEq_eq {α : Type*} {d : DecidableEq α} [i : BEq α] [LawfulBEq α] (a : α)
    (l : List α) : @List.idxOf α (@instBEqOfDecidableEq α d) a l = l.idxOf a := by
  obtain rfl := lawful_beq_subsingleton (@instBEqOfDecidableEq α d) i
  rfl

/-- **A key of a ring has a first position in it**, at the decidable equality of the types `T`.
`ofBase` locates the signer's key with this equality; stated over `T`, the lemma gives positions at
that equality also for a concrete `T` whose key type has another `BEq` instance (a product). -/
theorem BaseTypes.idxOf_lt_length_of_mem {T : BaseTypes} {N : ℕ} {R : KeyRing T.PK N} {x : T.PK}
    (h : x ∈ R.1) : R.1.idxOf x < R.1.length :=
  List.idxOf_lt_length_iff.2 h

/-- **The key at its first position**, at the decidable equality of the types `T`
(`BaseTypes.idxOf_lt_length_of_mem`). -/
theorem BaseTypes.getElem_idxOf {T : BaseTypes} {N : ℕ} {R : KeyRing T.PK N} {x : T.PK}
    (h : R.1.idxOf x < R.1.length) : R.1[R.1.idxOf x] = x :=
  List.getElem_idxOf h

namespace BaseSigner

variable {X Y : Type} {N : ℕ} {T : BaseTypes}

/-- Public keys: those of the types `T`. -/
abbrev PK (_ : BaseSigner X Y N T) : Type := T.PK

/-- Secret keys: those of the types `T`. -/
abbrev SK (_ : BaseSigner X Y N T) : Type := T.SK

/-- The coins of key generation: those of the types `T`. -/
abbrev KeyCoins (_ : BaseSigner X Y N T) : Type := T.KeyCoins

/-- Ring messages: those of the types `T`. -/
abbrev Msg (_ : BaseSigner X Y N T) : Type := T.Msg

/-- Base messages: those of the types `T`. -/
abbrev BMsg (_ : BaseSigner X Y N T) : Type := T.BMsg

/-- Base signatures: those of the types `T`. -/
abbrev BSig (_ : BaseSigner X Y N T) : Type := T.BSig

/-- Public values: those of the types `T`. -/
abbrev Pub (_ : BaseSigner X Y N T) : Type := T.Pub

/-- The coins of signing: those of the types `T`. -/
abbrev Coins (_ : BaseSigner X Y N T) : Type := T.Coins

end BaseSigner

variable {X Y : Type} {N : ℕ}

/-- **The ring relation's statement**, depending only on the base signer's key, message and
public-value types: a ring of at most `N` keys, a ring message and a public value. -/
structure RingStmtOf (PK Msg Pub : Type) (N : ℕ) where
  /-- The ring. -/
  ring : KeyRing PK N
  /-- The ring message. -/
  msg : Msg
  /-- The public value. -/
  pub : Pub
deriving DecidableEq

/-- **Ring statements as triples** of a ring, a ring message and a public value. -/
@[expose] def RingStmtOf.equivProd (PK Msg Pub : Type) (N : ℕ) :
    RingStmtOf PK Msg Pub N ≃ KeyRing PK N × Msg × Pub where
  toFun x := (x.ring, x.msg, x.pub)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The ring statements are finite** for finite keys, messages and public values. -/
noncomputable instance {PK Msg Pub : Type} [Fintype PK] [DecidableEq PK] [Fintype Msg] [Fintype Pub]
    {N : ℕ} : Fintype (RingStmtOf PK Msg Pub N) :=
  Fintype.ofEquiv _ (RingStmtOf.equivProd PK Msg Pub N).symm

/-- **The ring relation's witness**, depending only on the base signer's signature type: the
signer's position and a base signature. -/
structure RingWitOf (BSig : Type) where
  /-- The signer's position. -/
  idx : ℕ
  /-- The base signature. -/
  sig : BSig
deriving DecidableEq

/-- **A statement of the ring relation** of the base signer `B` (`RingStmtOf` at its key,
message and public-value types): a ring, a ring message and a public value. -/
abbrev RingStmt {T : BaseTypes} (_ : BaseSigner X Y N T) : Type := RingStmtOf T.PK T.Msg T.Pub N

/-- **A witness of the ring relation** of the base signer `B` (`RingWitOf` at its signature
type): the signer's position and a base signature. -/
abbrev RingWit {T : BaseTypes} (_ : BaseSigner X Y N T) : Type := RingWitOf T.BSig

/-- **The ring relation** `R_ring((R, m, y), (i, σ))` at the oracle `H` on the supported rings
`adm`: the ring is supported, `i` is a position of it, `σ` verifies on the base message
`bmsg R m` under the key at `i`, and its public value under that key is `y`. -/
structure RingRel {TB : BaseTypes} (B : BaseSigner X Y N TB) (adm : KeyRing B.PK N → Prop) (H : X → Y)
    (x : RingStmt B) (w : RingWit B) : Prop where
  /-- The ring is supported. -/
  supported : adm x.ring
  /-- The position is in the ring. -/
  idx_lt : w.idx < x.ring.1.length
  /-- The base signature verifies under the key at the position. -/
  verify_eq : B.bverify H (x.ring.1[w.idx]'idx_lt) (B.bmsg x.ring x.msg) w.sig = true
  /-- Its public value is the statement's. -/
  pub_eq : (B.pub (x.ring.1[w.idx]'idx_lt) w.sig).run H = x.pub

/-- **A decided test of the statements of the empty ring** at the statement map `stmt`: `isNil`
accepts the statement `stmt y` of a ring statement `y` exactly when the ring of `y` is empty. -/
class EmptyRingTest {TB : BaseTypes} {B : BaseSigner X Y N TB} {X₀ : Type} (stmt : RingStmt B → X₀) where
  /-- The test. -/
  isNil : X₀ → Bool
  /-- It accepts the statements of the empty ring, and only those among the statements. -/
  isNil_stmt_iff : ∀ y : RingStmt B, isNil (stmt y) = true ↔ y.ring.1 = []

/-- **The ring statements themselves have the emptiness of their ring as the test.** -/
instance EmptyRingTest.instId {TB : BaseTypes} {B : BaseSigner X Y N TB} : EmptyRingTest (B := B) id where
  isNil y := y.ring.1.isEmpty
  isNil_stmt_iff y := List.isEmpty_iff

/-- **The ring relation is decided** on decided supported rings: the support, the position, the
base verification and the public value are each decided. -/
instance RingRel.instDecidable {TB : BaseTypes} (B : BaseSigner X Y N TB) (adm : KeyRing B.PK N → Prop)
    [DecidablePred adm] (H : X → Y) (x : RingStmt B) (w : RingWit B) :
    Decidable (RingRel B adm H x w) :=
  decidable_of_iff (adm x.ring ∧ ∃ h : w.idx < x.ring.1.length,
      B.bverify H (x.ring.1[w.idx]'h) (B.bmsg x.ring x.msg) w.sig = true ∧
        (B.pub (x.ring.1[w.idx]'h) w.sig).run H = x.pub)
    ⟨fun ⟨ha, hi, hv, hp⟩ => ⟨ha, hi, hv, hp⟩,
      fun h => ⟨h.supported, h.idx_lt, h.verify_eq, h.pub_eq⟩⟩

/-- **The ring relation as a set** of statement-witness pairs. -/
@[expose] def ringRel {TB : BaseTypes} (B : BaseSigner X Y N TB) (adm : KeyRing B.PK N → Prop) (H : X → Y) :
    Set (RingStmt B × RingWit B) :=
  {p | RingRel B adm H p.1 p.2}

/-- **The ring relation on fewer supported rings is smaller.** -/
theorem ringRel_mono {TB : BaseTypes} (B : BaseSigner X Y N TB) {adm adm' : KeyRing B.PK N → Prop}
    (h : ∀ R, adm' R → adm R) (H : X → Y) : ringRel B adm' H ⊆ ringRel B adm H :=
  fun _ hp => ⟨h _ hp.supported, hp.idx_lt, hp.verify_eq, hp.pub_eq⟩

/-- **The types of a proof system**: proofs and the prover's coins, with the finiteness and
decidable equality the games read. A `ProofSystem` takes its types as this parameter. -/
structure PSTypes where
  /-- Proofs. -/
  Proof : Type
  /-- The prover's coins. -/
  Coins : Type
  [instFintypeProof : Fintype Proof]
  [instDecEqProof : DecidableEq Proof]
  [instFintypeCoins : Fintype Coins]
  [instDecEqCoins : DecidableEq Coins]
  [instNonemptyCoins : Nonempty Coins]

attribute [instance] PSTypes.instFintypeProof PSTypes.instDecEqProof PSTypes.instFintypeCoins
  PSTypes.instDecEqCoins PSTypes.instNonemptyCoins

/-- **A non-interactive proof system** with the random oracle `X → Y` and the types `T`: proofs,
uniform prover coins, the honest prover (a classical oracle program with at most `q` queries) and
the verifier at the oracle. The relation it is sound for is a property, not data. -/
structure ProofSystem (X Y Stmt Wit : Type) (T : PSTypes) where
  /-- The bound on the prover's queries. -/
  q : ℕ
  /-- The honest prover. -/
  prove : Stmt → Wit → T.Coins → OracleProg X Y T.Proof
  /-- It makes at most `q` queries. -/
  prove_queries : ∀ x w c, (prove x w c).QueriesLE q
  /-- The verifier at an oracle. -/
  verify : (X → Y) → Stmt → T.Proof → Bool

namespace ProofSystem

variable {Stmt Wit : Type} {T : PSTypes}

/-- Proofs: those of the types `T`. -/
abbrev Proof (_ : ProofSystem X Y Stmt Wit T) : Type := T.Proof

/-- The prover's coins: those of the types `T`. -/
abbrev Coins (_ : ProofSystem X Y Stmt Wit T) : Type := T.Coins

/-- **The honest prover as a `NARG.Prover`**, its coins uniform. -/
@[expose] noncomputable def prover (PS : ProofSystem X Y Stmt Wit T) :
    NARG.Prover X Y Stmt Wit PS.Proof PS.Coins where
  prog := PS.prove
  coins := PMF.uniformOfFintype _
  q := PS.q
  prog_queries := PS.prove_queries

/-- The program of `prover` is the honest prover. -/
theorem prover_prog (PS : ProofSystem X Y Stmt Wit T) : PS.prover.prog = PS.prove :=
  rfl

/-- The coins of `prover` are uniform. -/
theorem prover_coins (PS : ProofSystem X Y Stmt Wit T) :
    PS.prover.coins = PMF.uniformOfFintype PS.Coins :=
  rfl

/-- The query bound of `prover` is `q`. -/
theorem prover_q (PS : ProofSystem X Y Stmt Wit T) : PS.prover.q = PS.q :=
  rfl

/-- **The proof system of a `NARG.Prover`** and a verifier. Its coins are uniform, so it is the
prover's when the prover's coins are uniform (`prover_ofProver`). -/
@[expose] def ofProver {Proof Coins : Type} [Fintype Proof] [DecidableEq Proof] [Fintype Coins]
    [DecidableEq Coins] [Nonempty Coins] (P : NARG.Prover X Y Stmt Wit Proof Coins)
    (verify : (X → Y) → Stmt → Proof → Bool) : ProofSystem X Y Stmt Wit ⟨Proof, Coins⟩ where
  q := P.q
  prove := P.prog
  prove_queries := P.prog_queries
  verify := verify

section ofProver

variable {Proof Coins : Type} [Fintype Proof] [DecidableEq Proof] [Fintype Coins]
  [DecidableEq Coins] [Nonempty Coins] (P : NARG.Prover X Y Stmt Wit Proof Coins)
  (verify : (X → Y) → Stmt → Proof → Bool)

/-- The query bound of `ofProver` is the prover's. -/
theorem ofProver_q : (ofProver P verify).q = P.q :=
  rfl

/-- The honest prover of `ofProver` is the prover's program. -/
theorem ofProver_prove : (ofProver P verify).prove = P.prog :=
  rfl

/-- The verifier of `ofProver` is `verify`. -/
theorem ofProver_verify : (ofProver P verify).verify = verify :=
  rfl

end ofProver

/-- **A prover with uniform coins is the prover of its proof system.** -/
theorem prover_ofProver {Proof Coins : Type} [Fintype Proof] [DecidableEq Proof] [Fintype Coins]
    [DecidableEq Coins] [Nonempty Coins] (P : NARG.Prover X Y Stmt Wit Proof Coins)
    (verify : (X → Y) → Stmt → Proof → Bool) (hP : P.coins = PMF.uniformOfFintype Coins) :
    (ofProver P verify).prover = P := by
  cases P
  simp only [ofProver, prover] at hP ⊢
  rw [hP]

end ProofSystem

/-! ### The ring scheme -/

/-- **The types of the ring scheme from a base signer and a proof system** (`ofBase`): the keys,
key-generation coins and messages of the base signer's types `TB`; signatures, a public value and
a proof of `TP`; signing coins, the base signer's and the prover's. -/
abbrev ofBaseT (TB : BaseTypes) (TP : PSTypes) : RingTypes where
  PK := TB.PK
  SK := TB.SK
  Msg := TB.Msg
  Sig := TB.Pub × TP.Proof
  KeyCoins := TB.KeyCoins
  SignCoins := TB.Coins × TP.Coins
  instDecEqSig := instDecidableEqProd
  instDecEqSignCoins := instDecidableEqProd

variable {TB : BaseTypes} {TP : PSTypes} (B : BaseSigner X Y N TB)
  (PS : ProofSystem X Y (RingStmt B) (RingWit B) TP)

/-- **Signing at a position**: the base signature `σ` of the secret key `sk` at position `i` of
`R` on `m` (refusing if `bsign` refuses), its public value `y` under `pk`, and the proof of `(R, m, y)`
with the witness `(i, σ)`; the ring signature is `(y, π)`. -/
@[expose] def signAt (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : B.Coins × PS.Coins) : OracleProg X Y (Option (B.Pub × PS.Proof)) :=
  (B.bsign sk R i m c.1).bind fun
    | none => .pure none
    | some σ => (B.pub pk σ).bind fun y =>
        (PS.prove ⟨R, m, y⟩ ⟨i, σ⟩ c.2).mapOutput fun π => some (y, π)

/-- Signing at a position makes at most `q + (qPub + PS.q)` queries. -/
theorem signAt_queries (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : B.Coins × PS.Coins) : (signAt B PS pk sk R i m c).QueriesLE (B.q + (B.qPub + PS.q)) := by
  refine (B.bsign_queries sk R i m c.1).bind fun o => ?_
  rcases o with _ | σ
  · exact OracleProg.QueriesLE.pure _ _
  · exact (B.pub_queries pk σ).bind fun y => (PS.prove_queries _ _ c.2).mapOutput _

/-- `signAt`, unfolded. -/
theorem signAt_eq (pk : B.PK) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : B.Coins × PS.Coins) :
    signAt B PS pk sk R i m c = (B.bsign sk R i m c.1).bind fun
      | none => .pure none
      | some σ => (B.pub pk σ).bind fun y =>
          (PS.prove ⟨R, m, y⟩ ⟨i, σ⟩ c.2).mapOutput fun π => some (y, π) :=
  rfl

/-- **The ring signature from a base signer and a proof system** on the supported rings `adm`:
public keys, secret keys, key generation and ring messages of the base signer; signatures
`(y, π)`; signing coins those of the base signer and of the prover. Signing by the key pair
`(pk, sk)` finds the first position `i` of `pk` in the ring, refuses (`none`) when `pk` is not in
the ring or the ring is not supported, and otherwise is `signAt` at `i`. Verification is `PS`'s
verifier on `(R, m, y)`. -/
@[expose] def ofBase (adm : KeyRing B.PK N → Prop) [DecidablePred adm] :
    RingScheme X Y N (ofBaseT TB TP) where
  keyGen := B.keyGen
  q := B.q + (B.qPub + PS.q)
  sign kp R m c :=
    if R.1.idxOf kp.1 < R.1.length ∧ adm R then signAt B PS kp.1 kp.2 R (R.1.idxOf kp.1) m c
    else .pure none
  sign_queries kp R m c := by
    split_ifs
    · exact signAt_queries B PS _ _ _ _ _ _
    · exact OracleProg.QueriesLE.pure _ _
  verify H R m s := PS.verify H ⟨R, m, s.1⟩ s.2
  Supported := adm

variable (adm : KeyRing B.PK N → Prop) [DecidablePred adm]

/-- Key generation of `ofBase` is the base signer's. -/
theorem ofBase_keyGen : (ofBase B PS adm).keyGen = B.keyGen :=
  rfl

/-- The query bound of `ofBase`. -/
theorem ofBase_q : (ofBase B PS adm).q = B.q + (B.qPub + PS.q) :=
  rfl

/-- **Signing of `ofBase`**: `signAt` at the first position of the key on a supported ring
holding it, refusal otherwise. -/
theorem ofBase_sign (kp : B.PK × B.SK) (R : KeyRing B.PK N) (m : B.Msg) (c : B.Coins × PS.Coins) :
    (ofBase B PS adm).sign kp R m c =
      if R.1.idxOf kp.1 < R.1.length ∧ adm R then signAt B PS kp.1 kp.2 R (R.1.idxOf kp.1) m c
      else .pure none :=
  rfl

/-- The supported rings of `ofBase` are `adm`. -/
theorem ofBase_supported : (ofBase B PS adm).Supported = adm :=
  rfl

/-- Verification of `ofBase` is the proof system's verifier on `(R, m, y)`. -/
theorem verify_ofBase (H : X → Y) (R : KeyRing B.PK N) (m : B.Msg) (s : B.Pub × PS.Proof) :
    (ofBase B PS adm).verify H R m s = PS.verify H ⟨R, m, s.1⟩ s.2 :=
  rfl

/-- **The signer of `ofBase` refuses outside its rings.** -/
theorem ofBase_refusesOutside : (ofBase B PS adm).RefusesOutside := by
  refine (RingScheme.refusesOutside_iff _).2 fun kp R m c H h => ?_
  simp only [ofBase]
  split_ifs with hc
  · rcases h with h | h
    · exact absurd (List.idxOf_lt_length_iff.1 hc.1) h
    · exact absurd hc.2 h
  · rfl

/-- **On a supported ring holding its key, the signer of `ofBase` signs at the key's first
position.** -/
theorem sign_ofBase_of_mem {kp : B.PK × B.SK} {R : KeyRing B.PK N} (hR : kp.1 ∈ R.1) (ha : adm R)
    (m : B.Msg) (c : B.Coins × PS.Coins) :
    (ofBase B PS adm).sign kp R m c = signAt B PS kp.1 kp.2 R (R.1.idxOf kp.1) m c := by
  simp only [ofBase]
  split_ifs with hc
  · rfl
  · exact absurd ⟨List.idxOf_lt_length_iff.2 hR, ha⟩ hc

/-- **An honest ring signature is the public value and the proof of the base signature**: when
`bsign` outputs `σ` at the oracle `H`, signing at the position outputs `(y, π)` with `y` the public
value of `σ` under `pk` and `π` the prover's proof of `(R, m, y)` with the witness `(i, σ)`. -/
theorem run_signAt_of_bsign {H : X → Y} {pk : B.PK} {sk : B.SK} {R : KeyRing B.PK N} {i : ℕ}
    {m : B.Msg} {c : B.Coins × PS.Coins} {σ : B.BSig} (hσ : (B.bsign sk R i m c.1).run H = some σ) :
    (signAt B PS pk sk R i m c).run H =
      some ((B.pub pk σ).run H,
        (PS.prove ⟨R, m, (B.pub pk σ).run H⟩ ⟨i, σ⟩ c.2).run H) := by
  simp only [signAt, OracleProg.run_bind, hσ, OracleProg.run_mapOutput]

omit [DecidablePred adm] in
/-- **The relation holds on honest signatures**: a base signature `σ` of the key at position `i` of
a supported ring that verifies on `bmsg R m` is a witness, with `i`, of the statement `(R, m, y)`
whose public value `y` is that of `σ`. The relation is satisfiable whenever the base signer outputs a
verifying signature. -/
theorem ringRel_of_bsign {H : X → Y} {R : KeyRing B.PK N} {i : ℕ} (hi : i < R.1.length)
    {m : B.Msg} {σ : B.BSig} (ha : adm R)
    (hv : B.bverify H (R.1[i]'hi) (B.bmsg R m) σ = true) :
    (⟨R, m, (B.pub (R.1[i]'hi) σ).run H⟩, ⟨i, σ⟩) ∈ ringRel B adm H :=
  ⟨ha, hi, hv, rfl⟩

end GordieHowe.RingSignature
