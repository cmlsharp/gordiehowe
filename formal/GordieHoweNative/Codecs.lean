-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Terms
public meta import GordieHoweNative.Derive

@[expose] public section

/-!
# GordieHowe: the decoders of the certificate types, and the section types

Every type of `Data.lean` gets its `.ghc` decoder by derivation (`Derive.lean`); `IndexMap`'s is the
override of `Ghc.lean`. `sectionTypes` lists the types a section may have, which `load_ghc` reads.
A new kind of certificate data adds its types to this library, derives their decoders here and
lists its section types.
-/

namespace GordieHowe.Ghc

open GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Certificate GordieHowe.GKR.Fold

deriving instance Decode for Coef
deriving instance Decode for ConvForm
deriving instance Decode for NttOrder
deriving instance Decode for NamedOp
deriving instance Decode for Wire
deriving instance Decode for Place
deriving instance Decode for NTree
deriving instance Decode for GKR.Certificate.Table
deriving instance Decode for Layered
deriving instance Decode for Cert
deriving instance Decode for BinOp
deriving instance Decode for CmpOp
deriving instance Decode for CmpArg
deriving instance Decode for EOp
deriving instance Decode for ETerm
deriving instance Decode for ENode
deriving instance Decode for ENodeInfo
deriving instance Decode for Trie
deriving instance Decode for ETable
deriving instance Decode for Assert
deriving instance Decode for Dag
deriving instance Decode for Frac
deriving instance Decode for FracTree
deriving instance Decode for LogupCert
deriving instance Decode for MacHCert
deriving instance Decode for FamCert
deriving instance Decode for EntryCert
deriving instance Decode for Consts
deriving instance Decode for CircuitData

/-- **The types a section may have**: a GKR circuit's certificate (`CircuitData`) and its parts. -/
def sectionTypes : Array Entry := #[
  .of Nat, .of (List Nat), .of Consts, .of NTree, .of Dag, .of GKR.Certificate.Table, .of Layered,
  .of Cert, .of (Trie ENodeInfo), .of ETable, .of (List EntryCert), .of CircuitData]

end GordieHowe.Ghc
