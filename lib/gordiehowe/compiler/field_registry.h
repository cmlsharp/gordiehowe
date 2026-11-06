// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the Lean objects a generated proof system names, by the
// plan's descriptors.
//
// The proof modules of an export (plan_proofs.h) build the program's proof
// system from Lean objects the library proves once:
//   fields     by the field descriptor's name (the plan's FieldSpec): the
//              Lean field interpretation, its model with its prime and bit
//              nodes, its packing facts, the homomorphism of its GKR code
//              arithmetic (emit_export.h's field_arith), and, where the
//              library has them, its MAC field facts and its linear
//              integer reading;
//   tableaus   by the plan's Ligero numbers (rate, t, block_enc, the
//              low-degree repetitions, the mask test): the Ligero
//              certificates the library proves, which the configurations'
//              round-error proofs read by name;
//   frontends  by the configuration: the interpretation's opaque functions
//              and the lemmas about them (the Falcon frontend's falconOps,
//              the ML-DSA frontend's targetBitsFn).
// Nothing here is trusted. Lean checks every choice: the interpretation's
// names and characteristics against the program's fields
// (Interp.SpecsMatch, in the model), the packing and the tableau against
// the plan (fieldOkB), the code arithmetic against the field (the
// certificates' CircuitFieldOk), and the opaque functions' facts (the
// model's opaque and MAC parts). A wrong entry fails to compile.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_FIELD_REGISTRY_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_FIELD_REGISTRY_H_

#include <cstddef>
#include <string>
#include <utility>

namespace proofs::gordiehowe::compiler {

// A field's Lean objects. MAC_OK and READ_LINEAR are empty where the
// library has no such fact; MODULE defines the field's interpretation,
// model and code homomorphism; the packings are FieldPackings'.
// EDGES lists the packing edges the field's packing facts realize, each
// `m:d:mode` (child degree, relative degree, `s` squaring-chain or `m`
// subfield masks; Lean `FieldInterp.Packing.edge`). BYTES, CODEC and READER
// are the transcript's: an element's bytes on the wire, its Lean byte codec
// (`SPBCS.Codec.FieldBytes`) and its challenge reader (`SPBCS.CReader`);
// CODEC is null where the library has none.
struct FieldModelEntry {
  const char *name, *title, *interp, *model, *packing, *code_hom, *mac_ok,
      *read_linear, *module, *edges;
  size_t bytes = 0;
  const char *codec = nullptr, *reader = nullptr;
  // Degree of the subfield in which the packing kit's masks lie.
  size_t mask_field_degree = 1;
};

// The module defining every field's packing facts.
inline constexpr char kFieldPackingsModule[] =
    "GordieHowe.ProofSystem.Program.FieldPackings";

// The entry of the field named NAME, or null when the library has no model
// of it.
inline const FieldModelEntry *field_model(const std::string &name) {
  static const FieldModelEntry entries[] = {
      {"GF(2^128)", "`GF(2^128)`", "RealizedProgram.gf128", "RealizedProgram.gf128_model",
       "RealizedProgram.gf128Packing", "RealizedProgram.gf128_codeHom",
       "RealizedProgram.gf128_macFieldOk", "", "GordieHowe.Applications.FieldInterps.Basic",
       "1:16:s 16:4:m 64:2:m 16:8:m 16:2:m 32:4:m", 16, "SPBCS.Codec.FieldBytes.gf2_128",
       "SPBCS.CReader.gf2_128", 16},
      {"GF(2^256)", "`GF(2^256)`", "RealizedProgram.gf256", "RealizedProgram.gf256_model",
       "RealizedProgram.gf256Packing", "RealizedProgram.gf256_codeHom",
       "RealizedProgram.gf256_macFieldOk", "", "GordieHowe.Applications.FieldInterps.GF256",
       "1:16:s 16:4:m 64:4:m", 32, "SPBCS.Codec.FieldBytes.gf2_256",
       "SPBCS.CReader.gf2_256", 16},
      {"F_q^9", "`F_q^9`", "RealizedProgram.fq9", "RealizedProgram.fq9_model",
       "RealizedProgram.fq9Packing",
       "(RealizedProgram.fq9_codeHom.withPrime RealizedProgram.fq9Code_primeOn)", "",
       "RealizedProgram.fq9_readLinear", "GordieHowe.Applications.FieldInterps.Basic", "1:9:m", 18,
       "SPBCS.Codec.FieldBytes.falconNative", "SPBCS.CReader.falconNative"},
      {"F_q^20", "`F_q^20`", "RealizedProgram.fq20", "RealizedProgram.fq20_model",
       "RealizedProgram.fq20Packing",
       "(RealizedProgram.fq20_codeHom.withPrime RealizedProgram.fq20Code_primeOn)", "",
       "RealizedProgram.fq20_readLinear", "GordieHowe.Applications.FieldInterps.Fq20",
       "1:4:m 4:5:m", 35, "SPBCS.Codec.FieldBytes.falconNative20",
       "SPBCS.CReader.falconNative20"},
      {"F_q^6", "`F_q^6`", "RealizedProgram.fq6", "RealizedProgram.fq6_model",
       "RealizedProgram.fq6Packing",
       "(RealizedProgram.fq6_codeHom.withPrime RealizedProgram.fq6Code_primeOn)", "", "",
       "GordieHowe.Applications.FieldInterps.Odd", "1:6:m", 18,
       "SPBCS.Codec.FieldBytes.mldsaNative", "SPBCS.CReader.mldsaNative"},
      {"F_q^11", "`F_q^11`", "RealizedProgram.fq11", "RealizedProgram.fq11_model",
       "RealizedProgram.fq11Packing",
       "(RealizedProgram.fq11_codeHom.withPrime RealizedProgram.fq11Code_primeOn)", "", "",
       "GordieHowe.Applications.FieldInterps.Odd", "1:11:m", 32,
       "SPBCS.Codec.FieldBytes.mldsaNative11", "SPBCS.CReader.mldsaNative11"},
      {"Goldilocks^2", "Goldilocks²", "RealizedProgram.gold2", "RealizedProgram.gold2_model",
       "RealizedProgram.gold2Packing",
       "(RealizedProgram.gold2_codeHom.withPrime RealizedProgram.gold2Code_primeOn)", "", "",
       "GordieHowe.Applications.FieldInterps.Odd", "1:2:m", 16,
       "SPBCS.Codec.FieldBytes.goldilocksExt2", "SPBCS.CReader.goldilocksExt2"},
      {"Goldilocks^4", "Goldilocks⁴", "RealizedProgram.gold4", "RealizedProgram.gold4_model",
       "RealizedProgram.gold4Packing",
       "(RealizedProgram.gold4_codeHom.withPrime RealizedProgram.gold4Code_primeOn)", "", "",
       "GordieHowe.Applications.FieldInterps.Odd", "1:4:m", 32,
       "SPBCS.Codec.FieldBytes.goldilocksExt4", "SPBCS.CReader.goldilocksExt4"},
      {"F_p256", "`F_p256`", "RealizedProgram.p256", "RealizedProgram.p256_model",
       "RealizedProgram.p256Packing",
       "(RealizedProgram.p256_codeHom.withPrime RealizedProgram.p256Code_primeOn)", "", "",
       "GordieHowe.Applications.FieldInterps.P256", "", 32, nullptr, nullptr},
  };
  for (const FieldModelEntry &e : entries)
    if (name == e.name) return &e;
  return nullptr;
}

// Whether the field's packing facts realize the edge EDGE (`m:d:mode`).
inline bool field_has_edge(const FieldModelEntry &e, const std::string &edge) {
  const std::string all = std::string(" ") + e.edges + " ";
  return all.find(" " + edge + " ") != std::string::npos;
}

// The kit's prefix and own mask-cell counts at a queried edge. Unsupported
// edges have no kit and answer zero, matching Packing.desc. Subfield masks
// use relative_degree * [field:mask_subfield] prefix cells; a bit-chain kit
// has relative_degree + relative_degree*(relative_degree-1)/2 own cells.
inline std::pair<size_t, size_t> field_mask_nums(const FieldModelEntry &e,
                                               size_t field_degree,
                                               const std::string &edge) {
  if (!field_has_edge(e, edge)) return {0, 0};
  const size_t a = edge.find(':'), b = edge.find(':', a + 1);
  const size_t d = std::stoull(edge.substr(a + 1, b - a - 1));
  if (edge.substr(b + 1) == "s") return {0, d + d * (d - 1) / 2};
  return {d * (field_degree / e.mask_field_degree), 0};
}

// A Ligero certificate the library proves, by its Ligero numbers (the mask
// test; untested masks have none here): its Lean name and module.
struct KnownTableau {
  size_t rate, t, block_enc, reps;
  const char *name, *module;
};

// The library's certificate of the tableau (RATE, T, BLOCK_ENC, REPS) with
// the mask test, or null.
inline const KnownTableau *known_tableau(size_t rate, size_t t, size_t block_enc,
                                         size_t reps) {
  static const char kRing[] = "GordieHowe.Applications.MLDSA44.Ring.Tableaux";
  static const KnownTableau entries[] = {
      {12, 128, 4746, 2, "RealizedProgram.gf256K339R2Cert", kFieldPackingsModule},
      {6, 201, 4095, 1, "RealizedProgram.gold4K512Cert", kFieldPackingsModule},
      {6, 175, 4095, 2, "RealizedProgram.gold4K512R2Cert", kFieldPackingsModule},
      {12, 63, 4203, 2, "RealizedProgram.gf128K300R2Cert", kFieldPackingsModule},
      {12, 63, 3955, 2, "RealizedProgram.gf128K282R2Cert", kFieldPackingsModule},
      {5, 96, 3583, 2, "RealizedProgram.gold2K512R2Cert", kFieldPackingsModule},
      {12, 127, 3799, 1, "RealizedProgram.fq20K271Cert", kFieldPackingsModule},
      {5, 90, 2369, 2, "RealizedProgram.falconNativeROMACert", kFieldPackingsModule},
      {5, 89, 2105, 2, "RealizedProgram.falconRingNativeROMACert", kFieldPackingsModule},
      {6, 214, 8191, 1, "RealizedProgram.gold4K1024Cert", kRing},
      {12, 63, 3722, 2, "RealizedProgram.gf128K265R2Cert", kRing},
  };
  for (const KnownTableau &e : entries)
    if (e.rate == rate && e.t == t && e.block_enc == block_enc && e.reps == reps) return &e;
  return nullptr;
}

// The frontend whose opaque functions a configuration's interpretation
// reads: the Falcon frontend's (falconOps, `key.coefficients` and
// `mac.target_bits`), the ML-DSA frontend's (targetBitsFn, the
// interpretations mldsaInterp/mldsaQROMInterp), or none (targetBitsFn at a
// two-field interpretation of its own), or the ECDSA mDL's (mdocOps:
// `device.e2_point`, `issuer.q_table` and `mac.target_bits`, at a
// two-field interpretation).
enum class Frontend { kFalcon, kMLDSA, kMdoc, kNone };

inline Frontend frontend_of(const std::string &config) {
  if (config.rfind("falcon", 0) == 0) return Frontend::kFalcon;
  if (config.rfind("mldsa", 0) == 0) return Frontend::kMLDSA;
  if (config.rfind("mdoc", 0) == 0) return Frontend::kMdoc;
  return Frontend::kNone;
}

// The module defining a frontend's interpretation builder and its lemmas.
// The opaque-function set of a program's interpretation (the plan's
// `opaqueSet`, Lean `GordieHowe.OpaqueKey`): `none` when no opaque value
// reads an argument (OPAQUE_ARGS false), the mDL frontend's `mdoc`, the
// Falcon frontend's `falcon` at two fields, and `targetBits` otherwise.
inline const char *opaque_set(bool opaque_args, Frontend f, size_t fields) {
  if (!opaque_args) return "none";
  if (f == Frontend::kMdoc) return "mdoc";
  if (f == Frontend::kFalcon && fields == 2) return "falcon";
  return "targetBits";
}

// The Lean function of an opaque-function set (opaque_set).
inline std::string opaque_fn(const std::string &set) {
  if (set == "none") return "fun _ _ _ => 0";
  if (set == "mdoc") return "RealizedProgram.mdocOps";
  if (set == "falcon") return "RealizedProgram.falconOps";
  return "RealizedProgram.targetBitsFn";
}

// The Lean key of a field entry (`GordieHowe.FieldKey`): its interpretation's
// name in RealizedProgram (`RealizedProgram.gf128` is `.gf128`).
inline std::string field_key(const FieldModelEntry &e) {
  const std::string s = e.interp;
  return s.substr(s.rfind('.') + 1);
}

// The Lean key of a library tableau (`GordieHowe.TableauKey`): its
// certificate's name without `Cert` (`RealizedProgram.gf128K282R2Cert` is
// `.gf128K282R2`).
inline std::string tableau_key(const KnownTableau &t) {
  std::string s = t.name;
  s = s.substr(s.rfind('.') + 1);
  return s.substr(0, s.size() - 4);
}

inline const char *frontend_module(Frontend f) {
  switch (f) {
    case Frontend::kFalcon:
      return "GordieHowe.Applications.Falcon512.Frontend.Fields";
    case Frontend::kMLDSA:
      return "GordieHowe.Applications.MLDSA44.Interp";
    case Frontend::kMdoc:
      return "GordieHowe.Applications.MDL.Frontend";
    case Frontend::kNone:
      break;
  }
  return "GordieHowe.Applications.FieldInterps.Basic";
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_FIELD_REGISTRY_H_
