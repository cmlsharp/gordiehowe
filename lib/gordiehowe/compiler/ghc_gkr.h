// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// A GKR circuit's certificate as a `.ghc` file (ghc.h): the Lean types of
// formal/GordieHoweNative/Data.lean as a schema, and the sections of
// `name : CircuitData` (formal/GordieHowe/Language/Realizations/Circuit/
// Load.lean), the large values split into sections of their own.
//
// The sections, in order: name.consts (the constant table, packed);
// name.dagPart<p> and name.dag (the DAG's nodes, their term lists packed,
// in a trie split at depth log2(nodes / 2048)); per layer namelayer<d> (the
// gates, packed) and namewtab<d> (the wires' DAG nodes, packed);
// name.layered, name.width, name.sched; name.nodes<p> and name.table (the
// node table, a trie split at depth log2(nodes / 512)); name.entries; and
// name. The composite sections are in spine form, referring to the parts.
// Sections the GKR source reads (consts, layers, layered, width) get
// compiled code; native mode reads name and every layer and wire table at
// run time (the constants the checks name).
//
// The packing and the tries are Lean's representation of the data
// (GordieHowe.GKR.Certificate.Table.packed, NTree, RealizedProgram.Trie):
// the writer builds them, so Lean's decoder only reads values by type.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_GKR_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_GKR_H_

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "gordiehowe/compiler/ghc.h"

namespace proofs::gordiehowe::ghc {

// The Lean types of a GKR circuit's certificate (Data.lean), in its order,
// each structure's fields named as in Lean (their text, Schema::dump, is
// formal/scripts/ghc_schema.txt, which formal/scripts/check.sh compares with
// the Lean types' and gordiehowe_ghc_test with this schema's).
inline const Schema &gkr_schema() {
  static const Schema s = [] {
    Schema s;
    const std::string rp = "GordieHowe.RealizedProgram.", rel = "GordieHowe.GKR.Rel.",
                      cert = "GordieHowe.GKR.Certificate.", fold = "GordieHowe.GKR.Fold.";
    const std::string N = "Nat";
    s.inductive(rp + "Coef", 0, {{"const", {N}}, {"node", {N, N}}});
    s.inductive(rp + "ConvForm", 0, {{"coefficients", {}}, {"ntt", {N}}, {"nttNatural", {N}}});
    s.inductive(rp + "NttOrder", 0, {{"scheme", {}}, {"natural", {}}});
    const std::string cf = rp + "ConvForm";
    s.inductive(rp + "NamedOp", 0,
                {{"negacyclicConv", {N, cf}},
                 {"polyMatVec", {N, N, N, cf}},
                 {"polyBroadcast", {N, N, cf}},
                 {"ntt", {N, N, rp + "NttOrder"}},
                 {"inverseNtt", {N, N}},
                 {"nttTranspose", {N, N}},
                 {"rowDot", {N, N, N}},
                 {"macConv", {N, N, N, "List Nat"}},
                 {"acyclicConv", {N, N}},
                 {"diagonal", {N}},
                 {"scale", {N}},
                 {"constDiagonal", {N}},
                 {"sum", {N}},
                 {"fromDigits", {N, N}},
                 {"batched", {N, rp + "NamedOp"}}});
    s.structure(rel + "Wire", 0, {"c0 : Nat", "c1 : Nat", "n : Nat"});
    s.inductive(rel + "Place", 0, {{"block", {N}}, {"late", {N, N}}, {"defined", {N}}});
    s.inductive(cert + "NTree", 0,
                {{"nil", {}}, {"leaf", {N}}, {"node", {cert + "NTree", cert + "NTree"}}});
    s.inductive(cert + "Table", 0, {{"ident", {}}, {"packed", {N, cert + "NTree"}}});
    s.structure(cert + "Layered", 0, {"inputs : Nat", "layers : List (List Nat)"});
    s.structure(cert + "Cert", 0,
                {"width : Nat", "tables : List " + cert + "Table", "outputs : List (Prod Nat Nat)",
                 "outWires : List Nat"});
    s.inductive(rp + "BinOp", 0, {{"add", {}}, {"mul", {}}, {"and", {}}, {"or", {}}, {"xor", {}}});
    s.inductive(rp + "CmpOp", 0, {{"lt", {}}, {"leq", {}}, {"eq", {}}});
    const std::string im = "GordieHowe.RealizedProgram.IndexMap";
    s.inductive(rp + "CmpArg", 0, {{"node", {N}}, {"imm", {N, im}}});
    s.inductive(rp + "EOp", 0,
                {{"view", {im, "Option Nat"}},
                 {"named", {rp + "NamedOp"}},
                 {"sparse", {"List (List (Prod Nat " + rp + "Coef))"}},
                 {"staged", {rp + "NamedOp", N}}});
    s.structure(rp + "ETerm", 0, {"scale : Nat", "view : Nat", "ops : List " + rp + "EOp"});
    s.inductive(rp + "ENode", 0,
                {{"lin", {"List " + rp + "ETerm", N}},
                 {"const", {N}},
                 {"bin", {rp + "BinOp", N, N}},
                 {"scale", {N, N}},
                 {"sum", {N, N}},
                 {"prod", {N, N}},
                 {"broadcast", {im, N}},
                 {"lnot", {N, N}},
                 {"mux", {"Bool", N, N, N}},
                 {"cmp", {rp + "CmpOp", N, N, rp + "CmpArg"}},
                 {"tree", {"Bool", N, N}},
                 {"materialize", {N}},
                 {"gather", {im, "List Nat"}},
                 {"apply", {rp + "EOp", N}},
                 {"value", {N, rel + "Place"}}});
    s.structure(rp + "ENodeInfo", 0,
                {"node : " + rp + "ENode", "len : Nat", "cut : Bool", "ref : Option Nat",
                 "wires : List " + rel + "Wire", "aux : List " + rel + "Wire"});
    s.inductive(rp + "Trie", 1,
                {{"nil", {}}, {"leaf", {"#0"}}, {"node", {rp + "Trie #0", rp + "Trie #0"}}});
    s.structure(rp + "ETable", 0, {"size : Nat", "tree : " + rp + "Trie " + rp + "ENodeInfo"});
    s.structure(rel + "Assert", 0, {"Z : Nat", "U : Nat"});
    s.structure(cert + "Dag", 0,
                {"tree : " + cert + "NTree", "inputs : Nat", "size : Nat", "asserts : List Nat",
                 "outputs : List Nat"});
    s.structure(rel + "Frac", 0,
                {"l : Nat", "r : Nat", "num : " + rel + "Wire", "den : " + rel + "Wire"});
    s.structure(rel + "FracTree", 0,
                {"dens : List " + rel + "Wire", "inner : List " + rel + "Frac"});
    s.structure(rel + "LogupCert", 0,
                {"alpha : Nat", "needles : List Nat", "hists : List Nat", "weights : Nat",
                 "tree : " + rel + "FracTree", "sum : " + rel + "Wire"});
    s.structure(rel + "MacHCert", 0,
                {"bits : Nat", "powers : Nat", "tag : Nat", "chunks : List " + rel + "Wire"});
    s.inductive(rel + "FamCert", 0,
                {{"alignment", {N}}, {"logup", {rel + "LogupCert"}}, {"macH", {rel + "MacHCert"}}});
    s.structure(rel + "EntryCert", 0,
                {"entry : Nat", "lo : Nat", "hi : Nat", "root : Option Nat",
                 "asserts : List " + rel + "Assert", "fam : Option " + rel + "FamCert"});
    s.structure(fold + "Consts", 0, {"width : Nat", "table : " + cert + "Table"});
    s.structure(rp + "CircuitData", 0,
                {"c : Nat", "w : Nat", "chr : Nat", "prime : Nat", "char2 : Bool", "neg1 : Nat",
                 "half : Nat", "consts : " + fold + "Consts", "dag : " + cert + "Dag",
                 "layered : " + cert + "Layered", "sched : " + cert + "Cert",
                 "table : " + rp + "ETable", "entries : List " + rel + "EntryCert"});
    return s;
  }();
  return s;
}

// --------------------------------------------------------------- tries --

// An LSB-first binary trie of keyed leaves, in Lean's form (Load.lean's
// splitting, Data.lean's NTree and Trie: nil 0, leaf 1, node 2): no entry a
// nil, one entry a leaf, else the even keys left and the odd keys right,
// each key halved. ITEMS are (key, the leaf value's plain bytes), keys
// distinct.
class TrieWriter {
 public:
  using Items = std::vector<std::pair<uint64_t, const Bytes *>>;

  // The trie's plain encoding.
  static void plain(Bytes &o, const Items &items) {
    if (items.empty()) return o.ctor(0);
    if (items.size() == 1) {
      o.ctor(1);
      return o.bytes(*items[0].second);
    }
    o.ctor(2);
    const auto [l, r] = halves(items);
    plain(o, l);
    plain(o, r);
  }

  // The trie in spine form, each subtree of more than one entry at depth
  // SPLIT the section BASE<path> of type TY (path: the subtree's keys' low
  // bits), added to F before the spine is used.
  static void split(File &f, Bytes &o, const Items &items, const std::string &base, const Ty &ty,
                    uint64_t at, size_t depth = 0, uint64_t path = 0) {
    if (items.size() <= 1) {
      o.plain();
      return plain(o, items);
    }
    if (depth == at) {
      Bytes part;
      plain(part, items);
      return o.ref(f.section(base + std::to_string(path), ty, 0, part));
    }
    o.inline_();
    o.ctor(2);
    const auto [l, r] = halves(items);
    split(f, o, l, base, ty, at, depth + 1, path);
    split(f, o, r, base, ty, at, depth + 1, path + (uint64_t(1) << depth));
  }

 private:
  static std::pair<Items, Items> halves(const Items &items) {
    Items l, r;
    for (const auto &[k, v] : items) (k % 2 == 0 ? l : r).emplace_back(k / 2, v);
    return {std::move(l), std::move(r)};
  }
};

// Lean's Nat.log2 (0 for 0).
inline uint64_t log2_floor(uint64_t x) {
  uint64_t n = 0;
  while (x >>= 1) ++n;
  return n;
}

// --------------------------------------------------------- certificate --

// A GKR circuit's certificate, field-free: field elements as the
// little-endian bytes of their codes.
struct GkrCore {
  using Code = std::vector<uint8_t>;
  using Terms = std::vector<std::array<uint64_t, 3>>;  // (constant, op0, op1)
  // The circuit's index, the term width, the field's characteristic, the
  // fast path's prime (empty: none), the characteristic-two flag, the codes
  // of -1 and 1/2 (zero in characteristic two).
  uint64_t c = 0, w = 0;
  Code chr, prime;
  bool char2 = false;
  Code neg1, half;
  uint64_t ninputs = 0, nnodes = 0;
  std::vector<Code> consts;
  // The DAG's kept nodes in id order, its asserted and output nodes.
  std::vector<std::pair<uint64_t, Terms>> dag;
  std::vector<uint64_t> asserts, outputs;
  // Per layer above the inputs, per wire: its DAG node, copy flag, terms.
  struct Gate {
    uint64_t node;
    bool copy;
    Terms terms;
  };
  std::vector<std::vector<Gate>> layers;
  // The last-layer assertions (wire, node) and the output wires.
  std::vector<std::pair<uint64_t, uint64_t>> last_asserts;
  std::vector<uint64_t> out_wires;
};

// The node table and the entries of a certificate (emit_export.h): the
// table's size, each node's ENodeInfo and each entry's EntryCert, encoded.
struct GkrTable {
  uint64_t size = 0;
  std::vector<Bytes> nodes;
  std::vector<Bytes> entries;
};

namespace gkr_internal {
// A term list's chunk bits after a header of H bits (Lean's termsChunk).
inline void terms_chunk(BitPack &c, uint64_t w, uint64_t h, const GkrCore::Terms &ts) {
  for (size_t i = 0; i < ts.size(); ++i) {
    const uint64_t at = h + 3 * w * i;
    c.put(at, ts[i][0]);
    c.put(at + w, ts[i][1]);
    c.put(at + 2 * w, ts[i][2]);
  }
}
// A packed table (Table.packed e) of W-bit entries, 2^E to a chunk.
inline void packed(Bytes &o, uint64_t w, uint64_t e, const std::vector<GkrCore::Code> &xs) {
  const size_t per = size_t(1) << e;
  std::vector<Bytes> chunks((xs.size() + per - 1) / per);
  for (size_t j = 0; j < chunks.size(); ++j) {
    BitPack c;
    for (size_t t = 0; t < per && j * per + t < xs.size(); ++t) c.put(t * w, xs[j * per + t]);
    c.write(chunks[j]);
  }
  TrieWriter::Items items;
  for (size_t j = 0; j < chunks.size(); ++j) items.emplace_back(j, &chunks[j]);
  o.ctor(1);
  o.nat(e);
  TrieWriter::plain(o, items);
}
inline GkrCore::Code le(uint64_t x) {
  GkrCore::Code b;
  for (; x != 0; x >>= 8) b.push_back(uint8_t(x));
  return b;
}
inline void nats(Bytes &o, const std::vector<uint64_t> &v) {
  o.nat(v.size());
  for (uint64_t x : v) o.nat(x);
}
}  // namespace gkr_internal

// The DAG, constants and schedule of a GkrCertificate (circuits/compiler/
// gkr_certificate.h) over F, the other fields of K left as they are.
template <class Cert, class Field>
void gkr_core(GkrCore &k, const Cert &c, const Field &f) {
  std::vector<uint8_t> buf(Field::kBytes);
  auto code = [&](const typename Field::Elt &x) {
    f.to_bytes_field(buf.data(), x);
    return GkrCore::Code(buf.begin(), buf.end());
  };
  k.w = c.term_width();
  k.ninputs = c.ninput;
  k.nnodes = c.nnodes;
  k.consts.clear();
  for (const auto &x : c.constants) k.consts.push_back(code(x));
  k.dag.clear();
  for (size_t n = 0; n < c.node_id.size(); ++n) {
    GkrCore::Terms ts;
    for (size_t t = c.node_term_begin[n]; t < c.node_term_begin[n + 1]; ++t)
      ts.push_back({c.node_terms[3 * t], c.node_terms[3 * t + 1], c.node_terms[3 * t + 2]});
    k.dag.emplace_back(c.node_id[n], std::move(ts));
  }
  k.asserts.clear();
  for (uint32_t n : c.asserted()) k.asserts.push_back(n);
  k.outputs.clear();
  k.out_wires.clear();
  for (const auto &[n, g] : c.outputs) {
    k.outputs.push_back(n);
    k.out_wires.push_back(g);
  }
  const auto &s = c.wires;
  k.layers.clear();
  for (size_t d = 1; d < s.depths(); ++d) {
    std::vector<GkrCore::Gate> ws;
    for (size_t w = s.first_wire[d]; w < s.first_wire[d + 1]; ++w) {
      GkrCore::Gate g{s.op[w], s.copy[w] != 0, {}};
      for (size_t t = s.term_begin[w]; t < s.term_begin[w + 1]; ++t)
        g.terms.push_back({s.terms[3 * t], s.terms[3 * t + 1], s.terms[3 * t + 2]});
      ws.push_back(std::move(g));
    }
    k.layers.push_back(std::move(ws));
  }
  k.last_asserts.clear();
  for (const auto &[g, n] : c.last_asserts) k.last_asserts.emplace_back(g, n);
}

// Writes the sections of NAME : CircuitData (see the file comment) to F.
inline void write_gkr(File &f, const std::string &name, const GkrCore &k, const GkrTable &t) {
  using namespace gkr_internal;
  const std::string cert = "GordieHowe.GKR.Certificate.", rp = "GordieHowe.RealizedProgram.";
  const uint64_t w = k.w;
  // The constant table, at the width of its largest code.
  size_t wc = 1;
  for (const auto &x : k.consts) wc = std::max(wc, bit_length(x));
  Bytes consts;
  consts.nat(wc);
  packed(consts, wc, 4, k.consts);
  const size_t sConsts = f.section(name + ".consts", ty("GordieHowe.GKR.Fold.Consts"), kCompile,
                                   consts);
  // The DAG: per kept node 2 * |terms| | termsChunk w w terms.
  std::vector<Bytes> leaves(k.dag.size());
  TrieWriter::Items items;
  for (size_t i = 0; i < k.dag.size(); ++i) {
    BitPack c;
    c.put(0, 2 * k.dag[i].second.size());
    terms_chunk(c, w, w, k.dag[i].second);
    c.write(leaves[i]);
    items.emplace_back(k.dag[i].first, &leaves[i]);
  }
  Bytes dag;
  dag.inline_();
  TrieWriter::split(f, dag, items, name + ".dagPart", ty(cert + "NTree"),
                    log2_floor(std::max<uint64_t>(1, k.dag.size() / 2048)));
  dag.plain();
  dag.nat(k.ninputs);
  dag.plain();
  dag.nat(k.nnodes);
  dag.plain();
  nats(dag, k.asserts);
  dag.plain();
  nats(dag, k.outputs);
  const size_t sDag = f.section(name + ".dag", ty(cert + "Dag"), kSpine, dag);
  // The layers: per gate copy + 2 |terms| | g << w | node << 2w |
  // termsChunk w 3w terms; the wire tables, the nodes packed 4 to a chunk.
  std::vector<size_t> sLayers, sTabs;
  for (size_t d = 0; d < k.layers.size(); ++d) {
    const auto &ws = k.layers[d];
    Bytes layer;
    layer.nat(ws.size());
    std::vector<GkrCore::Code> nodes;
    for (size_t g = 0; g < ws.size(); ++g) {
      BitPack c;
      c.put(0, (ws[g].copy ? 1 : 0) + 2 * ws[g].terms.size());
      c.put(w, g);
      c.put(2 * w, ws[g].node);
      terms_chunk(c, w, 3 * w, ws[g].terms);
      c.write(layer);
      nodes.push_back(le(ws[g].node));
    }
    sLayers.push_back(
        f.section(name + "layer" + std::to_string(d), ty("List Nat"), kCompile | kReader, layer));
    Bytes tab;
    packed(tab, w, 2, nodes);
    sTabs.push_back(f.section(name + "wtab" + std::to_string(d), ty(cert + "Table"), kReader, tab));
  }
  Bytes layered;
  layered.inline_();
  layered.plain();
  layered.nat(k.ninputs);
  layered.inline_();
  layered.nat(sLayers.size());
  for (size_t s : sLayers) layered.ref(s);
  const size_t sLayered =
      f.section(name + ".layered", ty(cert + "Layered"), kCompile | kSpine, layered);
  Bytes width;
  width.nat(w);
  f.section(name + ".width", ty("Nat"), kCompile, width);
  Bytes sched;
  sched.inline_();
  sched.plain();
  sched.nat(w);
  sched.inline_();
  sched.nat(sTabs.size());
  for (size_t s : sTabs) sched.ref(s);
  sched.plain();
  sched.nat(k.last_asserts.size());
  for (const auto &[g, n] : k.last_asserts) {
    sched.nat(g);
    sched.nat(n);
  }
  sched.plain();
  nats(sched, k.out_wires);
  const size_t sSched = f.section(name + ".sched", ty(cert + "Cert"), kSpine, sched);
  // The node table.
  TrieWriter::Items tnodes;
  for (size_t i = 0; i < t.nodes.size(); ++i) tnodes.emplace_back(i, &t.nodes[i]);
  Bytes table;
  table.inline_();
  table.plain();
  table.nat(t.size);
  TrieWriter::split(f, table, tnodes, name + ".nodes", ty(rp + "Trie " + rp + "ENodeInfo"),
                    log2_floor(std::max<uint64_t>(1, t.nodes.size() / 512)));
  const size_t sTable = f.section(name + ".table", ty(rp + "ETable"), kSpine, table);
  Bytes entries;
  entries.nat(t.entries.size());
  for (const Bytes &e : t.entries) entries.bytes(e);
  const size_t sEntries =
      f.section(name + ".entries", ty("List GordieHowe.GKR.Rel.EntryCert"), 0, entries);
  // The certificate.
  Bytes cd;
  cd.inline_();
  cd.plain();
  cd.nat(k.c);
  cd.plain();
  cd.nat(w);
  cd.plain();
  cd.nat_le(k.chr);
  cd.plain();
  cd.nat_le(k.prime);
  cd.plain();
  cd.boolean(k.char2);
  cd.plain();
  cd.nat_le(k.neg1);
  cd.plain();
  cd.nat_le(k.half);
  for (size_t s : {sConsts, sDag, sLayered, sSched, sTable, sEntries}) cd.ref(s);
  f.section(name, ty(rp + "CircuitData"), kSpine | kReader, cd);
}

}  // namespace proofs::gordiehowe::ghc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_GHC_GKR_H_
