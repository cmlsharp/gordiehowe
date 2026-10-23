// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe post-quantum mdoc (pq_mdoc.h): the test and bench system in
// either arm of domain A, over the ML-DSA native profile's fields
// (mldsa_native.h's Env, FqArm) or the emulated one's (mldsa_emulated.h's
// Env, GoldilocksArm), and its statement and witness from the test data of
// pq_mdoc_data.h.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_TESTING_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_TESTING_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <vector>

#include "circuits/tests/pq/ml_dsa/ml_dsa_44_examples.h"
#include "gordiehowe/compiler/compile_options.h"
#include "gordiehowe/examples/shared/domain_profile.h"
#include "gordiehowe/examples/mldsa/mldsa_emulated.h"
#include "gordiehowe/examples/mldsa/mldsa_native.h"
#include "gordiehowe/examples/mldsa/mldsa_native_testing.h"
#include "gordiehowe/examples/mdoc/mdoc_hash_builders.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc_builders.h"
#include "gordiehowe/examples/pq_mdoc/pq_mdoc_data.h"
#include "gordiehowe/examples/shared/system_testing.h"
#include "gordiehowe/lib/message_builders.h"

namespace proofs::gordiehowe::examples::pq_mdoc {

// Where A's Boolean checks go: the placement rule (kAuto, the default) or a
// target forced by bit_checks_force.
struct PqMdocConfig {
  Placement bit_checks = Placement::kAuto;
  // H's GF(2^16) words committed unpacked (DomainProfile::unpacked_s0, a
  // test-only ablation).
  bool h_unpacked_s0 = false;
  // A's F_q coordinates committed unpacked, one per cell in Ligero's
  // subfield rows (DomainProfile::unpacked_s0, a test-only ablation).
  bool a_unpacked_s0 = false;
  // False: the device-signature ablation (pq_mdoc_relation's
  // DEVICE_SIGNATURE, a test-only ablation), the system named
  // <arm's name>-nodevice.
  bool device_signature = true;
  // True: the MAC ablation (CompileProfile::unsound_no_mac, a measurement
  // control: no MAC, unsound), the system named <name>-nomac.
  bool unsound_no_mac = false;
  // True: the per-chunk MAC ablation (CompileProfile::unsound_per_chunk_mac,
  // a measurement control: Longfellow's per-chunk MAC, not zero-knowledge),
  // the system named <name>-perchunk.
  bool unsound_per_chunk_mac = false;
  // The compile cache (CompileOptions::cache); off by default.
  CompileCache cache;
};

// Each arm's fields and profiles in profile P: the proof of possession's
// of that arm (mldsa_native.h, mldsa_emulated.h), and the arm's range table
// (512 native, 4096 emulated).
template <class P, class Arm>
struct ArmProfiles;
template <class P>
struct ArmProfiles<P, FqArm> {
  using E = examples::mldsa::Env<P>;
  static constexpr const char *kName = "pq-mdoc";
  // The native proof of possession's fields (domain_profile.h: A's
  // block_enc at most 8192, the native NTT's length over F_q), A's F_q
  // coordinates unpacked under UNPACKED_S0.
  static auto a_profile(const E &env, bool unpacked_s0) {
    auto ap = domain_profile<P>(env.af, env.rsa);
    ap.unpacked_s0 = unpacked_s0;
    return ap;
  }
  static auto h_profile(const E &env) {
    return domain_profile<P>(env.hf, env.rsh);
  }
  static CompileProfile compile_profile() {
    return examples::mldsa::compile_profile<P>();
  }
};
template <class P>
struct ArmProfiles<P, GoldilocksArm> {
  using E = examples::mldsa::emulated::Env<P>;
  static constexpr const char *kName = "pq-mdoc-goldilocks";
  // The emulated proof of possession's fields (domain_profile.h); A has
  // no unpacked ablation.
  static auto a_profile(const E &env, bool unpacked_s0) {
    if (unpacked_s0)
      throw std::runtime_error("pq_mdoc: no unpacked A in the Goldilocks arm");
    return domain_profile<P>(env.af, env.rsa.factory());
  }
  static auto h_profile(const E &env) {
    return domain_profile<P>(env.hf, env.rsh);
  }
  static CompileProfile compile_profile() {
    return examples::mldsa::emulated::compile_profile<P>();
  }
};

// The placement pins (CompileOptions::placement_force) of A's Boolean
// checks at WHERE; none at kAuto.
inline std::string bit_checks_force(Placement where) {
  return where == Placement::kCircuit     ? "A/boolean=circuit"
         : where == Placement::kBatch     ? "A/boolean=batch"
         : where == Placement::kQuadratic ? "A/boolean=quadratic"
                                          : "";
}

// The relation of profile P in ARM for N_ATTR attributes and a device
// message of DEVICE_TBS_BYTES bytes, with the assignments of the host's
// values, for the tests and benchmarks that drive the prover directly.
template <class P, class Arm = FqArm>
struct PqMdocSystem
    : RelationSystem<typename ArmProfiles<P, Arm>::E::Sys,
                     PqMdocStatement<Value>, PqMdocWitness<Value>> {
  using Profiles = ArmProfiles<P, Arm>;
  using E = typename Profiles::E;
  using Sys = typename E::Sys;
  using Base =
      RelationSystem<Sys, PqMdocStatement<Value>, PqMdocWitness<Value>>;
  using typename Base::Assignment;

  Placement bit_checks;

  static auto h_profile(const E &env, const PqMdocConfig &cfg) {
    auto hp = Profiles::h_profile(env);
    hp.unpacked_s0 = cfg.h_unpacked_s0;
    return hp;
  }
  // The system's name: the arm's, with -nodevice under the
  // device-signature ablation, -nomac under the MAC ablation and -perchunk
  // under the per-chunk MAC ablation.
  static std::string name(const PqMdocConfig &cfg) {
    return std::string(Profiles::kName) +
           (cfg.device_signature ? "" : "-nodevice") +
           (cfg.unsound_no_mac ? "-nomac" : "") +
           (cfg.unsound_per_chunk_mac ? "-perchunk" : "");
  }
  static CompileProfile compile_profile(const PqMdocConfig &cfg) {
    CompileProfile c = Profiles::compile_profile();
    c.name = name(cfg);
    c.unsound_no_mac = cfg.unsound_no_mac;
    c.unsound_per_chunk_mac = cfg.unsound_per_chunk_mac;
    return c;
  }

  PqMdocSystem(const E &env, size_t n_attr, size_t device_tbs_bytes,
               const PqMdocConfig &cfg = {})
      : Base(declare(env, n_attr, device_tbs_bytes, cfg)),
        bit_checks(cfg.bit_checks) {}

  // The relation, compiled with A's Boolean checks at CFG.bit_checks.
  static Relation<PqMdocStatement<Value>, PqMdocWitness<Value>> declare(
      const E &env, size_t n_attr, size_t device_tbs_bytes,
      const PqMdocConfig &cfg) {
    CompileOptions options;
    options.cache = cfg.cache;
    options.placement_force = bit_checks_force(cfg.bit_checks);
    return pq_mdoc<Arm, Sys>(
        compile_profile(cfg), name(cfg), h_profile(env, cfg),
        Profiles::a_profile(env, cfg.a_unpacked_s0), n_attr,
        device_tbs_bytes, cfg.device_signature, options);
  }
  Assignment statement(const PqMdocStatementData &x) const {
    return Base::statement(pq_mdoc_statement(x));
  }
  Assignment witness(const PqMdocData &d) const {
    return Base::witness(pq_mdoc_witness(d));
  }
};

// ------------------------------------------------------------- instances --

struct Instance {
  PqMdocStatementData statement;
  PqMdocData data;
};

// v7's statement layout of element E (mdoc_hash_testing.h's statement_of).
inline examples::mdoc::MdocAttributeStatement statement_of(
    const data::Element &e) {
  examples::mdoc::MdocAttributeStatement x;
  std::vector<uint8_t> id = data::Cbor().tstr(e.id).b;
  for (size_t j = 0; j < id.size() && j < 32; ++j) x.id[j] = id[j];
  for (size_t j = 0; j < e.value.size() && j < 64; ++j) x.value[j] = e.value[j];
  x.id_len = uint8_t(1 + 17 + 1 + e.id.size());
  x.value_len = uint8_t(e.value.size() + 12 + 1);
  return x;
}

// The decoded signature SIG of MSG under PK, checked by the reference
// verifier (ml_dsa_witness's compute_witness, empty context).
inline examples::mldsa::Signature decoded(const std::vector<uint8_t> &pk,
                                const std::vector<uint8_t> &msg,
                                const std::vector<uint8_t> &sig) {
  ml_dsa::MlDsa44SignatureExample ex;
  ex.msg = msg;
  ex.pkey = pk;
  ex.sig = sig;
  const examples::mldsa::support::Existing e(ex);
  if (!e.ok) throw std::runtime_error("pq_mdoc: the reference verifier rejects");
  return e.signature();
}

// The 2-block SHA-256 padding of ITEM (v7's attribute buffer).
inline examples::mdoc::MdocHashData::Item padded_item(const data::Item &it) {
  examples::mdoc::MdocHashData::Item out;
  const size_t n = it.bytes.size();
  for (size_t i = 0; i < n; ++i) out.bytes[i] = it.bytes[i];
  out.bytes[n] = 0x80;
  const uint64_t bits = uint64_t(n) * 8;
  for (size_t i = 0; i < 8; ++i)
    out.bytes[data::kItemBytes - 1 - i] = uint8_t(bits >> (8 * i));
  out.length = n;
  out.i1 = it.i1;
  out.i2 = it.i2;
  out.i3 = it.i3;
  for (size_t j = 0; j < 4; ++j) out.l[j] = it.l[j];
  out.perm = it.perm;
  return out;
}

// The MSO buffer of TBS (cose_prefix || MSO): MSO's bytes, then SHAKE256's
// padding of tr || 00 00 || TBS at its place in the 29-block buffer, then
// zeros. Returns the buffer and sets LENGTH.
inline std::vector<uint8_t> mso_buffer(const std::vector<uint8_t> &tbs,
                                       size_t &length) {
  if (tbs.size() < kPrefixBytes ||
      !std::equal(cose_prefix().begin(), cose_prefix().end(), tbs.begin()))
    throw std::runtime_error("mso_buffer: the ToBeSigned prefix");
  length = kTrBytes + 2 + tbs.size();
  // The MSO's part of the buffer, kHeadBytes = tr || 00 00 || cose_prefix
  // in front of it; the buffer holds at most kBufBytes - 1 message bytes.
  const lib::message::Layout layout{kHeadBytes, kMsoBytes - 1, kMsoBytes};
  return lib::message::shake256_part(
      layout,
      std::vector<uint8_t>(tbs.begin() + long(kPrefixBytes), tbs.end()));
}

// The instance of presentation X.
inline Instance instance_of(const data::Presentation &x) {
  const auto &doc = x.doc;
  Instance in;
  auto &st = in.statement;
  st.now = x.now;
  for (size_t e : x.requested)
    st.attributes.push_back(statement_of(doc.elements.at(e)));
  st.issuer_pk = doc.issuer.pk;
  st.device_tbs = x.device_tbs;
  auto &d = in.data;
  d.mso = mso_buffer(doc.tbs, d.length);
  // The windows' offsets, from MSO byte 7.
  const std::vector<uint8_t> mso(doc.tbs.begin() + long(kPrefixBytes),
                                 doc.tbs.end());
  auto at = [&mso](const std::vector<uint8_t> &needle) {
    const size_t i = data::find(mso, needle);
    if (i < kWindowFirst) throw std::runtime_error("instance_of: window");
    return i - kWindowFirst;
  };
  d.offsets = {at(examples::mdoc::valid_from_key()),
               at(examples::mdoc::valid_until_key()), at(device_key_info_key()),
               at(examples::mdoc::value_digests_key())};
  for (size_t e : x.requested) {
    const auto &it = doc.items.at(e);
    std::vector<uint8_t> w = examples::mdoc::digest_key();
    w.insert(w.end(), it.digest.begin(), it.digest.end());
    d.offsets.push_back(at(w));
    d.items.push_back(padded_item(it));
  }
  d.issuer_sig = decoded(doc.issuer.pk, doc.tbs, doc.issuer_sig);
  d.device_sig = decoded(doc.device.pk, x.device_tbs, x.device_sig);
  return in;
}

// The bench's instance: the issuer key of label 1, the device key of label
// 2, and N of Longfellow's bench attributes.
inline Instance bench_instance(size_t n) {
  static const data::Document doc = data::issue(data::keygen(1), data::keygen(2));
  return instance_of(data::present(doc, data::bench_request(n)));
}

}  // namespace proofs::gordiehowe::examples::pq_mdoc

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_EXAMPLES_PQ_MDOC_PQ_MDOC_TESTING_H_
