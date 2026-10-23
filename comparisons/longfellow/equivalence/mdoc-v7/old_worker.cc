// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The old side of the mdoc v7 equivalence run: the fork-based driver of
// benchmarks/2026-10-07-mac-cost (longfellow_mac_ablation.cc, branch
// mac-bench-gh f2edc952, its timed copies of the fork's run_mdoc_prover and
// run_mdoc_verifier), compiled against that commit's libmdoc_static.a, with
// its main replaced by a worker of common/bench_worker.h.
//
// usage: old_worker mac|nomac DOC_INDEX NATTR
//
// The trial's totals use the definitions of baselines/mdoc-v7's driver:
// commit = hash_commit + sig_commit, prove = macs + hash_prove + sig_prove,
// verify = v_setup + v_statement + v_hash_recv + v_sig_recv + v_macs +
// v_hash_verify + v_sig_verify (everything after the circuit parse and the
// proof read).
#define main lfb_old_ablation_main
#include "longfellow_mac_ablation.cc"
#undef main

#include <map>

#include "bench_worker.h"

int main(int argc, char** argv) {
  if (argc != 4) return 2;
  const bool nomac = std::string(argv[1]) == "nomac";
  const int doc = std::atoi(argv[2]);
  const size_t na = std::strtoull(argv[3], nullptr, 10);
  if (na < 1 || na > 4 || (doc != 3 && na != 1)) return 2;
  set_log_level(ERROR);
  const RequestedAttribute all[4] = {
      test::age_over_18, test::familyname_mustermann,
      test::birthdate_1971_09_01, test::height_175};
  const MdocTests* t = &mdoc_tests[doc];
  const ZkSpecStruct* spec = &kZkSpecs[na - 1];
  uint8_t* circuit;
  size_t clen;
  mac_circuit_ablated = nomac;
  if (generate_circuit(spec, &circuit, &clen) != CIRCUIT_GENERATION_SUCCESS) {
    return 3;
  }
  mac_circuit_ablated = false;
  lfb::info({{"variant", nomac ? "nomac" : "mac"},
             {"doc", std::to_string(doc)},
             {"nattr", std::to_string(na)},
             {"spec_version", std::to_string(spec->version)},
             {"circuit_zst_bytes", std::to_string(clen)}});
  lfb::serve([&]() {
    lfb::Trial T;
    Marks M;
    M.reset();
    uint8_t* prf = nullptr;
    size_t plen = 0;
    auto rc = timed_prover(M, circuit, clen, t->mdoc, t->mdoc_size,
                           t->pkx.as_pointer, t->pky.as_pointer, t->transcript,
                           t->transcript_size, all, na, (const char*)t->now,
                           &prf, &plen, spec);
    if (rc != MDOC_PROVER_SUCCESS) return T;
    Marks V;
    V.reset();
    auto rv = timed_verifier(V, circuit, clen, t->pkx.as_pointer,
                             t->pky.as_pointer, t->transcript,
                             t->transcript_size, all, na, (const char*)t->now,
                             prf, plen, t->doc_type, spec);
    free(prf);
    std::map<std::string, double> m;
    for (auto& p : M.v) {
      m[p.first] = p.second;
      T.add(p.first, p.second);
    }
    for (auto& p : V.v) {
      m[p.first] = p.second;
      T.add(p.first, p.second);
    }
    T.commit_ms = m["hash_commit"] + m["sig_commit"];
    T.prove_ms = m["macs"] + m["hash_prove"] + m["sig_prove"];
    T.verify_ms = m["v_setup"] + m["v_statement"] + m["v_hash_recv"] +
                  m["v_sig_recv"] + m["v_macs"] + m["v_hash_verify"] +
                  m["v_sig_verify"];
    T.proof_bytes = plen;
    T.ok = rv == MDOC_VERIFIER_SUCCESS;
    return T;
  });
  free(circuit);
  return 0;
}
