// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// Timing and correctness driver for vole-mole's ML-DSA-44 proof of knowledge
// (cloudflareresearch/vole-mole PR #49), linked against the PR's library.
//
//   vm_bench FIXTURE_DIR LABEL WARMUPS TRIALS
//
// FIXTURE_DIR holds pk.hex, msg.hex and sig.hex: the ML-DSA-44 fixture our
// proof of possession proves (lib/circuits/tests/pq/ml_dsa/
// ml_dsa_44_benchmark.inc: 32-byte message, empty context).
//
// Output, one line each:
//   VM_SETUP   the one-time sparse-weight table build (recode_table), timed
//              before anything else, and the proof size
//   VM_TRIAL   per trial: P = prove(pk, msg, sig) (witness generation and
//              proof), V = verify(pk, proof) (statement preparation: pkDecode,
//              tr, ExpandA and the NTTs of sigma(A), sigma(t1 2^d); then
//              proof checking), and separately prep = make_statement(pk) and
//              Vcore = verify_proof(stmt, proof) on a prepared statement
//   VM_CHECK   correctness outcomes (after the timed trials)
#include "vole_mole/mldsa.hpp"
#include "vole_mole/mldsa_pok.hpp"

#include "mldsa/mldsa.hpp"
#include "mldsa_pok/prover.hpp"
#include "mldsa_pok/relation.hpp"
#include "mldsa_pok/verify_gadget.hpp"

#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace vole_mole;
namespace d = vole_mole::mldsa_pok::detail;
using Clock = std::chrono::steady_clock;

namespace {

std::vector<uint8_t> read_hex(const std::string& path) {
    std::ifstream f(path);
    std::string s;
    f >> s;
    if (s.size() % 2 != 0) {
        throw std::runtime_error("odd hex: " + path);
    }
    std::vector<uint8_t> out(s.size() / 2);
    for (size_t i = 0; i < out.size(); ++i) {
        out[i] = static_cast<uint8_t>(std::stoul(s.substr(2 * i, 2), nullptr, 16));
    }
    return out;
}

template <typename A> A to_array(const std::vector<uint8_t>& v, const char* what) {
    A a{};
    if (v.size() != a.size()) {
        throw std::runtime_error(std::string("wrong length: ") + what);
    }
    std::copy(v.begin(), v.end(), a.begin());
    return a;
}

double ms_since(Clock::time_point t0) {
    return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
}

void flip(std::vector<uint8_t>& bytes, size_t bit) {
    bytes[bit / 8] = static_cast<uint8_t>(bytes[bit / 8] ^ (1u << (bit % 8)));
}

// "accepted", "rejected", or "prover refused: <what>".
std::string api_outcome(const mldsa::PublicKey<mldsa::MlDsa44>& pk, const mldsa_pok::Message& msg,
                        const mldsa::Signature<mldsa::MlDsa44>& sig) {
    try {
        const auto proof = mldsa_pok::prove(pk, msg, sig);
        return mldsa_pok::verify(pk, proof) ? "accepted" : "rejected";
    } catch (const std::exception& e) {
        return std::string("prover refused: ") + e.what();
    }
}

} // namespace

int main(int argc, char** argv) {
    if (argc != 5) {
        std::fprintf(stderr, "usage: %s FIXTURE_DIR LABEL WARMUPS TRIALS\n", argv[0]);
        return 2;
    }
    const std::string dir = argv[1];
    const std::string label = argv[2];
    const int warmups = std::atoi(argv[3]);
    const int trials = std::atoi(argv[4]);

    // The one-time table, built before any proof (vole-mole excludes it from its timings).
    const auto t0 = Clock::now();
    const auto& table = d::MlDsaModQ::recode_table();
    const double table_ms = ms_since(t0);

    const auto pk = to_array<mldsa::PublicKey<mldsa::MlDsa44>>(read_hex(dir + "/pk.hex"), "pk");
    const auto msg = to_array<mldsa_pok::Message>(read_hex(dir + "/msg.hex"), "msg");
    const auto sig = to_array<mldsa::Signature<mldsa::MlDsa44>>(read_hex(dir + "/sig.hex"), "sig");
    if (!mldsa::verify<mldsa::MlDsa44>(pk, msg, {}, sig)) {
        std::fprintf(stderr, "fixture signature does not verify\n");
        return 1;
    }
    std::printf("VM_SETUP label=%s table_ms=%.3f table_bytes=%zu proof_bytes=%zu\n", label.c_str(),
                table_ms, table.size(), mldsa_pok::PROOF_BYTES);
    std::fflush(stdout);

    for (int r = 0; r < warmups + trials; ++r) {
        auto t = Clock::now();
        const auto proof = mldsa_pok::prove(pk, msg, sig);
        const double p = ms_since(t);
        t = Clock::now();
        const bool ok = mldsa_pok::verify(pk, proof);
        const double v = ms_since(t);
        t = Clock::now();
        const auto stmt = d::make_statement(pk);
        const double prep = ms_since(t);
        t = Clock::now();
        const bool ok2 = d::verify_proof(
            stmt, std::span<const uint8_t, d::PROOF_BYTES_>(proof.data(), proof.size()));
        const double vcore = ms_since(t);
        std::printf("VM_TRIAL label=%s r=%d warm=%d P=%.3f V=%.3f prep=%.3f Vcore=%.3f bytes=%zu "
                    "ok=%d\n",
                    label.c_str(), r, r < warmups ? 1 : 0, p, v, prep, vcore, proof.size(),
                    ok && ok2 ? 1 : 0);
        std::fflush(stdout);
        if (!ok || !ok2) {
            return 1;
        }
    }

    // Correctness. Through the API: the prover checks the signature first.
    std::printf("VM_CHECK label=%s case=valid outcome=%s\n", label.c_str(),
                api_outcome(pk, msg, sig).c_str());
    {
        // One flipped bit of z: bit 0 of z's first byte in the encoded signature (after c-tilde).
        auto bad = sig;
        bad[mldsa::MlDsa44::LAMBDA / 4] ^= 1;
        std::printf("VM_CHECK label=%s case=api-z-bit outcome=%s\n", label.c_str(),
                    api_outcome(pk, msg, bad).c_str());
        auto bad_msg = msg;
        bad_msg[0] ^= 1;
        std::printf("VM_CHECK label=%s case=api-msg-bit outcome=%s\n", label.c_str(),
                    api_outcome(pk, bad_msg, sig).c_str());
    }
    // A cheating prover: the honest witness with one witness bit flipped (bit 0 of z_0, and
    // separately bit 0 of the message), proved without the prover's checks.
    {
        const auto stmt = d::make_statement(pk);
        const auto decoded = mldsa::detail::decode_signature<mldsa::MlDsa44>(sig);
        const d::Rho rho{7};
        const struct {
            const char* name;
            size_t bit;
        } cases[] = {{"witness-z-bit", d::SIG.z_bit(0, 0)}, {"witness-msg-bit", d::MU.msg_bit(0)}};
        for (const auto& c : cases) {
            auto w = d::make_witness(stmt, msg, *decoded);
            flip(w.prefix, c.bit);
            std::string outcome;
            try {
                const auto proof = d::prove_witness(stmt, w, rho);
                outcome = d::verify_proof(stmt, std::span<const uint8_t, d::PROOF_BYTES_>(
                                                    proof.data(), proof.size()))
                              ? "accepted"
                              : "rejected";
            } catch (const std::exception& e) {
                outcome = std::string("prover failed: ") + e.what();
            }
            std::printf("VM_CHECK label=%s case=%s outcome=%s\n", label.c_str(), c.name,
                        outcome.c_str());
        }
    }
    return 0;
}
