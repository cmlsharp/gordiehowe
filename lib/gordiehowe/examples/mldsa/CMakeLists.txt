# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# ML-DSA proofs of possession: the native arm (mldsa_native.h) and the
# emulated arm (mldsa_emulated.h), and the parts they share, at the
# parameter sets ML-DSA-44 (mldsa_native, mldsa_emulated), ML-DSA-65
# (mldsa65_*) and ML-DSA-87 (mldsa87_*): one example system per set and
# arm, one translation unit per profile.
gordiehowe_add_example_system(mldsa_native)
gordiehowe_add_example_system(mldsa_emulated)
gordiehowe_add_example_system(mldsa65_native)
gordiehowe_add_example_system(mldsa65_emulated)
gordiehowe_add_example_system(mldsa87_native)
gordiehowe_add_example_system(mldsa87_emulated)

gordiehowe_add_test(mldsa_native_test
                    EXAMPLES mldsa_native
                    SETS rom_ml_dsa qrom_ml_dsa)
target_link_libraries(mldsa_native_test ml_dsa sha3 OpenSSL::Crypto)
# The verifier's phase records (the phase timers, which the diagnostics
# option profile turns on: --diagnostics profile, diagnostics::Options)
# add up to each domain's total, on ML-DSA native packed and under the
# packing ablation; its own binary, since it turns the phase timers on.
gordiehowe_add_test(verify_phases_test
                    EXAMPLES mldsa_native
                    SETS rom_ml_dsa qrom_ml_dsa)
target_link_libraries(verify_phases_test ml_dsa sha3 OpenSSL::Crypto)
gordiehowe_add_test(mldsa_emulated_test mldsa_emulated_parallel_test.cc
                    EXAMPLES mldsa_emulated
                    SETS rom_emu qrom_emu)
target_link_libraries(mldsa_emulated_test ml_dsa sha3 OpenSSL::Crypto)
# ML-DSA-65 and ML-DSA-87, both arms and both profiles
# (mldsa_sets_test.cc): one translation unit per set, profile and arm
# (sets/), and the host checks.
set(MLDSA_SET_TESTS)
foreach(SET 65 87)
  foreach(ARM native emulated)
    foreach(PROFILE rom qrom)
      list(APPEND MLDSA_SET_TESTS sets/mldsa${SET}_${ARM}_${PROFILE}_test.cc)
    endforeach()
  endforeach()
endforeach()
gordiehowe_add_test(mldsa_sets_test ${MLDSA_SET_TESTS}
                    EXAMPLES mldsa65_native mldsa65_emulated mldsa87_native
                             mldsa87_emulated
                    SETS rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu)
target_link_libraries(mldsa_sets_test ml_dsa sha3 OpenSSL::Crypto)
# ML-DSA-44's ExpandA from a private seed (expand_a.h): SHAKE128 in one
# Keccak batch, sixteen RejNTTPoly selections under one challenge, and
# A_hat crossed into the ML-DSA native domain.
gordiehowe_add_test(expand_a_test SETS rom_ml_dsa qrom_ml_dsa)
target_link_libraries(expand_a_test ml_dsa sha3)
# x.to(A) and a bound in H between the ML-DSA native profile's domains,
# with A's Boolean checks in the circuit and batched.
gordiehowe_add_test(crossing_test SETS rom_ml_dsa qrom_ml_dsa)
target_link_libraries(crossing_test ml_dsa sha3)

# The bench executables (bench/cli.h), in the build tree's bench/ beside
# report_bench, which runs their serve commands as its workers; and the
# measurement benches of ExpandA's cost split and of the crossing of H's
# integers to A.
gordiehowe_add_bench(mldsa_native_bench
                     EXAMPLES mldsa_native mldsa65_native mldsa87_native
                     SETS rom_ml_dsa qrom_ml_dsa)
target_link_libraries(mldsa_native_bench ml_dsa sha3 OpenSSL::Crypto)
gordiehowe_add_bench(mldsa_emulated_bench
                     EXAMPLES mldsa_emulated mldsa65_emulated mldsa87_emulated
                     SETS rom_emu qrom_emu)
target_link_libraries(mldsa_emulated_bench ml_dsa sha3 OpenSSL::Crypto)
gordiehowe_add_bench(expand_a_bench SETS rom_ml_dsa qrom_ml_dsa)
target_link_libraries(expand_a_bench ml_dsa sha3)
gordiehowe_add_bench(crossing_bench SETS rom_ml_dsa qrom_ml_dsa)
target_link_libraries(crossing_bench ml_dsa sha3)
