# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The tests of the GordieHowe core: the compiler, the proof system and the
# library functions (gordiehowe_add_test, ../CMakeLists.txt).
gordiehowe_add_test(gordiehowe_test gordiehowe_structure_test.cc
                    gordiehowe_packing_test.cc gordiehowe_expr_test.cc
                    gordiehowe_expr_ops_test.cc gordiehowe_relation_test.cc
                    gordiehowe_compile_cache_test.cc
                    gordiehowe_batch_form_test.cc
                    SETS gold4_gf128_sha256 gold4_gf128 gf128 gf256)
# Batched relations and the Keccak instance.
gordiehowe_add_test(gordiehowe_batch_test gordiehowe_batch_mac_test.cc
                    gordiehowe_batch_shake_test.cc
                    gordiehowe_batch_words_test.cc
                    gordiehowe_live_rows_test.cc
                    SETS gf128_sha256 gold4 gf128_3 qrom_emu gf256)
target_link_libraries(gordiehowe_batch_test sha3)
# The lowerings (ranges, selection, equalities).
gordiehowe_add_test(gordiehowe_lowering_test
                    gordiehowe_lowering_select_test.cc SETS gold4_gf256)
# Branch-free witness helpers against test-only reference implementations.
gordiehowe_add_test(gordiehowe_ct_test)
# wide_int.h's fixed-width integers (bounds, intervals, certificates) and
# ct.h's operations on them.
gordiehowe_add_test(wide_int_test)
# The transcript forks and joins (transcript_fork.h).
gordiehowe_add_test(gordiehowe_transcript_fork_test)
# The task pool's nesting and its waiting callers' help (threads.h).
gordiehowe_add_test(gordiehowe_threads_test)
# Operators (native NTT plans, NTT forms, spectral circuits).
gordiehowe_add_test(gordiehowe_operators_test
                    gordiehowe_operators_systems_test.cc
                    gordiehowe_operators_rings_test.cc SETS gold4)
# One Keccak batch shared by several sponge calls.
gordiehowe_add_test(gordiehowe_keccak_test SETS gf128_sha256 gf128 gf256)
target_link_libraries(gordiehowe_keccak_test sha3 xkcp)
# SHA-256 (sha256.h): the host side, and proofs in both modes (the GKR mode
# runs Longfellow's flat SHA-256 circuit and witness, flatsha).
gordiehowe_add_test(gordiehowe_sha256_test gordiehowe_sha256_system_test.cc
                    SETS gf128_sha256 gf256)
target_link_libraries(gordiehowe_sha256_test flatsha)
# D.commit: committed values equal to expressions, their witnesses
# evaluated by the compiler.
gordiehowe_add_test(gordiehowe_commit_test SETS gf128_sha256 gf256 gold4)
target_link_libraries(gordiehowe_commit_test sha3)
# The protocol hash of each field profile: digest and salt sizes, and a
# proof under one hash rejected under the other.
gordiehowe_add_test(gordiehowe_profile_hash_test SETS gf128_sha256 gf128 gf256)
# The native norm and encodability gadgets, gadget certificates.
gordiehowe_add_test(gordiehowe_norm_test SETS fp14_9 falcon20)
# assert_mod, the MAC lowering and the range groups.
gordiehowe_add_test(gordiehowe_mod_test SETS mod)
# The per-chunk MAC ablation (CompileProfile::unsound_per_chunk_mac).
gordiehowe_add_test(gordiehowe_per_chunk_mac_test SETS rom_emu qrom_emu)
# Interval propagation through products, assert_int_equal and the conv
# realizations.
gordiehowe_add_test(gordiehowe_int_equal_test SETS mod)
# The Ligero parameter choice (compiler/ligero_choice.h).
gordiehowe_add_test(gordiehowe_ligero_choice_test)
# The compiled plan as Lean data (plan_export.h).
gordiehowe_add_test(gordiehowe_plan_export_test SETS gold4_gf256)
# Public tables, ordered selection and record permutations.
gordiehowe_add_test(gordiehowe_table_test SETS gold4_gf256)
# F_p256: a prime, unpacked domain, and its per-cell, per-term and
# per-instance rates.
gordiehowe_add_test(gordiehowe_p256_test SETS p256)
gordiehowe_add_test(gordiehowe_sample_test SETS gf128 gf128_sha256)
target_link_libraries(gordiehowe_sample_test ml_dsa sha3)
# The library functions over the core (windows, ordered selection, memory
# checking, multiset equality, word arithmetic) in a binary and an odd
# field.
gordiehowe_add_test(gordiehowe_library_test SETS gf128 gold4)
# The example program listings of gordiehowe_spec_examples_test.cc as tests.
gordiehowe_add_test(gordiehowe_spec_examples_test)
target_link_libraries(gordiehowe_spec_examples_test ml_dsa sha3)

# Compiler tests on the example applications' systems (EXAMPLES links
# their builders, examples/CMakeLists.txt).
# The constructions' batches over their live rows against all their rows,
# single- and multi-threaded, byte for byte (field_skip.h; live_rows_test.cc).
gordiehowe_add_test(live_rows_test live_rows_falcon_native_test.cc
                    live_rows_mldsa_native_test.cc
                    live_rows_mldsa_emulated_test.cc
                    EXAMPLES falcon_emulated falcon_native mldsa_native mldsa_emulated
                    SETS rom_emu qrom_emu rom_ml_dsa qrom_ml_dsa
                    rom_falcon_native qrom_falcon_native)
target_link_libraries(live_rows_test ml_dsa sha3 OpenSSL::Crypto)
# The placement rule (placement.h) on small domains of the profiles' fields,
# and the microbench of its rates (DISABLED_Rates).
gordiehowe_add_test(placement_test
                    SETS rom_ml_dsa qrom_ml_dsa rom_falcon_native
                    qrom_falcon_native rom_emu qrom_emu p256 rom_fp128)
target_link_libraries(placement_test ml_dsa sha3)
# The tree-cost experiment: forced chains and the per-stage microbench.
gordiehowe_add_test(tree_cost_test
                    SETS rom_ml_dsa qrom_ml_dsa rom_falcon_native
                    qrom_falcon_native rom_emu qrom_emu)
target_link_libraries(tree_cost_test ml_dsa sha3)
# The low-degree test's repetitions end to end.
gordiehowe_add_test(ldt_reps_test
                    SETS rom_ml_dsa qrom_ml_dsa rom_falcon_native
                    qrom_falcon_native)
target_link_libraries(ldt_reps_test ml_dsa sha3)
# assert_in (membership.h) in both profiles' ML-DSA native fields and in
# F_p256: fixed kappa and gamma packing, several tables per domain, and
# assert_range as assert_in on [0, n).
gordiehowe_add_test(membership_test SETS rom_ml_dsa qrom_ml_dsa p256)
target_link_libraries(membership_test ml_dsa sha3)
# Interval propagation in prime fields above 2^127: Fp128 (the RSA system's
# A profile) and F_p256, values unrequested, requested at p and at 2^100,
# and assert_int_equal's no-wrap check over them.
gordiehowe_add_test(wide_prime_interval_test SETS rom_fp128 p256)
target_link_libraries(wide_prime_interval_test flatsha util OpenSSL::Crypto)
# The compile time of four relations, fresh and from the compile cache,
# the provisional pass's tableau against the scheduled circuit's, and the
# lazy provisional tableau against the one computed up front.
gordiehowe_add_test(compile_time_test
                    EXAMPLES falcon_native falcon_emulated mldsa_native composite
                    SETS rom_falcon_native qrom_falcon_native
                    rom_ml_dsa qrom_ml_dsa rom_emu qrom_emu
                    rom_composite qrom_composite mdoc qrom_ecdsa)
target_link_libraries(compile_time_test ml_dsa sha3 flatsha util
                      OpenSSL::Crypto)
# The per-chunk MAC ablation's untimed smoke check on the ECDSA mDL, the
# emulated ML-DSA-44 proof of possession and the post-quantum mDL's arms
# at the ROM parameters (DISABLED_ tests: run them explicitly).
gordiehowe_add_test(per_chunk_mac_test
                    EXAMPLES mldsa_emulated
                    SETS mdoc rom_emu rom_ml_dsa)
target_link_libraries(per_chunk_mac_test ml_dsa sha3 flatsha util
                      OpenSSL::Crypto)
