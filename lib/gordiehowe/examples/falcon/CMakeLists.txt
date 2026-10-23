# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Falcon-512 proofs of possession: the native arm (falcon_native.h) and the
# emulated arm (falcon_emulated.h), over the hash domain of falcon_hash.h.
gordiehowe_add_example_system(falcon_native)
gordiehowe_add_example_system(falcon_emulated)

gordiehowe_add_test(falcon_emulated_test falcon_emulated_layout_test.cc
                    falcon_emulated_threads_test.cc
                    EXAMPLES falcon_emulated
                    SETS rom_emu qrom_emu)
target_link_libraries(falcon_emulated_test sha3)
gordiehowe_add_test(falcon_native_test
                    EXAMPLES falcon_native
                    SETS rom_falcon_native qrom_falcon_native)
target_link_libraries(falcon_native_test sha3)

# The bench executables (bench/cli.h), in the build tree's bench/.
gordiehowe_add_bench(falcon_native_bench
                     EXAMPLES falcon_native
                     SETS rom_falcon_native qrom_falcon_native)
target_link_libraries(falcon_native_bench sha3)
gordiehowe_add_bench(falcon_emulated_bench
                     EXAMPLES falcon_emulated
                     SETS rom_emu qrom_emu)
target_link_libraries(falcon_emulated_bench sha3)
