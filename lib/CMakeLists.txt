# Copyright 2025 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# Modified 2026 by Chad Sharp and Paul Grubbs: C++23, Dev build type, OpenSSL, separate third_party/longfellow include root and object libraries, report_bench target, tools directory, Longfellow's own tests built from third_party/longfellow; on aarch64, a caller's -march/-mcpu in place of the default -march; aarch64 build goals

cmake_minimum_required(VERSION 3.13)
project(proofs)

# Dev: a build type for test iteration. Most of a large test file's compile
# time is the optimizer at -O3; -O1 roughly halves it. Benchmarks and the
# final test run before a merge use Release.
if(NOT CMAKE_CXX_FLAGS_DEV)
  set(CMAKE_CXX_FLAGS_DEV "-O1 -DNDEBUG" CACHE STRING "C++ flags of the Dev build type" FORCE)
endif()
if(NOT CMAKE_C_FLAGS_DEV)
  set(CMAKE_C_FLAGS_DEV "-O1 -DNDEBUG" CACHE STRING "C flags of the Dev build type" FORCE)
endif()
# C++23, which the flake's clang 21 and libstdc++ 15 support (the
# designated initializers of linear_operator, among others).
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
# The protocol hash belongs to the field profile (util/crypto.h,
# params/param_sets.h); no build option selects it.
if(DEFINED PROOFS_HASH384)
  message(FATAL_ERROR "PROOFS_HASH384 is not an option: each field profile "
    "fixes its protocol hash (SHA-256 narrow, SHA-384 wide). Remove it from "
    "the cache (cmake -U PROOFS_HASH384).")
endif()
include(CMake/proofs.cmake)
include(CMake/longfellow_tests.cmake)
enable_testing()
# Only the out-of-circuit path of the ring benchmarks uses this: the
# in-repo SHA3 is a reference implementation and would misrepresent the
# verifier's real hashing cost.
find_package(OpenSSL REQUIRED)
if (CMAKE_HOST_SYSTEM_NAME MATCHES "Darwin" AND NOT CMAKE_SYSTEM_NAME STREQUAL "iOS" AND NOT CMAKE_SYSTEM_NAME STREQUAL "Android")
  link_directories("/opt/homebrew/lib")
  include_directories("/opt/homebrew/include")
elseif (CMAKE_SYSTEM_NAME STREQUAL "iOS")
  include_directories("${CMAKE_CURRENT_SOURCE_DIR}/../deps-ios/include")
  link_directories("${CMAKE_CURRENT_SOURCE_DIR}/../deps-ios/lib")
  set(CMAKE_XCODE_GENERATE_SCHEME ON)
  set(CMAKE_XCODE_SCHEME_BUILD_CONFIGURATION "Release")
elseif (CMAKE_SYSTEM_NAME STREQUAL "Android")
  include_directories("${CMAKE_CURRENT_SOURCE_DIR}/../deps-android/include")
  link_directories("${CMAKE_CURRENT_SOURCE_DIR}/../deps-android/lib")
endif()


# add compiler flags for all known ISA's
string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" ARCHITECTURE)

if(ARCHITECTURE MATCHES "x86_64")
    set(ARCH_FLAGS -mpclmul)
elseif(ARCHITECTURE MATCHES "i386")
    set(ARCH_FLAGS -msse2 -mpclmul)
elseif(ARCHITECTURE MATCHES "aarch64")
    # A caller's -march/-mcpu in CMAKE_CXX_FLAGS selects the ISA (it must
    # include the crypto extension); the default -march would come after it
    # and override it.
    if(CMAKE_CXX_FLAGS MATCHES "-march=|-mcpu=")
        set(ARCH_FLAGS "")
    else()
        set(ARCH_FLAGS -march=armv8-a -march=armv8-a+crypto)
    endif()
elseif(ARCHITECTURE MATCHES "armv7l")
    set(ARCH_FLAGS -march=armv7-a -mfpu=neon-vfpv4 -mfloat-abi=hard)
elseif(ARCHITECTURE MATCHES "arm64")
    if (CMAKE_SYSTEM_NAME STREQUAL "iOS")
        set(ARCH_FLAGS -march=armv8-a -march=armv8-a+crypto)
    else()
        # Mac Arm
        set(ARCH_FLAGS -mcpu=apple-m1 -march=armv8-a+crypto)
    endif()
else()
    set(ARCH_FLAGS "")
endif()

if(ARCH_FLAGS)
    add_compile_options( "$<$<COMPILE_LANGUAGE:CXX>:${ARCH_FLAGS}>")
    message(STATUS "Compiler flags added for architecture ${ARCHITECTURE}: ${ARCH_FLAGS}")
else()
     message(STATUS "Architecture ${ARCHITECTURE} not recognized, no specific compiler flags added.")
endif()


include_directories(${proofs_SOURCE_DIR})

# The GordieHowe test switches (gordiehowe/compiler/test_switches.h): the
# prover's self-checks and the switches between two computations of the
# same value, which the tests set. This build compiles the tests, so it
# compiles them in; a build of the library without them has none.
option(GORDIEHOWE_TEST_SWITCHES "Compile in the GordieHowe test switches" ON)
if(GORDIEHOWE_TEST_SWITCHES)
  add_compile_definitions(GORDIEHOWE_TEST_SWITCHES=1)
endif()
# The diagnostic output (util/diagnostics.h): the profiler, the
# performance counters and the measurement lines the benchmark scripts
# parse, each off until a driver turns it on. OFF compiles them away; the
# benchmarks need them on.
option(PROOFS_DIAGNOSTICS "Compile in the diagnostic output" ON)
if(NOT PROOFS_DIAGNOSTICS)
  add_compile_definitions(PROOFS_DIAGNOSTICS=0)
endif()


# The unchanged Longfellow files have their own include root.
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib)
add_subdirectory(third_party/xkcp)
include_directories(${XKCP_INCLUDE_DIRS})
add_library(algebra OBJECT "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/algebra/nat.cc" "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/algebra/crt.cc")
add_library(ec OBJECT "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/ec/p256.cc")
add_library(util OBJECT "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/util/log.cc" "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/util/crypto.cc")
add_library(testing_main OBJECT "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/testing/test_main.cc")
# Every test binary reads its drivers' environment variables into the
# library's options (testing/env_options_testing.h); the bench executables
# take them as flags (bench/cli.h).
add_library(env_options_testing OBJECT testing/env_options_testing.cc)
add_library(sha3 OBJECT "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/circuits/tests/sha3/sha3_reference.cc" "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/circuits/tests/sha3/sha3_round_constants.cc" "${CMAKE_CURRENT_SOURCE_DIR}/circuits/tests/sha3/sha3_witness.cc")
add_library(flatsha OBJECT "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/circuits/sha/flatsha256_witness.cc" "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/circuits/sha/sha256_constants.cc")
add_library(ml_dsa OBJECT "${CMAKE_CURRENT_SOURCE_DIR}/../third_party/longfellow/lib/circuits/tests/pq/ml_dsa/ml_dsa_shared.cc" "${CMAKE_CURRENT_SOURCE_DIR}/circuits/tests/pq/ml_dsa/ml_dsa_44_examples.cc" "${CMAKE_CURRENT_SOURCE_DIR}/circuits/tests/pq/ml_dsa/ml_dsa_ref.cc")
target_link_libraries(util crypto zstd xkcp)
add_executable(report_bench bench/report_bench.cc)
set_target_properties(report_bench PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bench)
add_subdirectory(algebra)
add_subdirectory(arrays)
add_subdirectory(ligero)
add_subdirectory(merkle)
add_subdirectory(random)
add_subdirectory(sumcheck)
add_subdirectory(gf2k)
add_subdirectory(zk)
add_subdirectory(circuits/compiler)
add_subdirectory(circuits/logic)
add_subdirectory(circuits/tests/sha3)
add_subdirectory(util)
add_subdirectory(gordiehowe)
# Everything run_bench.sh builds, as one goal: `cmake --build --target t1
# t2 ...` under the Makefile generator builds its targets one at a time (the
# top-level Makefile is .NOTPARALLEL), so the script builds this instead.
add_custom_target(pq_bench_targets DEPENDS
  report_bench falcon_emulated_bench falcon_native_bench mldsa_native_bench
  mldsa_emulated_bench falcon_ring_bench mldsa_ring_bench keccak_compare_bench
  sha256_compare_bench mdoc_bench rsa_pkcs1_bench pq_mdoc_bench
  composite_bench)
add_subdirectory(tools)
# The aarch64 benchmark run's executables, as one goal: the flagship bench
# executables, report_bench, and the tests of the kernels with an aarch64
# path and of the flagship systems.
add_custom_target(rpi_bench_targets DEPENDS
  report_bench falcon_emulated_bench falcon_native_bench mldsa_native_bench
  mldsa_emulated_bench falcon_ring_bench mldsa_ring_bench)
add_custom_target(rpi_test_targets DEPENDS
  fields256_test fp_goldilocks_test gf2_128_test boolean_skip_test
  skip_gfni_test gordiehowe_ct_test
  mldsa_native_test mldsa_emulated_test falcon_native_test
  falcon_emulated_test mldsa_ring_test falcon_ring_test native_wide_test
  neon_kernels_test neon_kernels_scalar_test openssl_asm_test)
