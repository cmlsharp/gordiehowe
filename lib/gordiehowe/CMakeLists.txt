# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# GordieHowe: the phased constraint-system core.
# Header-only; the tests link the default proofs test dependencies and the
# explicit instantiations of instances.h.

# ccache, when the build host has it, for the GordieHowe targets; the
# sloppiness lets it cache translation units that use the precompiled
# header.
find_program(GORDIEHOWE_CCACHE ccache)
if(GORDIEHOWE_CCACHE)
  set(CMAKE_CXX_COMPILER_LAUNCHER
      ${CMAKE_COMMAND} -E env CCACHE_SLOPPINESS=pch_defines,time_macros
      ${GORDIEHOWE_CCACHE})
endif()

# The compile cache's compiler digest (compiler/compile_cache.h): SHA-256 of
# the sources that decide a compiled system's circuits and stored decisions,
# the GordieHowe core, compiler and operators, the library functions and
# the examples (whose circuit closures' bodies no description holds),
# Longfellow's circuit compiler, Logic, sumcheck circuits and fields, and
# the Ligero and ZK layouts the tableau search and the provisional tableau
# read.
file(GLOB GORDIEHOWE_COMPILER_SOURCES CONFIGURE_DEPENDS
     ${CMAKE_CURRENT_SOURCE_DIR}/*.h
     ${CMAKE_CURRENT_SOURCE_DIR}/compiler/*.h
     ${CMAKE_CURRENT_SOURCE_DIR}/ops/*.h
     ${CMAKE_CURRENT_SOURCE_DIR}/lib/*.h
     ${CMAKE_CURRENT_SOURCE_DIR}/examples/*.h
     ${CMAKE_CURRENT_SOURCE_DIR}/examples/*/*.h
     ${CMAKE_SOURCE_DIR}/circuits/compiler/*.h
     ${CMAKE_SOURCE_DIR}/circuits/logic/*.h
     ${CMAKE_SOURCE_DIR}/sumcheck/*.h
     ${CMAKE_SOURCE_DIR}/algebra/*.h
     ${CMAKE_SOURCE_DIR}/gf2k/*.h
     ${CMAKE_SOURCE_DIR}/ligero/*.h
     ${CMAKE_SOURCE_DIR}/zk/*.h)
list(FILTER GORDIEHOWE_COMPILER_SOURCES EXCLUDE REGEX "_(test|fixture)\\.h$")
set(GORDIEHOWE_COMPILER_DIGEST ${CMAKE_CURRENT_BINARY_DIR}/compiler_digest.cc)
add_custom_command(
  OUTPUT ${GORDIEHOWE_COMPILER_DIGEST}
  COMMAND ${CMAKE_COMMAND} -DROOT=${CMAKE_SOURCE_DIR}
          -DOUT=${GORDIEHOWE_COMPILER_DIGEST}
          "-DSOURCES=${GORDIEHOWE_COMPILER_SOURCES}"
          -P ${CMAKE_CURRENT_SOURCE_DIR}/compiler_digest.cmake
  DEPENDS ${GORDIEHOWE_COMPILER_SOURCES}
          ${CMAKE_CURRENT_SOURCE_DIR}/compiler_digest.cmake
  VERBATIM)
add_library(gordiehowe_compiler_digest STATIC ${GORDIEHOWE_COMPILER_DIGEST})

# One precompiled header of the common GordieHowe, field and gtest headers,
# built once by gordiehowe_pch and reused by every GordieHowe target
# (gordiehowe_use_pch). The targets share gordiehowe_pch's compile
# definitions, which a reused precompiled header requires.
add_library(gordiehowe_pch STATIC pch.cc)
macro(gordiehowe_use_pch TARGET)
  target_link_libraries(${TARGET} gtest benchmark::benchmark
                        gordiehowe_compiler_digest)
  if(NOT "${TARGET}" STREQUAL "gordiehowe_pch")
    target_precompile_headers(${TARGET} REUSE_FROM gordiehowe_pch)
  endif()
endmacro()
gordiehowe_use_pch(gordiehowe_pch)
target_precompile_headers(gordiehowe_pch PRIVATE
                          <gordiehowe/instances.h>
                          <algebra/reed_solomon_fp.h>
                          <params/param_sets.h>
                          <random/secure_random_engine.h>
                          <gtest/gtest.h>)
if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  # Without timestamps ccache can hash the precompiled header.
  target_compile_options(gordiehowe_pch PRIVATE -Xclang -fno-pch-timestamp)
endif()

# The compile, lowering and domain paths of the field sets in instances.h:
# one library per field set, gordiehowe_instances_<set>, of one translation
# unit per domain (instantiations/<set>__<field>.cc), so they compile once
# and in parallel, and a test builds only the sets it uses.
#
# The units are written by hand, one per entry DOM(F, RSF, S) of
# instances.h's GORDIEHOWE_INSTANCES: <set>__<field>.cc defines that
# domain's GORDIEHOWE_LOWERING_INSTANCE and GORDIEHOWE_DOMAIN_INSTANCE with
# an empty first argument (an explicit instantiation definition), and the
# unit of the set's first domain also its GORDIEHOWE_SYSTEM_INSTANCE.
# instances.h expands the same list with `extern` (the declarations), so
# every other translation unit that includes it compiles none of these
# bodies. The glob below takes a set's units by their <set>__ prefix. A new
# field set is an entry in GORDIEHOWE_INSTANCES, a unit per domain, and its
# name here; a set or domain left out is instantiated implicitly where it is
# used, which costs only build time. examples/CMakeLists.txt does the same
# for the example systems' builders (gordiehowe_example_<system>).
set(GORDIEHOWE_INSTANCE_SETS
    fp14_9 mod rom_emu qrom_emu rom_ml_dsa qrom_ml_dsa
    rom_falcon_native qrom_falcon_native
    gold4_gf128_sha256 gold4_gf128 gold4_gf256 gold4 gold2_sha256 gf128_3
    gf128_sha256
    gf128 gf256 falcon20 p256 mdoc rom_fp128 rom_composite
    qrom_composite qrom_ecdsa)
foreach(SET ${GORDIEHOWE_INSTANCE_SETS})
  file(GLOB SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/instantiations/${SET}__*.cc)
  add_library(gordiehowe_instances_${SET} STATIC ${SOURCES})
  gordiehowe_use_pch(gordiehowe_instances_${SET})
endforeach()

# The prover's test-only self-checks, on in every GordieHowe test but the
# DISABLED_ ones (compiler/test_switches.h); an object library, so
# that its listener's registration links into each test binary.
add_library(gordiehowe_prover_check_testing OBJECT prover_check_testing.cc)
target_link_libraries(gordiehowe_prover_check_testing gtest)

# The instance libraries of a GordieHowe target: the field sets after
# SETS (gordiehowe_instances_<set>) and the example systems after EXAMPLES
# (gordiehowe_example_<system>, examples/CMakeLists.txt). A set or system
# the target uses but does not list is a link error; a field set outside
# instances.h compiles in the target.
# The systems come first: their builders reference the sets' instances.
macro(gordiehowe_link_instances PROG)
  foreach(SYS ${GH_EXAMPLES})
    target_link_libraries(${PROG} gordiehowe_example_${SYS})
  endforeach()
  foreach(SET ${GH_SETS})
    target_link_libraries(${PROG} gordiehowe_instances_${SET})
  endforeach()
endmacro()

# A GordieHowe test: proofs_add_test(PROG sources...) with the instance
# libraries after SETS and EXAMPLES (gordiehowe_link_instances). Its tests
# run with the prover's self-checks on.
macro(gordiehowe_add_test PROG)
  cmake_parse_arguments(GH "" "" "SETS;EXAMPLES" ${ARGN})
  proofs_add_test(${PROG} ${GH_UNPARSED_ARGUMENTS})
  gordiehowe_use_pch(${PROG})
  target_link_libraries(${PROG} gordiehowe_prover_check_testing)
  gordiehowe_link_instances(${PROG})
endmacro()

# A GordieHowe bench executable, built into the build tree's bench/ beside
# report_bench: PROG.cc and the sources after it, with the instance
# libraries after SETS and EXAMPLES. Its main is its command line
# (bench/cli.h); it links no test main and runs without the prover's
# self-checks.
macro(gordiehowe_add_bench PROG)
  cmake_parse_arguments(GH "" "" "SETS;EXAMPLES" ${ARGN})
  add_executable(${PROG} ${PROG}.cc ${GH_UNPARSED_ARGUMENTS})
  target_link_libraries(${PROG} ec algebra util pthread)
  gordiehowe_use_pch(${PROG})
  gordiehowe_link_instances(${PROG})
  set_target_properties(${PROG} PROPERTIES RUNTIME_OUTPUT_DIRECTORY
                        ${CMAKE_BINARY_DIR}/bench)
endmacro()

# The core tests (tests/), the application systems (examples/) and the
# hash comparison harnesses (bench/hash_comparisons/).
add_subdirectory(tests)
add_subdirectory(examples)
add_subdirectory(bench/hash_comparisons)
add_subdirectory(heldout)
