# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# The vendored XKCP subset (README.md): cSHAKE256 of SP 800-185 over one
# Keccak-p[1600] implementation, chosen at compile time in
# config/xkcp-target.h from the compiler's predefined macros.

enable_language(ASM)

set(XKCP_UP ${CMAKE_CURRENT_SOURCE_DIR}/upstream/lib)
# xkcp_objects for libraries that bundle object files (mdoc_static), xkcp
# for everyone else. Each select/*.S wrapper assembles its upstream file only
# when xkcp-target.h picks it, from the target compiler's macros, and is
# empty otherwise: the x86-64 AVX2 assembler is assembled on x86-64 only,
# in native and cross builds alike.
add_library(xkcp_objects OBJECT
  select/keccakp1600.c
  select/keccakp1600-avx2.S
  select/keccakp1600-armv7a-neon.S
  ${XKCP_UP}/high/Keccak/KeccakSponge.c
  ${XKCP_UP}/high/Keccak/SP800-185/SP800-185.c)
set(XKCP_INCLUDE_DIRS
  ${CMAKE_CURRENT_SOURCE_DIR}/config
  ${XKCP_UP}/common
  ${XKCP_UP}/low/common
  ${XKCP_UP}/low/KeccakP-1600/common
  ${XKCP_UP}/low/KeccakP-1600/plain-64bits
  ${XKCP_UP}/low/KeccakP-1600/AVX2
  ${XKCP_UP}/high/common
  ${XKCP_UP}/high/Keccak
  ${XKCP_UP}/high/Keccak/SP800-185)
target_include_directories(xkcp_objects PUBLIC ${XKCP_INCLUDE_DIRS})
# random/transcript.h includes SP800-185.h; every target may include it.
set(XKCP_INCLUDE_DIRS ${XKCP_INCLUDE_DIRS} PARENT_SCOPE)
# The C and assembler sources see the C++ flags (-march=native in the
# benchmark builds) and the architecture flags, so that the implementation
# xkcp-target.h picks here is the one the C++ side's headers pick.
separate_arguments(XKCP_CXX_FLAGS UNIX_COMMAND "${CMAKE_CXX_FLAGS}")
target_compile_options(xkcp_objects PRIVATE ${XKCP_CXX_FLAGS} ${ARCH_FLAGS})
set_target_properties(xkcp_objects PROPERTIES POSITION_INDEPENDENT_CODE ON)
add_library(xkcp STATIC $<TARGET_OBJECTS:xkcp_objects>)
target_include_directories(xkcp PUBLIC ${XKCP_INCLUDE_DIRS})
