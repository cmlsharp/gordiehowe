# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# The wide profile's hash domain, shared by the wide baselines: GF(2^256),
# the 256-bit MAC's multiplication, SHA-384 and the fork's SHA-384
# transcript (cSHAKE256 challenge stream from the vendored XKCP subset).
#
# include/ holds new headers and shadows of upstream headers.  A wide target
# must put include/ BEFORE upstream/lib, and every one of its translation
# units must see the shadows; lfb_use_common_wide(TARGET) does both the
# include order and the XKCP link.  Upstream's object libraries a wide target
# links (ec, algebra, util, flatsha, sha3, ml_dsa) include none of the
# shadowed headers.
add_subdirectory(third_party/xkcp)

set(LFB_COMMON_WIDE_INCLUDE ${CMAKE_CURRENT_SOURCE_DIR}/include
    CACHE INTERNAL "")
set(LFB_XKCP_INCLUDE_DIRS ${XKCP_INCLUDE_DIRS} CACHE INTERNAL "")

macro(lfb_use_common_wide TARGET)
  target_include_directories(${TARGET} BEFORE PRIVATE
                             ${LFB_COMMON_WIDE_INCLUDE})
  target_include_directories(${TARGET} PRIVATE ${LFB_XKCP_INCLUDE_DIRS})
  target_link_libraries(${TARGET} xkcp)
  target_compile_definitions(${TARGET} PRIVATE LFB_WIDE_HASH_DOMAIN=1)
endmacro()

lfb_add_driver(wide_selftest wide_selftest.cc)
lfb_use_common_wide(wide_selftest)
