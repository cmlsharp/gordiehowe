# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# longfellow-baselines: upstream longfellow-zk (upstream/, a submodule) and
# the baselines built on its library (baselines/<name>/).
#
# Configure and build with common/build.sh, which enters the nix shell and
# passes the benchmark flags.
cmake_minimum_required(VERSION 3.16)
project(longfellow_baselines C CXX)
set(CMAKE_CXX_STANDARD 17)

# Upstream's library and its own tests, as upstream builds them.  Only the
# targets a baseline links are built (common/build.sh names them).
add_subdirectory(upstream/lib upstream)

set(LFB_UPSTREAM_LIB ${CMAKE_CURRENT_SOURCE_DIR}/upstream/lib)
set(LFB_COMMON ${CMAKE_CURRENT_SOURCE_DIR}/common)

# Upstream adds its include root and ISA flags in its own directory scope;
# the baselines get the same.
include_directories(${LFB_UPSTREAM_LIB} ${LFB_COMMON})
add_compile_definitions(OPENSSL_SUPPRESS_DEPRECATED=1)
string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" LFB_ARCH)
if(LFB_ARCH MATCHES "x86_64")
  add_compile_options("$<$<COMPILE_LANGUAGE:CXX>:-mpclmul>")
endif()

# A benchmark driver: one executable that speaks the worker protocol of
# common/bench_worker.h, linked like upstream's tests.
macro(lfb_add_driver NAME)
  add_executable(${NAME} ${ARGN})
  target_link_libraries(${NAME} ec algebra util crypto zstd pthread)
endmacro()

# baselines/common-wide is not a baseline: the wide hash domain the wide
# baselines share (lfb_use_common_wide).  It is always configured, first.
add_subdirectory(baselines/common-wide)

file(GLOB LFB_BASELINES LIST_DIRECTORIES true
     ${CMAKE_CURRENT_SOURCE_DIR}/baselines/*)
# LFB_ONLY (a ;-list of baseline directory names) configures only those, so
# that one baseline's build does not depend on another's state.
foreach(dir ${LFB_BASELINES})
  get_filename_component(name ${dir} NAME)
  if(name STREQUAL "common-wide")
    continue()
  endif()
  if(DEFINED LFB_ONLY AND NOT LFB_ONLY STREQUAL "" AND
     NOT name IN_LIST LFB_ONLY)
    continue()
  endif()
  if(EXISTS ${dir}/CMakeLists.txt)
    add_subdirectory(${dir})
  endif()
endforeach()

# LFB_BUILD_TARGETS (a ;-list, set by common/build.sh): one target that
# depends on all of them, so that a single build goal compiles them in
# parallel (the Makefile generator runs several --target goals one at a time).
if(DEFINED LFB_BUILD_TARGETS AND NOT LFB_BUILD_TARGETS STREQUAL "")
  add_custom_target(lfb_selected DEPENDS ${LFB_BUILD_TARGETS})
endif()
