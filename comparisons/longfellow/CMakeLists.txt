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

string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" LFB_ARCH)
# On aarch64, upstream adds -march=armv8-a+crypto to each of its targets'
# compile options, which follow CMAKE_CXX_FLAGS on the command line and so
# override a caller's -march (an -mcpu's architecture likewise).  When
# CMAKE_CXX_FLAGS selects the ISA (it must include the crypto extension),
# upstream's -march options are removed from its targets, here and not in
# the submodule, which stays at its pinned commit unmodified.
if(LFB_ARCH MATCHES "aarch64" AND CMAKE_CXX_FLAGS MATCHES "-march=|-mcpu=")
  function(lfb_drop_upstream_march dir)
    get_property(targets DIRECTORY ${dir} PROPERTY BUILDSYSTEM_TARGETS)
    foreach(t IN LISTS targets)
      get_property(opts TARGET ${t} PROPERTY COMPILE_OPTIONS)
      # The generator expression of upstream's ARCH_FLAGS list is stored as
      # one item per flag, each holding "-march=armv8-a"; both go.
      list(FILTER opts EXCLUDE REGEX "-march=armv8-a")
      set_property(TARGET ${t} PROPERTY COMPILE_OPTIONS "${opts}")
    endforeach()
    get_property(subdirs DIRECTORY ${dir} PROPERTY SUBDIRECTORIES)
    foreach(s IN LISTS subdirs)
      lfb_drop_upstream_march(${s})
    endforeach()
  endfunction()
  lfb_drop_upstream_march(${CMAKE_CURRENT_SOURCE_DIR}/upstream/lib)
  message(STATUS "aarch64: upstream's -march removed; CMAKE_CXX_FLAGS selects the ISA")
endif()

set(LFB_UPSTREAM_LIB ${CMAKE_CURRENT_SOURCE_DIR}/upstream/lib)
set(LFB_COMMON ${CMAKE_CURRENT_SOURCE_DIR}/common)

# Upstream adds its include root and ISA flags in its own directory scope;
# the baselines get the same.
include_directories(${LFB_UPSTREAM_LIB} ${LFB_COMMON})
add_compile_definitions(OPENSSL_SUPPRESS_DEPRECATED=1)
if(LFB_ARCH MATCHES "x86_64")
  add_compile_options("$<$<COMPILE_LANGUAGE:CXX>:-mpclmul>")
elseif(LFB_ARCH MATCHES "aarch64" AND NOT CMAKE_CXX_FLAGS MATCHES "-march=|-mcpu=")
  add_compile_options("$<$<COMPILE_LANGUAGE:CXX>:-march=armv8-a+crypto>")
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
