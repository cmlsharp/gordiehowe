# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Longfellow's own unit tests, kept byte-identical under
# third_party/longfellow/lib (scripts/check_vendor.py): longfellow_add_tests
# builds each PROG from third_party/longfellow/lib/<module>/PROG.cc, where
# <module> is the calling directory's path under lib/, and registers it as
# proofs_add_test does (same target and test names, same libraries).
macro(longfellow_add_tests)
  file(RELATIVE_PATH LONGFELLOW_MODULE ${proofs_SOURCE_DIR}
       ${CMAKE_CURRENT_SOURCE_DIR})
  foreach(PROG ${ARGN})
    add_executable(${PROG}
      ${proofs_SOURCE_DIR}/../third_party/longfellow/lib/${LONGFELLOW_MODULE}/${PROG}.cc)
    target_link_libraries(${PROG} ec)
    target_link_libraries(${PROG} algebra)
    target_link_libraries(${PROG} util)
    proofs_add_testing_libraries(${PROG})
  endforeach()
endmacro()
