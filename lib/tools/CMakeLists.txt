# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Tools that print paper figures from the library's own computations.
# masktest_rows: the rows of tab:mask-test-room from the Ligero choice
# (gordiehowe/compiler/ligero_choice.h).
add_executable(masktest_rows masktest_rows.cc)
target_link_libraries(masktest_rows util)
set_target_properties(masktest_rows PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/tools)
