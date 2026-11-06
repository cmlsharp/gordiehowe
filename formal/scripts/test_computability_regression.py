#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Check the gate's baseline regression decisions independently of CostLint types."""

import unittest

from computability_regression import compare, read_inventory


class ComputabilityRegressionTests(unittest.TestCase):
    def test_unclassified_definition_still_strict(self):
        result = compare({"unclassified": (False, True)}, {"unclassified": (True, False)})
        self.assertEqual(result["became_noncomputable"], ["unclassified"])
        self.assertEqual(result["lost_ir"], ["unclassified"])

    def test_each_regression_flag_is_independent(self):
        result = compare(
            {"flag": (False, False), "code": (True, True)},
            {"flag": (True, False), "code": (True, False)},
        )
        self.assertEqual(result["became_noncomputable"], ["flag"])
        self.assertEqual(result["lost_ir"], ["code"])

    def test_improvement_and_removed_names_are_reported(self):
        result = compare(
            {"improved": (True, False), "removed": (False, True)},
            {"improved": (False, True), "new": (True, False)},
        )
        self.assertEqual(result["became_noncomputable"], [])
        self.assertEqual(result["lost_ir"], [])
        self.assertEqual(result["added"], ["new"])
        self.assertEqual(result["removed"], ["removed"])

    def test_malformed_or_empty_input_fails(self):
        header = "name\tnoncomputable\thas_ir\n"
        for body in ("", "x\tfalse\n", "x\tmaybe\ttrue\n", "x\tfalse\ttrue\nx\tfalse\ttrue\n"):
            with self.subTest(body=body), self.assertRaises(ValueError):
                read_inventory(header + body)
        with self.assertRaises(ValueError):
            compare({"a": (False, True)}, {"b": (False, True)})


if __name__ == "__main__":
    unittest.main()
