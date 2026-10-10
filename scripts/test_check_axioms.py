#!/usr/bin/env python3
"""Regression checks for the CI trust-audit parser."""
import unittest
from check_axioms import validate

class AxiomAuditTests(unittest.TestCase):
    def test_single_line(self):
        self.assertEqual(validate("'HodgeProofHP.final' depends on axioms: [propext, Classical.choice, Quot.sound]", ["HodgeProofHP.final"]), 1)

    def test_multiline(self):
        self.assertEqual(validate("info: 'HodgeProofHP.final' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"), 1)

    def test_no_report(self):
        with self.assertRaises(ValueError):
            validate("Build completed successfully")

    def test_unexpected_axioms(self):
        for axiom in ("sorryAx", "HodgeProofHP.customAssumption", "Classical.choiceX"):
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                validate(f"'final' depends on axioms: [propext,\n {axiom},\n Quot.sound]")

    def test_incomplete_report(self):
        with self.assertRaises(ValueError):
            validate("'good' depends on axioms: [propext]\n'bad' depends on axioms: [Classical.choice")

    def test_missing_final_theorem(self):
        with self.assertRaises(ValueError):
            validate("'other' depends on axioms: [propext]", ["HodgeProofHP.final"])

if __name__ == "__main__":
    unittest.main()
