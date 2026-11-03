"""Compression ratio: code-only text, and that repetition compresses."""
import os
import unittest

import compression as cz


class CompressionTests(unittest.TestCase):
    def test_code_only(self):
        text = ('/-! Module doc -/\n\ntheorem foo : True := by  -- comment\n  trivial\n'
                '/-- doc -/\ndef s := "a string"\n')
        self.assertEqual(cz.code_only(text), "theorem foo : True := by\n  trivial\ndef s :=\n")

    def test_counted_lines(self):
        long = "  exact foo_bar_baz (by simpa using h) hx hy hz"
        code = f"import Mathlib.Algebra.Group.Defs.Basic.LongName.X\n{long}\nshort\n{long}\n"
        self.assertEqual(len(cz.line_hashes(code)), 2)
        self.assertEqual(cz.line_hashes(long), cz.line_hashes(long.strip()))

    def test_repetition_compresses(self):
        block = os.urandom(4000)
        self.assertLess(cz.csize(block * 10), 1.1 * cz.csize(block))
        self.assertEqual(cz.ratio(10, 4), 2.5)


if __name__ == "__main__":
    unittest.main()
