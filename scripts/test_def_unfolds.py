"""Explicit unfoldings of definitions: classification, name resolution, aggregation."""
import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import def_unfolds as du
import leanscan as ls


def classify_all(text: str, name: str) -> list:
    """Category of each occurrence of `name` in `text`."""
    masked, _ = ls.mask(text)
    out, i = [], masked.find(name)
    while i >= 0:
        out.append(du.classify(masked, i, i + len(name)))
        i = masked.find(name, i + len(name))
    return out


class ClassifyTests(unittest.TestCase):
    def test_unfold_family(self):
        self.assertEqual(classify_all("  unfold foo bar at h", "bar"), ["unfold"])
        self.assertEqual(classify_all("  · delta foo; simp", "foo"), ["unfold"])
        self.assertEqual(classify_all("unseal foo in\n", "foo"), ["unfold"])
        self.assertEqual(classify_all("  exact foo", "foo"), [None])

    def test_operator_after_delta_is_not_an_unfolding(self):
        self.assertEqual(classify_all("  if delta * size r < x then", "size"), [None])

    def test_simp_and_rw_lists(self):
        self.assertEqual(classify_all("  simp only [foo, ← bar] at h", "bar"), ["simp"])
        self.assertEqual(classify_all("  simp (config := {zeta := false}) only [foo]", "foo"),
                         ["simp"])
        self.assertEqual(classify_all("  simp +arith [foo]", "foo"), ["simp"])
        self.assertEqual(classify_all("  grind [foo]", "foo"), ["simp"])
        self.assertEqual(classify_all("  nth_rw 2 [foo]", "foo"), ["rw"])
        self.assertEqual(classify_all("  rw [a, b,\n    foo] at h", "foo"), ["rw"])
        self.assertEqual(classify_all("  simp_rw [foo]", "foo"), ["rw"])

    def test_list_items_that_are_not_unfoldings(self):
        self.assertEqual(classify_all("  simp [foo x]", "foo"), [None])
        self.assertEqual(classify_all("  simp [-foo]", "foo"), [None])
        self.assertEqual(classify_all("  rw [bar (foo)]", "foo"), [None])
        self.assertEqual(classify_all("  exact baz [foo, bar]", "foo"), [None])
        self.assertEqual(classify_all("  simp [bar] -- foo", "foo"), [])

    def test_attribute_commands(self):
        self.assertEqual(classify_all("attribute [local simp] foo bar\n", "bar"), ["simp"])
        self.assertEqual(classify_all("attribute [-simp] foo\n", "foo"), [None])
        self.assertEqual(classify_all("attribute [local semireducible] foo\n", "foo"),
                         ["unfold"])

    def test_scope(self):
        self.assertEqual(du.scope_of("A/B/C.lean", "A/B/C.lean"), "file")
        self.assertEqual(du.scope_of("A/B/C.lean", "A/B/D/E.lean"), "dir")
        self.assertEqual(du.scope_of("A/B/C.lean", "A/F.lean"), "outside")


class LocalNameTests(unittest.TestCase):
    def test_signature_binders_and_types(self):
        locs = du.local_names("", "(x y : Foo.Bar n) {s : Set α} [inst : Group G]")
        self.assertEqual(locs["x"], "Foo.Bar")
        self.assertEqual(locs["s"], "Set")
        self.assertIn("inst", locs)

    def test_type_ascription_is_not_a_binder(self):
        self.assertNotIn("ofList", du.local_names("p ∈ (ofList l hl : Multiset ℕ)", ""))

    def test_tactic_and_lambda_binders(self):
        locs = du.local_names("by\n  intro a b\n  obtain ⟨c, hc⟩ := h\n"
                              "  exact fun ⟨d, e⟩ => ∀ f ∈ s, g f\n", "")
        for n in "a b c hc d e f".split():
            self.assertIn(n, locs)
        self.assertNotIn("s", locs)

    def test_postfix_notation(self):
        masked = "theorem t : R[X] = x := by rw[X]"
        i = masked.index("X")
        self.assertTrue(du._in_notation(masked, i, i + 1))
        j = masked.rindex("X")
        self.assertFalse(du._in_notation(masked, j, j + 1))


LIB_FILES = {
    "Lib/A/Defs.lean": """namespace Foo
def bar (n : Nat) : Nat := n + 1
protected def baz : Nat := 0
structure S where
  val : Nat
def S.double (s : S) : Nat := 2 * s.val
structure T where
  n : Nat
def T.double (t : T) : Nat := t.n + t.n
theorem bar_succ (n : Nat) : bar n = n + 1 := by unfold bar; rfl
end Foo
""",
    "Lib/A/Use.lean": """import Lib.A.Defs
open Foo in
theorem t1 (n : Nat) : Foo.bar n = n + 1 := by simp [Foo.bar]
namespace Foo
theorem t2 (bar : Nat) : bar = bar := rfl
theorem t3 (n : Nat) : bar n = n + 1 := by rw [bar]
theorem t4 (s : S) : s.double = 2 * s.val := by simp [S.double]
end Foo
""",
    "Lib/B/Far.lean": """import Lib.A.Defs
theorem t5 (n : Nat) : Foo.bar n = n + 1 := by rw [Foo.bar.eq_def]
namespace Other
theorem _root_.Foo.t6 : Foo.baz = 0 := by unfold Foo.baz; rfl
theorem t7 (baz : Nat) : baz = baz := rfl
end Other
""",
    # Same short name as `Foo.bar`, in a file that nothing imports.
    "Lib/B/Unrelated.lean": """namespace Qux
def bar (n : Nat) : Nat := n
end Qux
""",
    "Lib/B/Both.lean": """import Lib.A.Defs
open Foo Qux
theorem t8 (n : Nat) : bar n = n + 1 := by simp [bar]
""",
}


class SourceBackendTests(unittest.TestCase):
    def run_lib(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for rel, text in LIB_FILES.items():
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                (root / rel).write_text(text)
            with contextlib.redirect_stderr(io.StringIO()):
                meta, rows, unf = du.run_source(root, ["Lib"], [], [], 2)
        return {r["name"]: r for r in rows}, unf

    def test_uses_and_unfoldings_by_scope(self):
        rows, unf = self.run_lib()
        bar = rows["Foo.bar"]
        # Own file: `unfold bar` and the statement of bar_succ.
        self.assertEqual(bar["unfolds"]["file"]["unfold"], 1)
        self.assertEqual(bar["uses"]["file"], 2)
        # Rest of the directory: t1 (statement, simp) and t3 (statement, rw); the local
        # `bar` of t2 is not a use.
        self.assertEqual(bar["uses"]["dir"], 4)
        self.assertEqual(bar["unfolds"]["dir"]["simp"], 1)
        self.assertEqual(bar["unfolds"]["dir"]["rw"], 1)
        # Elsewhere: t5's statement and its equation lemma, and t8 (statement, simp), where
        # `Qux.bar` is not imported and so does not compete.
        self.assertEqual(bar["uses"]["outside"], 4)
        self.assertEqual(bar["unfolds"]["outside"]["eq_def"], 1)
        self.assertEqual(bar["unfolds"]["outside"]["simp"], 1)
        self.assertEqual(bar["unfolding_files"], {"dir": 1, "outside": 2})
        self.assertEqual(sum(rows["Qux.bar"]["uses"].values()), 0)

    def test_field_notation_is_a_use_not_an_unfolding(self):
        rows, _ = self.run_lib()
        # `double` names two definitions: the binder type `S` of `s` picks `S.double`.
        double = rows["Foo.S.double"]
        self.assertEqual(double["uses"]["dir"], 2)
        self.assertEqual(double["unfolds"]["dir"]["simp"], 1)
        self.assertEqual(sum(rows["Foo.T.double"]["uses"].values()), 0)

    def test_protected_and_root_names(self):
        rows, _ = self.run_lib()
        baz = rows["Foo.baz"]
        # `Foo.baz` is unfolded in Far.lean; the atomic local `baz` of t7 is not a use.
        self.assertEqual(baz["uses"]["outside"], 2)
        self.assertEqual(baz["unfolds"]["outside"]["unfold"], 1)


    def test_flt_scoping_commands(self):
        files = {
            "Lib/Defs.lean": "namespace Foo\ndef bar (n : Nat) : Nat := n + 1\nend Foo\n",
            "Lib/Use.lean": """import Lib.Defs
namespace W
p2m_export "Foo" "bar"
theorem t (n : Nat) : bar n = n + 1 := by unfold bar; rfl
end W
p2m_open "Foo~baz"
theorem u (n : Nat) : bar n = n + 1 := by simp [bar]
""",
        }
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for rel, text in files.items():
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                (root / rel).write_text(text)
            with contextlib.redirect_stderr(io.StringIO()):
                _, rows, _ = du.run_source(root, ["Lib"], [], [], 2,
                                           commands=["p2m_open", "p2m_export"])
        bar = {r["name"]: r for r in rows}["Foo.bar"]
        self.assertEqual(bar["uses"]["dir"], 4)
        self.assertEqual(bar["unfolds"]["dir"]["unfold"], 1)
        self.assertEqual(bar["unfolds"]["dir"]["simp"], 1)


if __name__ == "__main__":
    unittest.main()
