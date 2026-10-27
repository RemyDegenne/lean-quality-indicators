import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import cfsg_pilot


class SourceTests(unittest.TestCase):
    def test_both_tau_ceti_and_mathlib_pins_and_lean_core_are_available(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); source = root / 'source'; source.mkdir()
            toolchain = 'leanprover/lean4:v4.35.0-rc3'
            (source / 'lean-toolchain').write_text(toolchain)
            core = root / '.elan/toolchains/leanprover--lean4---v4.35.0-rc3/src/lean'
            core.mkdir(parents=True)
            packages = [{'name': name, 'rev': name+'-revision'} for name in ['mathlib', 'TauCeti']]
            with patch.object(cfsg_pilot, 'ROOT', root), patch.object(cfsg_pilot, 'SOURCE', source), \
                 patch.object(cfsg_pilot, 'dependencies', return_value=packages), \
                 patch.object(cfsg_pilot.Path, 'home', return_value=root), \
                 patch.object(cfsg_pilot.subprocess, 'check_output', side_effect=[p['rev'] for p in packages]):
                cwd, dirs = cfsg_pilot.source_dirs({'dir': 'axiom-cfsg'})
            self.assertEqual(cwd, source)
            self.assertEqual(len(dirs), 3)
            self.assertTrue(any(k.startswith('TauCeti ') for k in dirs))
            self.assertTrue(any(k.startswith('mathlib ') for k in dirs))
            self.assertIn(core, dirs.values())

    def test_changed_dependency_is_rejected(self):
        with patch.object(cfsg_pilot, 'dependencies', return_value=[{'name': 'mathlib', 'rev': 'expected'}]), \
             patch.object(cfsg_pilot.subprocess, 'check_output', return_value='different'):
            with self.assertRaisesRegex(ValueError, 'changed pinned dependency'):
                cfsg_pilot.source_dirs({'dir': 'axiom-cfsg'})


if __name__ == '__main__':
    unittest.main()
