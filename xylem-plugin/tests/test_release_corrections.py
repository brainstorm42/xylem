#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Cross-surface mathematics and converter/freshness contract regressions.

Run with the declared Python environment; Lean-gate outcome tests below are
controlled unit regressions, not a claim of newly checking Lean output.
"""
import contextlib
from fractions import Fraction
import hashlib
import io
import json
import re
from pathlib import Path
import sqlite3
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'canonical'), str(ROOT/'canonical/xylem')]
from brickconverter import cli
from brickconverter.ir import Lit
from xylem.input_state import snapshot, current_warning


def read(path):
    return json.loads(path.read_text())


def invoke(args):
    stdout, stderr = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        code = cli.main(args)
    return code, json.loads(stdout.getvalue()) if stdout.getvalue() else None, stderr.getvalue()


class MathematicalSurfaces(unittest.TestCase):
    def test_coordinate_images_and_infinite_family(self):
        base = ROOT/'examples/compact-bounds'
        packet = read(base/'explanation-hS.json')
        illustration = packet['example']['structured_illustration']
        intervals = illustration['K_coordinate_intervals']
        self.assertEqual(illustration['index_count'], len(intervals))
        self.assertEqual(illustration['S_intervals'], intervals)
        self.assertEqual(intervals, [[1,2],[3,4]])
        # Each projection contains its whole interval: choose the other
        # coordinate's lower endpoint. Conversely every projected value lies
        # in one of these intervals. Neither image is a finite point set.
        for i, (lo, hi) in enumerate(intervals):
            for t in (Fraction(lo), Fraction(hi), Fraction(lo+hi,2)):
                x = [Fraction(a) for a,b in intervals]; x[i] = t
                self.assertTrue(all(a <= y <= b for y,(a,b) in zip(x,intervals)))
                self.assertEqual(x[i], t)
        # The injection n -> 1+1/(n+1), n>=1, gives distinct values of S:
        # reciprocal equality implies equal positive denominators. Exercise
        # many rational witnesses exactly, rather than using float rounding.
        values = [1+Fraction(1,n+1) for n in range(1,1001)]
        self.assertEqual(len(set(values)),len(values))
        self.assertTrue(all(1<t<=2 and (t,3)[0]==t for t in values))
        self.assertEqual(illustration['S_cardinality'],'infinite')
        for path in (base/'explanation-hS.md', ROOT/'TECHNICAL-REPORT.md'):
            text=path.read_text()
            self.assertIn('[1,2]',text); self.assertIn('[3,4]',text)
            self.assertIn('infinite',text)
        self.assertNotIn('finite coordinate-value set',json.dumps(packet))

    def test_retained_context_and_source_argument_roles(self):
        base=ROOT/'examples/compact-bounds'
        record=read(base/'component-record.json'); packet=read(base/'explanation-hS.json')
        decl=read(ROOT/'capture/declarations.json')['declarations'][0]
        source=(base/record['components'][0]['source']['path']).read_text()
        self.assertEqual(hashlib.sha256(source.encode()).hexdigest(),record['components'][0]['source']['sha256'])
        self.assertEqual(packet['parent_statement']['signature'],decl['signature'])
        self.assertEqual([(b['index'],b['name'],b['binder_info'],b['type']) for b in packet['parent_statement']['binders']], [(b['idx'],b['name'],b['binderInfo'],b['type']) for b in decl['binders']])
        types=[b['type'] for b in decl['binders']]
        self.assertEqual(types,['Type uIota','Finite ι','Set (ι → ℝ)','IsCompact K','∀ x ∈ K, ∀ (i : ι), 0 < x i'])
        for component in record['components']:
            self.assertEqual(packet['assumptions'][component['boundary']+'_interface'],component['interface_context'])
            self.assertIn('IsCompact K → (∀ x ∈ K, ∀ (i : ι), 0 < x i) →',component['recorded_formal_interface'])
            self.assertEqual(component['assumption_minimization'],'not performed')
        hS=source.split('have hS :')[1].split('have hSpos :')[0]
        hSpos=source.split('have hSpos :')[1].split('obtain ⟨a,')[0]
        self.assertIn('isCompact_iUnion',hS); self.assertIn('hK.image',hS); self.assertNotIn('hpos',hS)
        self.assertIn('Set.mem_iUnion.mp',hSpos); self.assertIn('hpos x hx i',hSpos); self.assertNotIn('hK',hSpos)
        used=packet['assumptions']['source_argument_used']
        self.assertTrue(any('hK' in a for a in used['hS'])); self.assertFalse(any('hpos' in a for a in used['hS']))
        self.assertTrue(any('hpos' in a for a in used['hSpos'])); self.assertFalse(any('hK' in a for a in used['hSpos']))

    def test_displayed_helper_interfaces_match_records(self):
        record=read(ROOT/'examples/compact-bounds/component-record.json')
        expected={c['boundary']:c['recorded_formal_interface'] for c in record['components']}
        for path in (ROOT/'examples/compact-bounds/explanation-hS.md', ROOT/'TECHNICAL-REPORT.md'):
            blocks=re.findall(r'```text\n(.*?)\n```',path.read_text(),re.DOTALL)
            block=next(b for b in blocks if 'hS:' in b and 'hSpos:' in b)
            for boundary, following in [('hS','hSpos:'),('hSpos',None)]:
                displayed=block.split(boundary+':',1)[1]
                if following:displayed=displayed.split(following,1)[0]
                self.assertEqual(' '.join(displayed.split()),' '.join(expected[boundary].split()),
                                 f'{path.name}: {boundary} syntax differs from the recorded interface')

    def test_point_mass_statement_matches_source_and_capture(self):
        source=(ROOT.parent/'ctrllib/Ctrllib/PointMassComFlow.lean').read_text()
        capture=read(ROOT/'examples/ctrllib-e2e/graph/declarations.json')
        decl=next(d for d in capture['declarations'] if d['name']=='Ctrllib.pointMass_tendsto_zero')
        page=(ROOT/'examples/ctrllib-e2e/vault/PointMassComFlow.md').read_text()
        self.assertEqual(len(decl['binders']),7)
        self.assertEqual([b['name'] for b in decl['binders']],['m','d','k','hm','hd','hk','z₀'])
        signature=source.split('theorem pointMass_tendsto_zero')[1].split(':= by')[0]
        self.assertIn(' '.join(signature.split()),' '.join(page.split()))
        proof=source.split('theorem pointMass_tendsto_zero')[1]
        self.assertIn('com_attractive',proof); self.assertIn('pmM_inv',proof)
        self.assertIn('pmM_inv',page); self.assertIn('com_attractive',page)


class ConverterContracts(unittest.TestCase):
    def test_ir_roundtrip_success_failure_and_parse_failure(self):
        args=['round-trip','--source-profile',str(ROOT/'canonical/brickconverter/profiles/house.yaml'),'--target-profile',str(ROOT/'canonical/brickconverter/profiles/lean.yaml'),'--expression','1 + 2 * 3','--strict']
        code, data, err=invoke(args)
        self.assertEqual(code,0); self.assertTrue(data['ir_round_trip'])
        self.assertEqual(data['check_scope'],'normalized_ir_equality'); self.assertNotIn('semantic_round_trip',data)
        self.assertEqual(data['acceptance_status'],'not_assessed'); self.assertFalse(data['formal_check_performed'])
        real=cli.parse_math; count=0
        def different_reparse(text,profile):
            nonlocal count
            count+=1
            return real(text,profile) if count==1 else Lit('999')
        with patch.object(cli,'parse_math',side_effect=different_reparse):
            code, data, err=invoke(args)
        self.assertEqual(code,1); self.assertEqual(data['check_status'],'failed'); self.assertFalse(data['ir_round_trip'])
        args[args.index('1 + 2 * 3')]='unlistedSymbol'
        code,data,err=invoke(args)
        self.assertEqual(code,2); self.assertIsNone(data); self.assertIn('undeclared symbol',err)

    def test_existing_gate_success_failure_scope_and_receipt_hash(self):
        with tempfile.TemporaryDirectory() as temp:
            capture=Path(temp)/'capture.json'
            capture.write_text(json.dumps({'schema_version':1,'errors':[],'declarations':[{'name':'Test.existing','module':'Test','conclusion_tree':{'node':'lit','value':'1'}}]}))
            args=['check','--extractor',str(capture),'--profile',str(ROOT/'canonical/brickconverter/profiles/lean.yaml'),'--declaration','Test.existing','--ctrllib',temp]
            def outcome(passed):
                with patch.object(cli,'check_declaration',return_value={'matched_existing_declaration':True,'reused_kernel_checked_theorem':passed}) as gate:
                    result=invoke(args)
                # No rendered-output or expected-type argument reaches Lean.
                gate.assert_called_once_with(temp,'Test.existing','Test')
                return result
            code, good,err=outcome(True); self.assertEqual(code,0)
            _, repeat,_=outcome(True); self.assertEqual(good,repeat)
            code,bad,err=outcome(False); self.assertEqual(code,1)
            self.assertTrue(good['checks_passed']); self.assertFalse(bad['checks_passed'])
            self.assertNotEqual(good['receipt_hash'],bad['receipt_hash'])
            for data in (good,bad):
                self.assertEqual(data['check_scope'],'existing_declaration_check')
                self.assertEqual(data['acceptance_status'],'not_assessed')
                self.assertTrue(data['formal_check_performed'])
                self.assertFalse(data['generated_output_formally_checked']); self.assertFalse(data['source_equivalence_checked'])
                self.assertEqual(data['outputs']['lean_facing_sha256'],hashlib.sha256(b'1').hexdigest())
                body={k:v for k,v in data.items() if k!='receipt_hash'}
                expected=hashlib.sha256(json.dumps(body,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
                self.assertEqual(data['receipt_hash'],expected)


class FreshnessAdvice(unittest.TestCase):
    def test_partial_coverage_is_not_changed_input(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp); (root/'vault').mkdir(); dot=root/'graph.dot'; dot.write_text('digraph G {}')
            capture=root/'capture.json'; capture.write_text('{}')
            spec={'dot':str(dot),'extractor':str(capture),'vault':str(root/'vault')}
            saved={'spec':spec,'files':snapshot(spec),'issues':['source modules absent from graph: Ctrllib.Omitted']}
            conn=sqlite3.connect(':memory:'); conn.row_factory=sqlite3.Row
            conn.execute('CREATE TABLE input_state (id INTEGER PRIMARY KEY,payload TEXT)')
            conn.execute('INSERT INTO input_state VALUES (1,?)',(json.dumps(saved),))
            warning=current_warning(conn)
            self.assertIn('Rebuilding an unchanged capture cannot add omitted modules',warning)
            self.assertNotIn('selected inputs changed:',warning)
            dot.write_text('digraph G { changed }')
            changed=current_warning(conn)
            self.assertIn('selected inputs changed:',changed); self.assertIn('regeneration first',changed)
            conn.close()


if __name__=='__main__':
    unittest.main(verbosity=2)
