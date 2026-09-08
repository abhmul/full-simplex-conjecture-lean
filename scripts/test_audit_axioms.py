"""Synthetic parser/coverage tests only. No Lean compiler is invoked."""
import json
from pathlib import Path
import unittest
from audit_axioms import validate

class AuditTests(unittest.TestCase):
    path = Path('/tmp/FSC-Audit.lean')
    source = '#print axioms FSC.target\n'
    def report(self, text="'FSC.target' depends on axioms: [propext, Classical.choice, Quot.sound]", **kw):
        d={'severity':'information','data':text,'fileName':str(self.path),
           'pos':{'line':1,'column':0}}
        d.update(kw)
        return json.dumps(d)
    def test_standard(self):
        self.assertEqual(validate(self.source,self.report(),self.path,['FSC.target']),[])
    def test_empty_axioms(self):
        self.assertEqual(validate(self.source,self.report("'FSC.target' does not depend on any axioms"),self.path),[])
    def test_subset(self):
        self.assertEqual(validate(self.source,self.report("'FSC.target' depends on axioms: [propext]"),self.path),[])
    def test_missing(self):
        self.assertTrue(validate(self.source,'',self.path))
    def test_duplicate(self):
        self.assertTrue(validate(self.source,self.report()+'\n'+self.report(),self.path))
    def test_foreign_axiom(self):
        self.assertTrue(validate(self.source,self.report("'FSC.target' depends on axioms: [nativeComputation42]"),self.path))
    def test_sorry(self):
        self.assertTrue(validate(self.source,self.report("'FSC.target' depends on axioms: [sorryAx]"),self.path))
    def test_stale_location(self):
        self.assertTrue(validate(self.source,self.report(pos={'line':2,'column':0}),self.path))
    def test_wrong_file(self):
        self.assertTrue(validate(self.source,self.report(fileName='/tmp/old.lean'),self.path))
    def test_required_omitted(self):
        self.assertTrue(validate(self.source,self.report(),self.path,['FSC.strict']))
    def test_compiler_error(self):
        extra=json.dumps({'severity':'error','data':'failure'})
        self.assertTrue(validate(self.source,self.report()+'\n'+extra,self.path))
    def test_malformed(self):
        self.assertTrue(validate(self.source,'not json',self.path))

if __name__ == '__main__':
    unittest.main()
