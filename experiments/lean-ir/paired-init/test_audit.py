import copy, unittest
from audit import scalar_claims
class ScalarClaims(unittest.TestCase):
 def claim(self,**kwargs):
  c=dict(nodeId=8,fieldIndex=0,value='4294967294',domain='Int',sourceType='Std.Format.nest',signedValue='-2');c.update(kwargs);return c
 def valid(self,*cs):return scalar_claims(dict(claims=list(cs),claimCount=len(cs)))
 def test_signed_native_int(self):self.assertEqual({(8,0):'4294967294'},self.valid(self.claim()))
 def test_nat_same_payload_has_distinct_domain(self):self.assertEqual({(8,0):'4294967294'},self.valid({k:v for k,v in self.claim(domain='Nat',sourceType='Std.Format.tag').items()if k!='signedValue'}))
 def test_wrong_signed_value(self):
  with self.assertRaises(ValueError):self.valid(self.claim(signedValue='4294967294'))
 def test_reject_signed_name(self):
  with self.assertRaises(ValueError):self.valid(self.claim(sourceType='Lean.Name.num'))
 def test_no_domain_inference_from_shape(self):
  with self.assertRaises(ValueError):self.valid(self.claim(domain='Nat'))
 def test_duplicate_source_slot(self):
  with self.assertRaises(ValueError):self.valid(self.claim(),self.claim())
 def test_int_outside_original_small_int_encoding(self):
  with self.assertRaises(ValueError):self.valid(self.claim(value='4294967296',signedValue='0'))
if __name__=='__main__':unittest.main()
