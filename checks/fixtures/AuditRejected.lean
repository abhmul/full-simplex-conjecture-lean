import Init

/- Deliberately untrusted audit-calibration fixture; never imported by a library. -/
axiom FSCFixture.unapproved : False
theorem FSCFixture.rejected : False := FSCFixture.unapproved
#print axioms FSCFixture.rejected
