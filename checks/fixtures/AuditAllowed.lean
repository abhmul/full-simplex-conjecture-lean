import Init

theorem FSCFixture.rfl_nat : (0 : Nat) = 0 := rfl
#print axioms FSCFixture.rfl_nat

theorem FSCFixture.excluded_middle (p : Prop) : p ∨ ¬ p := Classical.em p
#print axioms FSCFixture.excluded_middle
