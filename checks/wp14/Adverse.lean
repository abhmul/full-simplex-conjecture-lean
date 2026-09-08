import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace FSCChecks

/-- The supplied zero-component adverse case is a scalar inequality counterexample. -/
theorem emptyComponentCounterexample :
    let u : Fin 2 → ℝ := ![1 / 2, 0]
    let e : Fin 2 → ℝ := ![1 / 2, 0]
    let omega : Fin 2 → ℝ := fun _ ↦ 1 / 2
    let M : ℝ := 6 / 5
    0 < M ∧ (∀ i, 0 ≤ u i ∧ 0 ≤ e i ∧ 0 < omega i) ∧
      (∑ i, omega i) = 1 ∧
      (∀ i, omega i * e i ≤
        (u i + e i) ^ 2 / M - (u i) ^ 2 / (∑ j, u j)) ∧
      (∑ i, (u i + e i)) < M ∧ u 1 = 0 ∧ e 1 = 0 := by
  dsimp
  refine ⟨by norm_num, ?_, by norm_num, ?_, ?_, rfl, rfl⟩
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

#print axioms emptyComponentCounterexample

end FSCChecks
