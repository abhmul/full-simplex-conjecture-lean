import FSC.Support.Differentiation
import FSCProbes.SingularTriangle

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FSCChecks.WP05Support

open FSC

/-- The manuscript's five planar directions, including both antipodal pairs. -/
def planarNormals : Fin 5 → Coord 2 :=
  ![WeakSimplex.Coord.ofFun ![1, 0], WeakSimplex.Coord.ofFun ![0, 1],
    WeakSimplex.Coord.ofFun ![3 / 5, 4 / 5], WeakSimplex.Coord.ofFun ![-1, 0],
    WeakSimplex.Coord.ofFun ![0, -1]]

theorem planar_unit (j : Fin 5) : ‖planarNormals j‖ = 1 := by
  have hs : ‖planarNormals j‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases j <;> norm_num [planarNormals, Fin.sum_univ_two]
  nlinarith [norm_nonneg (planarNormals j)]

theorem planar_noCoincident (t : ℝ) (ht : 0 < t) :
    NoCoincident planarNormals (fun _ ↦ t) := by
  intro j k hjk
  refine ⟨?_, fun _ ↦ by linarith⟩
  intro heq _
  have h₀ := congrArg (fun v : Coord 2 ↦ v 0) heq
  have h₁ := congrArg (fun v : Coord 2 ↦ v 1) heq
  fin_cases j <;> fin_cases k <;>
    norm_num [planarNormals] at *

/-- Actual five-direction cap has the canonical derivative at every positive common threshold. -/
theorem planar_actual_derivative (t : ℝ) (ht : 0 < t) :
    HasFDerivAt (capMass planarNormals) (supportGradient planarNormals (fun _ ↦ t))
      (fun _ ↦ t) :=
  hasFDerivAt_capMass planarNormals planar_unit _ (planar_noCoincident t ht)

/-- After pinning the first direction, the three nonantipodal tangent normals retain redundancy. -/
def projectedNormals : Fin 3 → Coord 1 :=
  ![WeakSimplex.Coord.ofFun ![1], WeakSimplex.Coord.ofFun ![1],
    WeakSimplex.Coord.ofFun ![-1]]

theorem projected_unit (j : Fin 3) : ‖projectedNormals j‖ = 1 := by
  have hs : ‖projectedNormals j‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases j <;> norm_num [projectedNormals]
  nlinarith [norm_nonneg (projectedNormals j)]

theorem projected_noCoincident (t : ℝ) (ht : 0 < t) :
    NoCoincident projectedNormals ![t, t / 2, t] := by
  intro j k hjk
  constructor
  · intro heq
    have h₀ := congrArg (fun v : Coord 1 ↦ v 0) heq
    fin_cases j <;> fin_cases k <;>
      norm_num [projectedNormals] at * <;> linarith
  · intro heq
    have h₀ := congrArg (fun v : Coord 1 ↦ v 0) heq
    fin_cases j <;> fin_cases k <;>
      norm_num [projectedNormals] at * <;> linarith

/-- The actual projected redundant and antipodal cap is C1 in all three listed supports. -/
theorem projected_actual_C1 (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ 1 (capMass projectedNormals) ![t, t / 2, t] :=
  contDiffAt_one_capMass projectedNormals projected_unit _ (projected_noCoincident t ht)

/-- The weaker upper face has zero actual slice mass, so it contributes no derivative. -/
theorem projected_weaker_sliceMass_zero (t : ℝ) (ht : 0 < t) :
    sliceMass projectedNormals ![t, t / 2, t] 0 = 0 := by
  have hn : projectedNormals 0 = FSCProbes.SingularTriangle.redundantNormals 0 := by
    ext i
    fin_cases i
    rfl
  rw [sliceMass, hn, FSCProbes.SingularTriangle.redundant_sliceLaw]
  have hbad : ¬t ≤ t / 2 := by linarith
  simp [projectedNormals, PiLp.inner_apply, Fin.forall_fin_succ, hbad]

theorem projected_weaker_derivative_zero (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ capMass projectedNormals (Function.update ![t, t / 2, t] 0 z))
      0 t := by
  simpa only [Matrix.cons_val_zero, projected_weaker_sliceMass_zero t ht, mul_zero] using
    hasDerivAt_capMass_update projectedNormals projected_unit _ (projected_noCoincident t ht) 0

/-- Opposite normals at zero support fail the required noncoincidence hypothesis. -/
theorem antipodal_zero_is_coincident :
    ¬NoCoincident
      (![WeakSimplex.Coord.ofFun ![1], WeakSimplex.Coord.ofFun ![-1]] : Fin 2 → Coord 1)
      (fun _ ↦ 0) := by
  intro h
  have heq : (WeakSimplex.Coord.ofFun ![1] : Coord 1) = -WeakSimplex.Coord.ofFun ![-1] := by
    ext i
    fin_cases i
    norm_num
  simpa using (h 0 1 (by decide)).2 heq

/-- Empty families remain valid even in a zero-dimensional ambient space. -/
theorem empty_ambient_C1 (w : Fin 0 → Coord 0) (b : Fin 0 → ℝ) :
    ContDiffAt ℝ 1 (capMass w) b := by
  apply contDiffAt_one_capMass
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j

/-- The new generic theorem accepts the genuine unbounded redundant triangle cap. -/
theorem unbounded_redundant_C1 (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ 1 (capMass FSCProbes.SingularTriangle.redundantNormals) ![t, 2 * t] := by
  apply contDiffAt_one_capMass
  · intro j
    have hs : ‖FSCProbes.SingularTriangle.redundantNormals j‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [FSCProbes.SingularTriangle.redundantNormals]
    nlinarith [norm_nonneg (FSCProbes.SingularTriangle.redundantNormals j)]
  · intro j k hjk
    constructor
    · intro _
      fin_cases j <;> fin_cases k <;> simp at hjk ⊢ <;> linarith
    · intro _
      fin_cases j <;> fin_cases k <;> simp at hjk ⊢ <;> linarith

/-- Existing exact counterexample is retained at the tied equal-support reference. -/
theorem tied_reference_not_differentiable (t : ℝ) :
    ¬ DifferentiableAt ℝ
      (fun b : ℝ ↦ capMass FSCProbes.SingularTriangle.redundantNormals ![t, b]) t :=
  FSCProbes.SingularTriangle.not_differentiableAt_tied_support t

end FSCChecks.WP05Support

#print axioms FSCChecks.WP05Support.planar_actual_derivative
#print axioms FSCChecks.WP05Support.projected_actual_C1
#print axioms FSCChecks.WP05Support.projected_weaker_derivative_zero
#print axioms FSCChecks.WP05Support.antipodal_zero_is_coincident
#print axioms FSCChecks.WP05Support.empty_ambient_C1
#print axioms FSCChecks.WP05Support.unbounded_redundant_C1
#print axioms FSCChecks.WP05Support.tied_reference_not_differentiable
