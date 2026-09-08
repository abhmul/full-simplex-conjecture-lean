import FSC.Definitions
import WeakSimplexConjectureLean.Coding.BayesValue

/-! Ordinary n-dimensional Gram realization using the pinned matrix square root. This is independent of the later singular rank-padding construction. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace MatrixOrder

namespace FSC

/-- Rows of the positive square root, regarded as ordinary n-dimensional vectors. -/
def gramVectors {n : ℕ} (G : Mat n) (i : Fin n) : Coord n :=
  WeakSimplex.Coord.ofFun fun j ↦ CFC.sqrt G i j

/-- Every PSD matrix has the prescribed ordinary Gram realization. -/
theorem gram_gramVectors {n : ℕ} (G : Mat n) (hG : G.PosSemidef) :
    Matrix.gram ℝ (gramVectors G) = G := by
  have hsqrt : (CFC.sqrt G).transpose = CFC.sqrt G := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (CFC.sqrt_nonneg G).isSelfAdjoint.isHermitian.eq
  calc
    Matrix.gram ℝ (gramVectors G) = CFC.sqrt G * (CFC.sqrt G).transpose := by
      ext i j
      simp [Matrix.gram_apply, gramVectors, PiLp.inner_apply, Matrix.mul_apply, mul_comm]
    _ = G := by rw [hsqrt, CFC.sqrt_mul_sqrt_self G hG.nonneg]

/-- Correlation matrices are realized by unit vectors, including singular matrices. -/
theorem norm_gramVectors {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) : ‖gramVectors G i‖ = 1 := by
  have hdiag : inner ℝ (gramVectors G i) (gramVectors G i) = 1 := by
    have h := congrFun (congrFun (gram_gramVectors G hG.1) i) i
    simpa only [Matrix.gram_apply, hG.2 i] using h
  rw [real_inner_self_eq_norm_sq] at hdiag
  nlinarith [norm_nonneg (gramVectors G i)]

/-- An existence form of ordinary unit Gram realization, with no rank hypothesis. -/
theorem exists_unit_gram {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G) :
    ∃ v : Fin n → Coord n, (∀ i, ‖v i‖ = 1) ∧ Matrix.gram ℝ v = G :=
  ⟨gramVectors G, norm_gramVectors G hG, gram_gramVectors G hG.1⟩

/-- The chosen realization has the actual all-PSD Gaussian score law. -/
theorem map_gramVectors_stdGaussian {n : ℕ} (G : Mat n) (hG : G.PosSemidef) :
    Measure.map
      (fun z : Coord n ↦ WeakSimplex.Coord.ofFun fun i ↦ inner ℝ (gramVectors G i) z)
      (stdGaussian (Coord n)) = multivariateGaussian (0 : Coord n) G := by
  simpa only [WeakSimplex.codeGram, gram_gramVectors G hG] using
    WeakSimplex.map_codeScore_stdGaussian (gramVectors G)

end FSC
