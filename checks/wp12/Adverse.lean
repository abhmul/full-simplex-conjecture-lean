import FSC.LinearAlgebra.PaddedGram
import FSCProbes.SingularTriangle

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FSCChecks.WP12

open FSC

/-- The rank-two singular triangle is represented in the exact two-dimensional padded space. -/
theorem triangle_padded_law :
    ∃ v : Fin 3 → Coord 2, (∀ i, ‖v i‖ = 1) ∧
      Matrix.gram ℝ v = FSCProbes.SingularTriangle.gram ∧
      (stdGaussian (Coord 2)).map
        (fun y ↦ WeakSimplex.Coord.ofFun fun i ↦ inner ℝ (v i) y) =
        multivariateGaussian (0 : Coord 3) FSCProbes.SingularTriangle.gram := by
  exact exists_padded_unit_gram_law (by norm_num) _
    FSCProbes.SingularTriangle.gram_isCorrelation FSCProbes.SingularTriangle.gram_not_posDef

theorem duplicate_three_correlation :
    WeakSimplex.IsCorrelation (fun _ _ : Fin 3 ↦ (1 : ℝ)) := by
  constructor
  · have hm : Matrix.vecMulVec (fun _ : Fin 3 ↦ (1 : ℝ))
        (star (fun _ : Fin 3 ↦ (1 : ℝ))) = (fun _ _ : Fin 3 ↦ (1 : ℝ)) := by
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [← hm]
    exact Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin 3 ↦ (1 : ℝ))
  · intro i
    rfl

theorem duplicate_three_not_posDef : ¬Matrix.PosDef (fun _ _ : Fin 3 ↦ (1 : ℝ)) := by
  intro h
  have hp := h.det_pos
  norm_num [Matrix.det_fin_three] at hp

/-- Rank one is padded to dimension two; no exact-rank premise is smuggled into the law. -/
theorem rank_one_padded_law :
    ∃ v : Fin 3 → Coord 2, (∀ i, ‖v i‖ = 1) ∧
      Matrix.gram ℝ v = (fun _ _ ↦ 1) ∧
      (stdGaussian (Coord 2)).map
        (fun y ↦ WeakSimplex.Coord.ofFun fun i ↦ inner ℝ (v i) y) =
        multivariateGaussian (0 : Coord 3) (fun _ _ ↦ 1) := by
  exact exists_padded_unit_gram_law (by norm_num) _
    duplicate_three_correlation duplicate_three_not_posDef

/-- The n=3 tangent is a genuine one-dimensional standard Gaussian space. -/
theorem triangle_tangent_law (u : Coord 2) (hu : ‖u‖ = 1) :
    (stdGaussian ((ℝ ∙ u)ᗮ)).map (paddedTangentCoordinates (n := 3) (by norm_num) u hu) =
      stdGaussian (Coord 1) :=
  map_paddedTangentCoordinates_stdGaussian (n := 3) (by norm_num) u hu

end FSCChecks.WP12

#print axioms FSCChecks.WP12.triangle_padded_law
#print axioms FSCChecks.WP12.rank_one_padded_law
#print axioms FSCChecks.WP12.triangle_tangent_law
