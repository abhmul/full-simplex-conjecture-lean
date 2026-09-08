import FSC.LinearAlgebra.Gram
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! Singular Gram realization in a fixed codimension-one space and exact tangent coordinates. -/

noncomputable section

open MeasureTheory ProbabilityTheory Submodule
open scoped InnerProductSpace

namespace FSC

/-- A nonzero vector's orthogonal hyperplane has fixed Euclidean coordinates. -/
def orthogonalCoordinates {d : ℕ} (hd : 1 ≤ d) (u : Coord d) (hu : u ≠ 0) :
    (ℝ ∙ u)ᗮ ≃ₗᵢ[ℝ] Coord (d - 1) := by
  letI : Fact (Module.finrank ℝ (Coord d) = (d - 1) + 1) := ⟨by
    rw [finrank_euclideanSpace_fin]
    omega⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (d - 1) hu).repr

/-- Non-PD forces the ordinary square-root rows into a genuine hyperplane. -/
theorem exists_orthogonal_gramVectors {n : ℕ} (G : Mat n) (hG : G.PosSemidef)
    (hnot : ¬G.PosDef) :
    ∃ u : Coord n, u ≠ 0 ∧ ∀ i, inner ℝ (gramVectors G i) u = 0 := by
  let S : Submodule ℝ (Coord n) := Submodule.span ℝ (Set.range (gramVectors G))
  have hS : S ≠ ⊤ := by
    intro htop
    have hli : LinearIndependent ℝ (gramVectors G) :=
      linearIndependent_of_top_le_span_of_card_eq_finrank
        (by change ⊤ ≤ S; rw [htop]) (by simp)
    apply hnot
    rw [← gram_gramVectors G hG]
    exact Matrix.posDef_gram_of_linearIndependent hli
  have hperp : Sᗮ ≠ ⊥ := fun h ↦ hS (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨u, huS, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  refine ⟨u, hu, fun i ↦ ?_⟩
  exact Submodule.inner_right_of_mem_orthogonal
    (show gramVectors G i ∈ S from Submodule.subset_span (Set.mem_range_self i)) huS

/-- Every non-PD correlation admits unit normals in the fixed padded dimension `n-1`. -/
theorem exists_padded_unit_gram {n : ℕ} (hn : 1 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hnot : ¬G.PosDef) :
    ∃ v : Fin n → Coord (n - 1), (∀ i, ‖v i‖ = 1) ∧ Matrix.gram ℝ v = G := by
  obtain ⟨u, hu, horth⟩ := exists_orthogonal_gramVectors G hG.1 hnot
  let e := orthogonalCoordinates hn u hu
  let v : Fin n → (ℝ ∙ u)ᗮ := fun i ↦
    ⟨gramVectors G i, Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (horth i)⟩
  refine ⟨fun i ↦ e (v i), ?_, ?_⟩
  · intro i
    rw [e.norm_map]
    exact norm_gramVectors G hG i
  · rw [← gram_gramVectors G hG.1]
    ext i j
    simp only [Matrix.gram_apply, LinearIsometryEquiv.inner_map_map]
    rfl

/-- The public WSC score-law theorem applies to every chosen fixed-dimensional realization. -/
theorem map_score_stdGaussian_of_gram {d n : ℕ} (v : Fin n → Coord d) (G : Mat n)
    (hgram : Matrix.gram ℝ v = G) :
    (stdGaussian (Coord d)).map
      (fun y ↦ WeakSimplex.Coord.ofFun fun i ↦ inner ℝ (v i) y) =
      multivariateGaussian (0 : Coord n) G := by
  simpa only [WeakSimplex.codeGram, hgram] using WeakSimplex.map_codeScore_stdGaussian v

/-- The padded realization has the actual centered Gaussian law, even below maximal rank. -/
theorem exists_padded_unit_gram_law {n : ℕ} (hn : 1 ≤ n) (G : Mat n)
    (hG : WeakSimplex.IsCorrelation G) (hnot : ¬G.PosDef) :
    ∃ v : Fin n → Coord (n - 1), (∀ i, ‖v i‖ = 1) ∧ Matrix.gram ℝ v = G ∧
      (stdGaussian (Coord (n - 1))).map
        (fun y ↦ WeakSimplex.Coord.ofFun fun i ↦ inner ℝ (v i) y) =
        multivariateGaussian (0 : Coord n) G := by
  obtain ⟨v, hv, hgram⟩ := exists_padded_unit_gram hn G hG hnot
  exact ⟨v, hv, hgram, map_score_stdGaussian_of_gram v G hgram⟩

/-- Tangent coordinates keep dimension `n-2`, regardless of the intrinsic Gram rank. -/
def paddedTangentCoordinates {n : ℕ} (hn : 3 ≤ n) (u : Coord (n - 1)) (hu : ‖u‖ = 1) :
    (ℝ ∙ u)ᗮ ≃ₗᵢ[ℝ] Coord (n - 2) := by
  have hne : u ≠ 0 := by
    intro hz
    simp [hz] at hu
  letI : Fact (Module.finrank ℝ (Coord (n - 1)) = (n - 2) + 1) := ⟨by
    rw [finrank_euclideanSpace_fin]
    omega⟩
  exact (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n - 2) hne).repr

theorem norm_paddedTangentCoordinates {n : ℕ} (hn : 3 ≤ n)
    (u : Coord (n - 1)) (hu : ‖u‖ = 1) (x : (ℝ ∙ u)ᗮ) :
    ‖paddedTangentCoordinates hn u hu x‖ = ‖(x : Coord (n - 1))‖ :=
  (paddedTangentCoordinates hn u hu).norm_map x

theorem inner_paddedTangentCoordinates {n : ℕ} (hn : 3 ≤ n)
    (u : Coord (n - 1)) (hu : ‖u‖ = 1) (x y : (ℝ ∙ u)ᗮ) :
    inner ℝ (paddedTangentCoordinates hn u hu x) (paddedTangentCoordinates hn u hu y) =
      inner ℝ (x : Coord (n - 1)) (y : Coord (n - 1)) :=
  (paddedTangentCoordinates hn u hu).inner_map_map x y

/-- The tangent coordinate isometry transports the actual standard Gaussian law. -/
theorem map_paddedTangentCoordinates_stdGaussian {n : ℕ} (hn : 3 ≤ n)
    (u : Coord (n - 1)) (hu : ‖u‖ = 1) :
    (stdGaussian ((ℝ ∙ u)ᗮ)).map (paddedTangentCoordinates hn u hu) =
      stdGaussian (Coord (n - 2)) :=
  stdGaussian_map (paddedTangentCoordinates hn u hu)

end FSC
