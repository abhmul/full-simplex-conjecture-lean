import FSC.Gaussian.IndependentSum
import FSC.Gaussian.ConditionalCaps
import FSC.Simplex.BaseCases

/-! Exact replacement of one score by an independent standard Gaussian. -/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace FSC

def keepCoordinate {n : ℕ} (i : Fin n) : Mat n := Matrix.diagonal fun k ↦ if k = i then 1 else 0
def eraseCoordinate {n : ℕ} (i : Fin n) : Mat n := Matrix.diagonal fun k ↦ if k = i then 0 else 1

def replacementCov {n : ℕ} (G : Mat n) (i : Fin n) : Mat n :=
  eraseCoordinate i * G * (eraseCoordinate i).transpose +
    keepCoordinate i * (1 : Mat n) * (keepCoordinate i).transpose

def replacementScore {n : ℕ} (i : Fin n) (p : Coord n × Coord n) : Coord n :=
  lin (eraseCoordinate i) p.1 + lin (keepCoordinate i) p.2

@[simp] theorem replacementScore_apply {n : ℕ} (i k : Fin n) (p : Coord n × Coord n) :
    replacementScore i p k = if k = i then p.2 i else p.1 k := by
  classical
  by_cases h : k = i <;> simp [replacementScore, lin_apply, eraseCoordinate,
    keepCoordinate, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, h]

theorem replacementCov_isCorrelation {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) : WeakSimplex.IsCorrelation (replacementCov G i) := by
  refine ⟨(posSemidef_congruence G hG.1 _).add
    (posSemidef_congruence (1 : Mat n) Matrix.PosSemidef.one _), ?_⟩
  intro k
  by_cases h : k = i <;>
    simp [replacementCov, eraseCoordinate, keepCoordinate, Matrix.diagonal_mul,
      Matrix.mul_diagonal, h, hG.2]

theorem map_replacementScore {n : ℕ} (G : Mat n) (hG : G.PosSemidef) (i : Fin n) :
    ((multivariateGaussian (0 : Coord n) G).prod
      (multivariateGaussian (0 : Coord n) (1 : Mat n))).map (replacementScore i) =
        multivariateGaussian (0 : Coord n) (replacementCov G i) := by
  change Measure.map ((fun p : Coord n × Coord n ↦ p.1 + p.2) ∘
    Prod.map (lin (eraseCoordinate i)) (lin (keepCoordinate i))) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    map_lin_multivariateGaussian _ _ hG,
    map_lin_multivariateGaussian _ _ Matrix.PosSemidef.one,
    map_add_multivariateGaussian _ _ _ _
      (posSemidef_congruence G hG _) (posSemidef_congruence (1 : Mat n) Matrix.PosSemidef.one _)]
  simp only [map_zero, add_zero, replacementCov]

theorem replacementScore_preimage {n : ℕ} (i : Fin n) (t : ℝ) :
    replacementScore i ⁻¹' WeakSimplex.lowerOrthant t =
      singleEvent i t ×ˢ {y : Coord n | y i ≤ t} := by
  ext p
  change (∀ k, replacementScore i p k ≤ t) ↔ (∀ k, k ≠ i → p.1 k ≤ t) ∧ p.2 i ≤ t
  simp only [replacementScore_apply]
  constructor
  · intro h
    exact ⟨fun k hk ↦ by simpa [hk] using h k, by simpa using h i⟩
  · rintro ⟨h, hi⟩ k
    split_ifs with hk
    · exact hi
    · exact h k hk

theorem cdf_replacementCov {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (t : ℝ) :
    cdf (replacementCov G i) t = WeakSimplex.normalCDF t *
      (multivariateGaussian (0 : Coord n) G (singleEvent i t)).toReal := by
  have hI : WeakSimplex.IsCorrelation (1 : Mat n) :=
    ⟨Matrix.PosSemidef.one, fun k ↦ Matrix.one_apply_eq k⟩
  rw [cdf, ← map_replacementScore G hG.1 i,
    Measure.map_apply (by unfold replacementScore; fun_prop) (WeakSimplex.measurableSet_lowerOrthant t),
    replacementScore_preimage, Measure.prod_prod, ENNReal.toReal_mul,
    gaussian_coordinate_le_toReal (1 : Mat n) hI i t, mul_comm]

theorem duplicate_coordinates_ae {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (hij : G i j = 1) :
    ∀ᵐ x ∂multivariateGaussian (0 : Coord n) G, x i = x j := by
  have hv : gramVectors G i = gramVectors G j :=
    (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) (norm_gramVectors G hG i)
      (norm_gramVectors G hG j)).mp (by rw [inner_gramVectors G hG.1, hij])
  rw [← map_gramVectors_stdGaussian G hG.1]
  apply (ae_map_iff (measurable_gramScore G).aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
  exact Filter.Eventually.of_forall fun y ↦ by simp only [WeakSimplex.Coord.ofFun_apply, hv]

theorem cdf_replacementCov_of_duplicate {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) (hij : i ≠ j) (hc : G i j = 1) (t : ℝ) :
    cdf (replacementCov G i) t = WeakSimplex.normalCDF t * cdf G t := by
  rw [cdf_replacementCov G hG i t]
  congr 1
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [duplicate_coordinates_ae G hG i j hc] with x hx
  apply propext
  change (∀ k, k ≠ i → x k ≤ t) ↔ ∀ k, x k ≤ t
  constructor
  · intro h k
    by_cases hk : k = i
    · rw [hk, hx]
      exact h j hij.symm
    · exact h k hk
  · intro h k _
    exact h k

end FSC
