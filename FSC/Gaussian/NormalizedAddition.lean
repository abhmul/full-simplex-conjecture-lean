import FSC.Gaussian.IndependentSum
import Mathlib.MeasureTheory.Integral.Prod

/-! Normalized PSD addition under the actual independent Gaussian product law.
The threshold-shift identity follows SUPPORT_NOISE_VARIATION section 4 and is valid at every PSD rank.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSC

def normalizingDiagonal {n : ℕ} (L : Mat n) (s : ℝ) : Mat n :=
  Matrix.diagonal (fun i ↦ (Real.sqrt (1 + s * L i i))⁻¹)

def normalizationShift {n : ℕ} (L : Mat n) (t s : ℝ) : Coord n :=
  WeakSimplex.Coord.ofFun (fun i ↦ t * (Real.sqrt (1 + s * L i i) - 1))

theorem normalizingDiagonal_cov {n : ℕ} (G L : Mat n) (s : ℝ) :
    normalizingDiagonal L s * (G + s • L) * (normalizingDiagonal L s).transpose =
      normalizedAdd G L s := by
  ext i j
  simp [normalizingDiagonal, normalizedAdd, Matrix.diagonal_mul, Matrix.mul_diagonal,
    div_eq_mul_inv]
  ring

@[simp] theorem lin_normalizingDiagonal {n : ℕ} (L : Mat n) (s : ℝ) (x : Coord n) (i : Fin n) :
    lin (normalizingDiagonal L s) x i = x i / Real.sqrt (1 + s * L i i) := by
  simp [lin_apply, normalizingDiagonal, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]

theorem normalization_scale_pos {n : ℕ} {L : Mat n} (hL : L.PosSemidef)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin n) : 0 < Real.sqrt (1 + s * L i i) := by
  apply Real.sqrt_pos.2
  have hprod : 0 ≤ s * L i i := mul_nonneg hs hL.diag_nonneg
  linarith

theorem normalizedAdd_isCorrelation {n : ℕ} {G L : Mat n}
    (hG : WeakSimplex.IsCorrelation G) (hL : L.PosSemidef) {s : ℝ} (hs : 0 ≤ s) :
    WeakSimplex.IsCorrelation (normalizedAdd G L s) := by
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [← normalizingDiagonal_cov]
    exact posSemidef_congruence (G + s • L) (hG.1.add (hL.smul hs)) (normalizingDiagonal L s)
  · have hpos := normalization_scale_pos hL hs i
    rw [normalizedAdd, hG.2 i, Real.mul_self_sqrt (by
      have hprod : 0 ≤ s * L i i := mul_nonneg hs hL.diag_nonneg
      linarith)]
    exact div_self (by
      have hprod : 0 ≤ s * L i i := mul_nonneg hs hL.diag_nonneg
      linarith)

@[simp] theorem normalizedAdd_zero {n : ℕ} (G L : Mat n) : normalizedAdd G L 0 = G := by
  ext i j
  simp [normalizedAdd]

@[simp] theorem normalizationShift_zero {n : ℕ} (L : Mat n) (t : ℝ) :
    normalizationShift L t 0 = 0 := by
  ext i
  simp [normalizationShift]

/-- Choosing negative noise gives the plus sign in the threshold-shift expectation. -/
theorem map_sub_sqrt_smul_multivariateGaussian {n : ℕ}
    (G L : Mat n) (hG : G.PosSemidef) (hL : L.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun p : Coord n × Coord n ↦ p.1 - Real.sqrt s • p.2)
      ((multivariateGaussian (0 : Coord n) G).prod (multivariateGaussian (0 : Coord n) L)) =
      multivariateGaussian (0 : Coord n) (G + s • L) := by
  simpa only [one_smul, one_pow, smul_zero, zero_add, neg_smul, sub_eq_add_neg,
    neg_sq, Real.sq_sqrt hs] using
    map_weighted_multivariateGaussian (0 : Coord n) 0 G L hG hL 1 (-Real.sqrt s)

theorem map_normalizedAddition {n : ℕ}
    (G L : Mat n) (hG : G.PosSemidef) (hL : L.PosSemidef) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun p : Coord n × Coord n ↦
      lin (normalizingDiagonal L s) (p.1 - Real.sqrt s • p.2))
      ((multivariateGaussian (0 : Coord n) G).prod (multivariateGaussian (0 : Coord n) L)) =
      multivariateGaussian (0 : Coord n) (normalizedAdd G L s) := by
  change Measure.map ((lin (normalizingDiagonal L s)) ∘
    (fun p : Coord n × Coord n ↦ p.1 - Real.sqrt s • p.2)) _ = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    map_sub_sqrt_smul_multivariateGaussian G L hG hL s hs]
  simpa only [map_zero, normalizingDiagonal_cov] using map_lin_multivariateGaussian
    (0 : Coord n) (G + s • L) (hG.add (hL.smul hs)) (normalizingDiagonal L s)

theorem normalizedAddition_event {n : ℕ}
    (L : Mat n) (hL : L.PosSemidef) (t s : ℝ) (hs : 0 ≤ s) (x y : Coord n) :
    lin (normalizingDiagonal L s) (x - Real.sqrt s • y) ∈ WeakSimplex.lowerOrthant t ↔
    x ∈ thresholdEvent (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t) +
      normalizationShift L t s + Real.sqrt s • y) := by
  change (∀ i, lin (normalizingDiagonal L s) (x - Real.sqrt s • y) i ≤ t) ↔ _
  simp only [lin_normalizingDiagonal, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    thresholdEvent, Set.mem_setOf_eq, PiLp.add_apply, WeakSimplex.Coord.ofFun_apply,
    normalizationShift]
  apply forall_congr'
  intro i
  rw [div_le_iff₀ (normalization_scale_pos hL hs i)]
  constructor <;> intro h <;> linarith

/-- Exact actual-law Fubini identity; neither covariance rank nor threshold sign is restricted. -/
theorem cdf_normalizedAdd_eq_noiseAverage {n : ℕ}
    (G L : Mat n) (hG : G.PosSemidef) (hL : L.PosSemidef) (t s : ℝ) (hs : 0 ≤ s) :
    cdf (normalizedAdd G L s) t =
      ∫ y : Coord n, thresholdCDF G
        (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t) +
          normalizationShift L t s + Real.sqrt s • y)
        ∂multivariateGaussian (0 : Coord n) L := by
  classical
  let T : Coord n × Coord n → Coord n :=
    fun p ↦ lin (normalizingDiagonal L s) (p.1 - Real.sqrt s • p.2)
  have hT : Measurable T := by fun_prop
  let E := T ⁻¹' WeakSimplex.lowerOrthant t
  have hE : MeasurableSet E := (WeakSimplex.measurableSet_lowerOrthant t).preimage hT
  have hInt : Integrable (E.indicator (1 : Coord n × Coord n → ℝ))
      ((multivariateGaussian (0 : Coord n) G).prod (multivariateGaussian (0 : Coord n) L)) :=
    (integrable_const (1 : ℝ)).indicator hE
  rw [cdf, ← map_normalizedAddition G L hG hL s hs,
    Measure.map_apply hT (WeakSimplex.measurableSet_lowerOrthant t)]
  change (((multivariateGaussian (0 : Coord n) G).prod
    (multivariateGaussian (0 : Coord n) L)).real E) = _
  rw [← integral_indicator_one hE, integral_prod_symm _ hInt]
  apply integral_congr_ae
  filter_upwards with y
  have heq : (fun x : Coord n ↦ E.indicator (1 : Coord n × Coord n → ℝ) (x, y)) =
      (thresholdEvent (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t) +
        normalizationShift L t s + Real.sqrt s • y)).indicator (1 : Coord n → ℝ) := by
    funext x
    have he : (x, y) ∈ E ↔ x ∈ thresholdEvent
        (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t) + normalizationShift L t s + Real.sqrt s • y) :=
      normalizedAddition_event L hL t s hs x y
    simp only [Set.indicator_apply, he, Pi.one_apply]
  rw [heq, integral_indicator_one (measurableSet_thresholdEvent _)]
  rfl

end FSC
