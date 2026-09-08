import FSC.LinearAlgebra.Gram
import FSC.Gaussian.PinDefinitions
import FSC.Support.Differentiation

/-! Ordinary Gram normals and retained conditional supports near a common positive threshold.
No rank padding is used in threshold calculus.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace Topology

namespace FSC

/-- The canonical nondegenerate retained pair indices; independent of threshold or rank. -/
abbrev RetainedPair {n : ℕ} (G : Mat n) (i : Fin n) :=
  {j : Fin n // j ≠ i ∧ -1 < G i j ∧ G i j < 1}

def projectedNormal {n : ℕ} (G : Mat n) (i : Fin n) (j : RetainedPair G i) : Coord n :=
  (pairSigma G i j)⁻¹ • (gramVectors G j - G i j • gramVectors G i)

def conditionalSupport {n : ℕ} (G : Mat n) (i : Fin n) (b : Coord n)
    (j : RetainedPair G i) : ℝ := (b j - G i j * b i) / pairSigma G i j

theorem inner_gramVectors {n : ℕ} (G : Mat n) (hG : G.PosSemidef) (i j : Fin n) :
    inner ℝ (gramVectors G i) (gramVectors G j) = G i j := by
  simpa only [Matrix.gram_apply] using congrFun (congrFun (gram_gramVectors G hG) i) j

theorem correlation_entry_symm {n : ℕ} (G : Mat n) (hG : G.PosSemidef) (i j : Fin n) :
    G j i = G i j := by
  simpa using congrFun (congrFun hG.isHermitian.eq i) j

theorem correlation_entry_bounds {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) : -1 ≤ G i j ∧ G i j ≤ 1 := by
  rw [← inner_gramVectors G hG.1]
  exact ⟨neg_one_le_real_inner_of_norm_eq_one (norm_gramVectors G hG i) (norm_gramVectors G hG j),
    real_inner_le_one_of_norm_eq_one (norm_gramVectors G hG i) (norm_gramVectors G hG j)⟩

theorem gramVectors_injective {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) : Function.Injective (gramVectors G) := by
  intro i j hij
  by_contra hne
  have hlt := hDistinct i j hne
  have he : G i j = 1 := by
    rw [← inner_gramVectors G hG.1, hij, inner_gramVectors G hG.1, hG.2 j]
  linarith

theorem gramVectors_eq_neg_iff {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i j : Fin n) : gramVectors G i = -gramVectors G j ↔ G i j = -1 := by
  rw [← inner_gramVectors G hG.1,
    inner_eq_neg_one_iff_of_norm_eq_one (norm_gramVectors G hG i) (norm_gramVectors G hG j)]

theorem noCoincident_gramVectors {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (t : ℝ) (ht : 0 < t) :
    NoCoincident (gramVectors G) (fun _ : Fin n ↦ t) := by
  intro i j hij
  refine ⟨fun he ↦ False.elim (hij (gramVectors_injective G hG hDistinct he)), ?_⟩
  intro _ he
  linarith

theorem retained_sigma_pos {n : ℕ} (G : Mat n) (i : Fin n) (j : RetainedPair G i) :
    0 < pairSigma G i j := by
  apply Real.sqrt_pos.2
  nlinarith [j.property.2.1, j.property.2.2]

theorem retained_sigma_sq {n : ℕ} (G : Mat n) (i : Fin n) (j : RetainedPair G i) :
    pairSigma G i j ^ 2 = 1 - G i j ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [j.property.2.1, j.property.2.2]

theorem norm_projectedNormal {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (j : RetainedPair G i) : ‖projectedNormal G i j‖ = 1 := by
  have hnorm : ‖gramVectors G j - G i j • gramVectors G i‖ = pairSigma G i j := by
    have hsq : ‖gramVectors G j - G i j • gramVectors G i‖ ^ 2 = 1 - G i j ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        inner_gramVectors G hG.1, hG.2, correlation_entry_symm G hG.1 i]
      ring
    nlinarith [retained_sigma_sq G i j, retained_sigma_pos G i j,
      norm_nonneg (gramVectors G j - G i j • gramVectors G i)]
  rw [projectedNormal, norm_smul, hnorm, Real.norm_of_nonneg
    (inv_nonneg.mpr (retained_sigma_pos G i j).le), inv_mul_cancel₀ (retained_sigma_pos G i j).ne']

theorem projectedNormal_reconstruct {n : ℕ} (G : Mat n) (i : Fin n) (j : RetainedPair G i) :
    pairSigma G i j • projectedNormal G i j = gramVectors G j - G i j • gramVectors G i := by
  rw [projectedNormal, smul_smul, mul_inv_cancel₀ (retained_sigma_pos G i j).ne', one_smul]

theorem inner_projectedNormal_pin {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (i : Fin n) (j : RetainedPair G i) :
    inner ℝ (projectedNormal G i j) (gramVectors G i) = 0 := by
  simp only [projectedNormal, real_inner_smul_left, inner_sub_left,
    inner_gramVectors G hG.1, hG.2, correlation_entry_symm G hG.1 i,
    mul_one, sub_self, mul_zero]

theorem conditionalSupport_common {n : ℕ} (G : Mat n) (i : Fin n)
    (t : ℝ) (j : RetainedPair G i) :
    conditionalSupport G i (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t)) j =
      pairSupport G t i j := by
  simp only [conditionalSupport, WeakSimplex.Coord.ofFun_apply, pairSupport]
  ring

theorem retained_support_pos {n : ℕ} (G : Mat n) (i : Fin n) (t : ℝ) (ht : 0 < t)
    (j : RetainedPair G i) : 0 < pairSupport G t i j := by
  exact div_pos (mul_pos ht (sub_pos.mpr j.property.2.2)) (retained_sigma_pos G i j)

/-- Positive equal conditional supports determine the original correlation coefficient. -/
theorem support_ratio_injective {c d t σ τ : ℝ}
    (hc : c < 1) (hd : d < 1) (ht : 0 < t) (hσ : 0 < σ) (hτ : 0 < τ)
    (hσsq : σ ^ 2 = 1 - c ^ 2) (hτsq : τ ^ 2 = 1 - d ^ 2)
    (he : t * (1 - c) / σ = t * (1 - d) / τ) : c = d := by
  have hcross : (1 - c) * τ = (1 - d) * σ := by
    have h := (div_eq_div_iff hσ.ne' hτ.ne').mp he
    apply (mul_left_cancel₀ ht.ne')
    nlinarith only [h]
  have hsq := congrArg (fun x : ℝ ↦ x ^ 2) hcross
  simp only [mul_pow, hσsq, hτsq] at hsq
  have hfactor : (1 - c) * (1 - d) * (c - d) = 0 := by nlinarith only [hsq]
  have hz : c - d = 0 := (mul_eq_zero.mp hfactor).resolve_left
    (mul_ne_zero (sub_pos.mpr hc).ne' (sub_pos.mpr hd).ne')
  exact sub_eq_zero.mp hz

theorem retained_support_injective_correlation {n : ℕ} (G : Mat n) (i : Fin n)
    (t : ℝ) (ht : 0 < t) (j k : RetainedPair G i)
    (he : pairSupport G t i j = pairSupport G t i k) : G i j = G i k := by
  exact support_ratio_injective j.property.2.2 k.property.2.2 ht
    (retained_sigma_pos G i j) (retained_sigma_pos G i k)
    (retained_sigma_sq G i j) (retained_sigma_sq G i k) he

theorem noCoincident_projectedNormals {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t) :
    NoCoincident (projectedNormal G i) (fun j ↦ pairSupport G t i j) := by
  intro j k hjk
  refine ⟨?_, ?_⟩
  · intro hnormal hsupport
    have hc := retained_support_injective_correlation G i t ht j k hsupport
    have hσ : pairSigma G i j = pairSigma G i k := by simp only [pairSigma, hc]
    have he : gramVectors G j - G i j • gramVectors G i =
        gramVectors G k - G i k • gramVectors G i := by
      rw [← projectedNormal_reconstruct G i j, ← projectedNormal_reconstruct G i k, hσ, hnormal]
    rw [hc] at he
    have hv : gramVectors G j = gramVectors G k := by
      simpa using congrArg (fun z ↦ z + G i k • gramVectors G i) he
    exact hjk (Subtype.ext (gramVectors_injective G hG hDistinct hv))
  · intro _ he
    have hj := retained_support_pos G i t ht j
    have hk := retained_support_pos G i t ht k
    linarith

theorem noCoincident_conditionalSupport {n : ℕ} (G : Mat n) (hG : WeakSimplex.IsCorrelation G)
    (hDistinct : DistinctScores G) (i : Fin n) (t : ℝ) (ht : 0 < t) :
    NoCoincident (projectedNormal G i)
      (conditionalSupport G i (WeakSimplex.Coord.ofFun (fun _ : Fin n ↦ t))) := by
  simpa only [funext (conditionalSupport_common G i t)] using
    noCoincident_projectedNormals G hG hDistinct i t ht

end FSC
