import FSC.Simplex.Definitions
import FSC.Gaussian.SinglePin
import FSC.Gaussian.ThresholdExpansion
import FSC.Support.Differentiation
import FSC.LinearAlgebra.Gram
import Mathlib.Data.Fintype.EquivFin

/-! Simplex conditional recursion and exact repetition of an existing support list. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators

namespace FSC

/-- A finite nonempty list can be extended to a prescribed larger size by repetition. -/
theorem exists_surjection_fin {ι : Type*} [Fintype ι] [Nonempty ι] {m : ℕ}
    (hm : Fintype.card ι ≤ m) : ∃ f : Fin m → ι, Function.Surjective f := by
  let e : ι → Fin m := fun i ↦ Fin.castLE hm (Fintype.equivFin ι i)
  have he : Function.Injective e := by
    intro i j h
    apply (Fintype.equivFin ι).injective
    exact Fin.ext (congrArg (fun x : Fin m ↦ x.val) h)
  exact ⟨Function.invFun e, Function.invFun_surjective he⟩

theorem cap_reindex_surjective {ι κ : Type*} {d : ℕ} (w : ι → Coord d)
    (b : ι → ℝ) (f : κ → ι) (hf : Function.Surjective f) :
    cap (w ∘ f) (b ∘ f) = cap w b := by
  ext y
  change (∀ k, inner ℝ (w (f k)) y ≤ b (f k)) ↔ ∀ j, inner ℝ (w j) y ≤ b j
  constructor
  · intro h j
    obtain ⟨k, rfl⟩ := hf j
    exact h k
  · intro h k
    exact h (f k)

/-- Conditional standard deviation after removing one of `m+1` simplex scores. -/
def simplexPinScale (m : ℕ) : ℝ := Real.sqrt (1 - (1 / (m : ℝ)) ^ 2)

theorem simplexPinScale_pos {m : ℕ} (hm : 2 ≤ m) : 0 < simplexPinScale m := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hi : 0 < (1 : ℝ) / m := div_pos zero_lt_one (by linarith)
  have hi1 : (1 : ℝ) / m < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem simplexPinScale_sq {m : ℕ} (hm : 2 ≤ m) :
    simplexPinScale m ^ 2 = 1 - (1 / (m : ℝ)) ^ 2 :=
  Real.sq_sqrt (Real.sqrt_pos.mp (simplexPinScale_pos hm)).le

/-- Standardized deletion of a single coordinate. -/
def simplexPinMatrix {m : ℕ} (i : Fin (m + 1)) : Matrix (Fin m) (Fin (m + 1)) ℝ :=
  fun k l ↦ if i.succAbove k = l then (simplexPinScale m)⁻¹ else 0

theorem lin_simplexPinMatrix {m : ℕ} (i : Fin (m + 1)) (x : Coord (m + 1)) (k : Fin m) :
    lin (simplexPinMatrix i) x k = (simplexPinScale m)⁻¹ * x (i.succAbove k) := by
  classical
  simp [lin_apply, Matrix.mulVec, dotProduct, simplexPinMatrix]

theorem simplexPinMatrix_congruence {m : ℕ} (i : Fin (m + 1)) (G : Mat (m + 1)) :
    simplexPinMatrix i * G * (simplexPinMatrix i).transpose =
      fun k l ↦ (simplexPinScale m)⁻¹ * (simplexPinScale m)⁻¹ *
        G (i.succAbove k) (i.succAbove l) := by
  classical
  ext k l
  simp only [Matrix.mul_apply, simplexPinMatrix, Matrix.transpose_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem simplexPinMatrix_covariance {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) :
    simplexPinMatrix i * singleCov (simplex (m + 1)) i * (simplexPinMatrix i).transpose =
      simplex m := by
  classical
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hs0 : simplexPinScale m ≠ 0 := ne_of_gt (simplexPinScale_pos hm)
  have hsq := simplexPinScale_sq hm
  field_simp at hsq
  rw [simplexPinMatrix_congruence]
  ext k l
  simp only [singleCov, simplex_apply (by omega : 2 ≤ m + 1), simplex_apply hm,
    Fin.succAbove_ne, if_false, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Fin.succAbove_right_inj]
  split_ifs <;> field_simp <;> nlinarith [hsq]

def simplexPinShift {m : ℕ} (t : ℝ) : Coord m :=
  WeakSimplex.Coord.ofFun fun _ ↦ t / (m : ℝ) / simplexPinScale m

theorem simplexPinMatrix_mean {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) (t : ℝ) :
    simplexPinShift (m := m) t + lin (simplexPinMatrix i) (singleMean (simplex (m + 1)) i t) = 0 := by
  ext k
  simp only [PiLp.add_apply, simplexPinShift, WeakSimplex.Coord.ofFun_apply,
    lin_simplexPinMatrix, singleMean, simplex_apply (by omega : 2 ≤ m + 1),
    Fin.succAbove_ne, if_false, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    PiLp.zero_apply]
  ring

/-- The whole actual one-pin law standardizes to the lower-size regular Gaussian law. -/
theorem map_simplex_singleLaw {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) (t : ℝ) :
    (singleLaw (simplex (m + 1)) i t).map
      (fun x ↦ simplexPinShift (m := m) t + lin (simplexPinMatrix i) x) =
      multivariateGaussian (0 : Coord m) (simplex m) := by
  rw [singleLaw, map_affine_multivariateGaussian _ _
    (singleCov_posSemidef _ (simplex_isCorrelation (by omega)) i),
    simplexPinMatrix_covariance hm i, simplexPinMatrix_mean hm i t]

theorem simplexPin_preimage {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) (t : ℝ) :
    (fun x ↦ simplexPinShift (m := m) t + lin (simplexPinMatrix i) x) ⁻¹'
      WeakSimplex.lowerOrthant ((t + t / (m : ℝ)) / simplexPinScale m) =
        singleEvent i t := by
  have hs := simplexPinScale_pos hm
  ext x
  change (∀ k : Fin m, (simplexPinShift (m := m) t + lin (simplexPinMatrix i) x) k ≤ _) ↔
    ∀ j, j ≠ i → x j ≤ t
  have hcoord (k : Fin m) :
      (simplexPinShift (m := m) t + lin (simplexPinMatrix i) x) k ≤
        (t + t / (m : ℝ)) / simplexPinScale m ↔ x (i.succAbove k) ≤ t := by
    simp only [PiLp.add_apply, simplexPinShift, WeakSimplex.Coord.ofFun_apply,
      lin_simplexPinMatrix]
    rw [inv_mul_eq_div, ← add_div, div_le_div_iff_of_pos_right hs]
    constructor <;> intro h <;> linarith
  simp_rw [hcoord]
  constructor
  · intro h j hji
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact h k
  · intro h k
    exact h _ (Fin.succAbove_ne i k)

theorem singlePinMass_simplex_raw {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) (t : ℝ) :
    singlePinMass (simplex (m + 1)) t i =
      cdf (simplex m) ((t + t / (m : ℝ)) / simplexPinScale m) := by
  rw [cdf, ← map_simplex_singleLaw hm i t, Measure.map_apply (by fun_prop)
    (WeakSimplex.measurableSet_lowerOrthant _), simplexPin_preimage hm i t]
  rfl

theorem simplex_conditional_threshold {m : ℕ} (hm : 2 ≤ m) (t : ℝ) :
    (t + t / (m : ℝ)) / simplexPinScale m = t * Real.sqrt (((m : ℝ) + 1) / ((m : ℝ) - 1)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hs0 : simplexPinScale m ≠ 0 := ne_of_gt (simplexPinScale_pos hm)
  have hsq := simplexPinScale_sq hm
  field_simp at hsq
  have hq : ((1 + 1 / (m : ℝ)) / simplexPinScale m) ^ 2 =
      ((m : ℝ) + 1) / ((m : ℝ) - 1) := by
    field_simp
    nlinarith [hsq]
  have hratio : 0 ≤ ((m : ℝ) + 1) / ((m : ℝ) - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hqpos : 0 ≤ (1 + 1 / (m : ℝ)) / simplexPinScale m :=
    div_nonneg (by positivity) (simplexPinScale_pos hm).le
  have he : (1 + 1 / (m : ℝ)) / simplexPinScale m =
      Real.sqrt (((m : ℝ) + 1) / ((m : ℝ) - 1)) := by
    nlinarith [Real.sq_sqrt hratio, Real.sqrt_nonneg (((m : ℝ) + 1) / ((m : ℝ) - 1))]
  calc
    _ = t * ((1 + 1 / (m : ℝ)) / simplexPinScale m) := by ring
    _ = _ := by rw [he]

theorem singlePinMass_simplex {m : ℕ} (hm : 2 ≤ m) (i : Fin (m + 1)) (t : ℝ) :
    singlePinMass (simplex (m + 1)) t i =
      cdf (simplex m) (t * Real.sqrt (((m : ℝ) + 1) / ((m : ℝ) - 1))) := by
  rw [singlePinMass_simplex_raw hm i t, simplex_conditional_threshold hm t]

theorem simplex_distinct {n : ℕ} (hn : 2 ≤ n) : DistinctScores (simplex n) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  intro i j hij
  rw [simplex_apply hn, if_neg hij]
  exact lt_of_lt_of_le (div_neg_of_neg_of_pos (by norm_num) (by linarith)) zero_le_one

theorem hasDerivAt_simplex_cdf_succ {m : ℕ} (hm : 2 ≤ m) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (cdf (simplex (m + 1)))
      (((m : ℝ) + 1) * WeakSimplex.normalPDF t *
        cdf (simplex m) (t * Real.sqrt (((m : ℝ) + 1) / ((m : ℝ) - 1)))) t := by
  have h := hasDerivAt_cdf (simplex (m + 1)) (simplex_isCorrelation (by omega))
    (simplex_distinct (by omega)) t ht
  convert! h using 1
  simp only [boundarySlope, singlePinMass_simplex hm, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Exact regular derivative recursion, including the antipodal lower law when n=3. -/
theorem hasDerivAt_simplex_cdf {n : ℕ} (hn : 3 ≤ n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (cdf (simplex n))
      ((n : ℝ) * WeakSimplex.normalPDF t *
        cdf (simplex (n - 1)) (t * Real.sqrt ((n : ℝ) / ((n : ℝ) - 2)))) t := by
  have h := hasDerivAt_simplex_cdf_succ (by omega : 2 ≤ n - 1) t ht
  have hn1 : (n - 1 : ℕ) + 1 = n := by omega
  convert! h using 1
  · exact congrArg (fun k ↦ cdf (simplex k)) hn1.symm
  · rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have htwo : (n : ℝ) - 1 - 1 = (n : ℝ) - 2 := by ring
    rw [sub_add_cancel, htwo]

/-- Repeating existing unit normals gives an actual correlation law and leaves the event unchanged. -/
theorem exists_correlation_capMass {ι : Type*} [Fintype ι] [Nonempty ι]
    {d m : ℕ} (w : ι → Coord d) (hw : ∀ i, ‖w i‖ = 1)
    (hm : Fintype.card ι ≤ m) :
    ∃ G : Mat m, WeakSimplex.IsCorrelation G ∧
      ∀ t : ℝ, cdf G t = capMass w (fun _ ↦ t) := by
  obtain ⟨f, hf⟩ := exists_surjection_fin hm
  let v : Fin m → Coord d := w ∘ f
  refine ⟨WeakSimplex.codeGram v, WeakSimplex.codeGram_isCorrelation v (fun i ↦ hw (f i)), ?_⟩
  intro t
  have hmeas : Measurable (fun y : Coord d ↦
      WeakSimplex.Coord.ofFun fun i ↦ inner ℝ (v i) y) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin m ↦ ℝ)).measurable.comp
    exact measurable_pi_lambda _ fun i ↦ (continuous_const.inner continuous_id).measurable
  rw [cdf, ← WeakSimplex.map_codeScore_stdGaussian v,
    Measure.map_apply hmeas (WeakSimplex.measurableSet_lowerOrthant t)]
  change (stdGaussian (Coord d) (cap (w ∘ f) ((fun _ : ι ↦ t) ∘ f))).toReal = _
  rw [cap_reindex_surjective w (fun _ ↦ t) f hf]
  rfl

/-- The full lower-size comparison applies directly to a repeated support list. -/
theorem reference_floor_of_comparison {ι : Type*} [Fintype ι] [Nonempty ι]
    {d m : ℕ} (w : ι → Coord d) (hw : ∀ i, ‖w i‖ = 1)
    (hm : Fintype.card ι ≤ m) (r : ℝ)
    (hcompare : ∀ G : Mat m, WeakSimplex.IsCorrelation G → cdf (simplex m) r ≤ cdf G r) :
    cdf (simplex m) r ≤ capMass w (fun _ ↦ r) := by
  obtain ⟨G, hG, he⟩ := exists_correlation_capMass w hw hm
  rw [← he r]
  exact hcompare G hG

end FSC
