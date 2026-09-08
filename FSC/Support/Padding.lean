import FSC.Support.Dilation
import WeakSimplexConjectureLean.Normal.TruncatedMoments

/-! Exact second moments for Gaussian padding; the full ambient norm is retained. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FSC

abbrev splitCoords (d k : ℕ) : Coord (d + k) ≃L[ℝ] Coord d × Coord k :=
  EuclideanSpace.finAddEquivProd

theorem splitCoords_fst {d k : ℕ} (y : Coord (d + k)) (i : Fin d) :
    (splitCoords d k y).1 i = y (Fin.castAdd k i) := rfl

theorem splitCoords_snd {d k : ℕ} (y : Coord (d + k)) (i : Fin k) :
    (splitCoords d k y).2 i = y (Fin.natAdd d i) := rfl

theorem norm_sq_splitCoords {d k : ℕ} (y : Coord (d + k)) :
    ‖y‖ ^ 2 = ‖(splitCoords d k y).1‖ ^ 2 + ‖(splitCoords d k y).2‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, splitCoords_fst, splitCoords_snd,
    Fin.sum_univ_add]

theorem map_splitCoords_stdGaussian (d k : ℕ) :
    (stdGaussian (Coord (d + k))).map (splitCoords d k) =
      (stdGaussian (Coord d)).prod (stdGaussian (Coord k)) := by
  have hc := measurePreserving_piCongrLeft
    (fun _ : Fin d ⊕ Fin k ↦ gaussianReal 0 1) finSumFinEquiv.symm
  have hs := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin d ⊕ Fin k ↦ gaussianReal 0 1)
  have hp := hs.comp hc
  have hm : MeasurePreserving (WithLp.toLp 2 : (Fin d → ℝ) → Coord d)
      (Measure.pi fun _ ↦ gaussianReal 0 1) (stdGaussian (Coord d)) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hk : MeasurePreserving (WithLp.toLp 2 : (Fin k → ℝ) → Coord k)
      (Measure.pi fun _ ↦ gaussianReal 0 1) (stdGaussian (Coord k)) :=
    ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have h := ((hm.prod hk).comp hp).map_eq
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  convert h using 2
  funext x
  apply Prod.ext <;> ext i <;>
    simp [Function.comp_def,
      MeasurableEquiv.coe_sumPiEquivProdPi, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply]

theorem inner_splitCoords {d k : ℕ} (x y : Coord (d + k)) :
    inner ℝ x y = inner ℝ (splitCoords d k x).1 (splitCoords d k y).1 +
      inner ℝ (splitCoords d k x).2 (splitCoords d k y).2 := by
  simp only [PiLp.inner_apply, splitCoords_fst, splitCoords_snd, Fin.sum_univ_add]

def padNormals {d : ℕ} {ι : Type*} (k : ℕ) (w : ι → Coord d) : ι → Coord (d + k) :=
  fun i ↦ (splitCoords d k).symm (w i, 0)

theorem inner_padNormals {d : ℕ} {ι : Type*} (k : ℕ) (w : ι → Coord d)
    (i : ι) (y : Coord (d + k)) :
    inner ℝ (padNormals k w i) y = inner ℝ (w i) (splitCoords d k y).1 := by
  rw [inner_splitCoords (padNormals k w i) y]
  have hp : splitCoords d k (padNormals k w i) = (w i, 0) :=
    (splitCoords d k).apply_symm_apply _
  rw [hp]
  simp only [inner_zero_left, add_zero]

theorem cap_padNormals {d : ℕ} {ι : Type*} (k : ℕ) (w : ι → Coord d) (b : ι → ℝ) :
    cap (padNormals k w) b = (splitCoords d k) ⁻¹' (cap w b ×ˢ Set.univ) := by
  ext y
  simp [cap, inner_padNormals]

theorem capMass_padNormals {d : ℕ} {ι : Type*} [Fintype ι]
    (k : ℕ) (w : ι → Coord d) (b : ι → ℝ) :
    capMass (padNormals k w) b = capMass w b := by
  rw [capMass, cap_padNormals, ← Measure.map_apply (by fun_prop)
    ((measurableSet_cap w b).prod MeasurableSet.univ), map_splitCoords_stdGaussian,
    Measure.prod_prod, measure_univ, mul_one]
  rfl

theorem integral_sq_standardGaussianReal :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa using h

theorem integral_sq_norm_stdGaussian (d : ℕ) :
    ∫ y : Coord d, ‖y‖ ^ 2 ∂stdGaussian (Coord d) = d := by
  have hproj (i : Fin d) :
      MeasurePreserving (fun y : Coord d ↦ y i) (stdGaussian (Coord d))
        (gaussianReal 0 1) := by
    simpa using (measurePreserving_eval_multivariateGaussian
      (μ := (0 : Coord d)) (S := (1 : Mat d)) Matrix.PosSemidef.one (i := i))
  have hint (i : Fin d) :
      Integrable (fun y : Coord d ↦ (y i) ^ 2) (stdGaussian (Coord d)) := by
    exact (hproj i).integrable_comp_of_integrable
      ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq)
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ ↦ hint i)]
  have hcoord (i : Fin d) :
      ∫ y : Coord d, (y i) ^ 2 ∂stdGaussian (Coord d) = 1 := by
    have hmap := (hproj i).map_eq
    have h := integral_map (hproj i).measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ ↦ x ^ 2)
        (Measure.map (fun y : Coord d ↦ y i) (stdGaussian (Coord d))) by fun_prop)
    rw [hmap] at h
    exact h.symm.trans integral_sq_standardGaussianReal
  simp_rw [hcoord]
  simp

/-- Exact product-coordinate energy: every unused Gaussian direction contributes the cap mass.
The integrand is the sum of the two squared Euclidean norms, not the squared product supremum norm. -/
theorem integral_product_padded_energy (d k : ℕ) (A : Set (Coord d)) :
    (∫ p in A ×ˢ Set.univ, ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2
      ∂(stdGaussian (Coord d)).prod (stdGaussian (Coord k))) =
      (∫ x in A, ‖x‖ ^ 2 ∂stdGaussian (Coord d)) +
        (k : ℝ) * (stdGaussian (Coord d) A).toReal := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [integral_add
    ((integrable_sq_norm_stdGaussian d).restrict.comp_fst (stdGaussian (Coord k)))
    ((integrable_sq_norm_stdGaussian k).comp_snd ((stdGaussian (Coord d)).restrict A))]
  rw [integral_fun_fst (fun x : Coord d ↦ ‖x‖ ^ 2),
    integral_fun_snd (fun x : Coord k ↦ ‖x‖ ^ 2), integral_sq_norm_stdGaussian]
  simp [measureReal_def, mul_comm]

/-- Exact Euclidean padding, under the actual Gaussian law on the larger ambient space. -/
theorem capEnergy_padNormals {d : ℕ} {ι : Type*}
    (k : ℕ) (w : ι → Coord d) (b : ι → ℝ) :
    capEnergy (padNormals k w) b = capEnergy w b + (k : ℝ) * capMass w b := by
  have h := setIntegral_map_equiv
    ((splitCoords d k).toHomeomorph.toMeasurableEquiv)
    (μ := stdGaussian (Coord (d + k)))
    (fun p : Coord d × Coord k ↦ ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) (cap w b ×ˢ Set.univ)
  change (∫ p in cap w b ×ˢ Set.univ, ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2
    ∂(stdGaussian (Coord (d + k))).map (splitCoords d k)) =
    ∫ y in (splitCoords d k) ⁻¹' (cap w b ×ˢ Set.univ),
      ‖(splitCoords d k y).1‖ ^ 2 + ‖(splitCoords d k y).2‖ ^ 2
      ∂stdGaussian (Coord (d + k)) at h
  rw [map_splitCoords_stdGaussian, integral_product_padded_energy, ← cap_padNormals] at h
  simp_rw [← norm_sq_splitCoords] at h
  exact h.symm

end FSC
