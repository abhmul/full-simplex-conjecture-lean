import FSC.Support.Differentiation
import FSC.LinearAlgebra.PaddedGram

/-! All-support cap mass depends only on the Gram matrix, including redundant and empty families. -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FSC

/-- Relabeling a finite family does not change its actual Gaussian cap. -/
theorem cap_reindex {d : ℕ} {ι κ : Type*} (e : ι ≃ κ)
    (w : κ → Coord d) (b : κ → ℝ) : cap (w ∘ e) (b ∘ e) = cap w b := by
  ext y
  simpa only [cap, Function.comp_def, Set.mem_setOf_eq] using
    (e.surjective.forall (p := fun k ↦ inner ℝ (w k) y ≤ b k)).symm

/-- A finite-index cap is exactly the threshold event under its Gaussian score law. -/
theorem capMass_eq_thresholdCDF_gram {d n : ℕ} (w : Fin n → Coord d) (b : Fin n → ℝ) :
    capMass w b = thresholdCDF (Matrix.gram ℝ w) (WeakSimplex.Coord.ofFun b) := by
  rw [thresholdCDF, ← map_score_stdGaussian_of_gram w (Matrix.gram ℝ w) rfl,
    Measure.map_apply (by unfold WeakSimplex.Coord.ofFun; fun_prop)
      (measurableSet_thresholdEvent _)]
  rfl

/-- Equal Gram matrices imply equal cap masses at every listed support, in different dimensions. -/
theorem capMass_eq_of_gram {d e : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → Coord d) (w : ι → Coord e)
    (hgram : Matrix.gram ℝ v = Matrix.gram ℝ w) (b : ι → ℝ) :
    capMass v b = capMass w b := by
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hrel : Matrix.gram ℝ (v ∘ f) = Matrix.gram ℝ (w ∘ f) := by
    ext i j
    exact congrFun (congrFun hgram (f i)) (f j)
  have hv : capMass (v ∘ f) (b ∘ f) = capMass v b := by
    unfold capMass
    rw [cap_reindex]
  have hw : capMass (w ∘ f) (b ∘ f) = capMass w b := by
    unfold capMass
    rw [cap_reindex]
  rw [← hv, ← hw, capMass_eq_thresholdCDF_gram, capMass_eq_thresholdCDF_gram, hrel]

/-- Norms are determined by the diagonal of a Gram matrix. -/
theorem norm_eq_of_gram {d e : ℕ} {ι : Type*}
    {v : ι → Coord d} {w : ι → Coord e}
    (hgram : Matrix.gram ℝ v = Matrix.gram ℝ w) (i : ι) : ‖v i‖ = ‖w i‖ := by
  have h := congrFun (congrFun hgram i) i
  simp only [Matrix.gram_apply, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (v i), norm_nonneg (w i)]

/-- Coincident-boundary exclusions transport across unit-normal Gram realizations. -/
theorem NoCoincident.of_gram {d e : ℕ} {ι : Type*}
    {v : ι → Coord d} {w : ι → Coord e} {b : ι → ℝ}
    (hb : NoCoincident w b) (hw : ∀ i, ‖w i‖ = 1)
    (hgram : Matrix.gram ℝ v = Matrix.gram ℝ w) : NoCoincident v b := by
  have hv (i : ι) : ‖v i‖ = 1 := (norm_eq_of_gram hgram i).trans (hw i)
  intro i j hij
  have hg : inner ℝ (v i) (v j) = inner ℝ (w i) (w j) :=
    congrFun (congrFun hgram i) j
  constructor
  · intro he
    apply (hb i j hij).1
    apply (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) (hw i) (hw j)).mp
    rw [← hg]
    exact (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) (hv i) (hv j)).mpr he
  · intro he
    apply (hb i j hij).2
    apply (inner_eq_neg_one_iff_of_norm_eq_one (𝕜 := ℝ) (hw i) (hw j)).mp
    rw [← hg]
    exact (inner_eq_neg_one_iff_of_norm_eq_one (𝕜 := ℝ) (hv i) (hv j)).mpr he

/-- The actual canonical slice gradient agrees across unit-normal Gram realizations. -/
theorem supportGradient_eq_of_gram {d e : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Coord d) (w : ι → Coord e)
    (hw : ∀ i, ‖w i‖ = 1) (hgram : Matrix.gram ℝ v = Matrix.gram ℝ w)
    (b : ι → ℝ) (hb : NoCoincident w b) : supportGradient v b = supportGradient w b := by
  have hv (i : ι) : ‖v i‖ = 1 := (norm_eq_of_gram hgram i).trans (hw i)
  have heq : capMass v = capMass w := funext (capMass_eq_of_gram v w hgram)
  have hd := hasFDerivAt_capMass v hv b (hb.of_gram hw hgram)
  rw [heq] at hd
  exact hd.unique (hasFDerivAt_capMass w hw b hb)

end FSC
