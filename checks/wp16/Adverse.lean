import FSC.Facet.Compatibility
import FSC.Support.Padding
import FSCProbes.SingularTriangle

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace BigOperators

namespace FSCChecks.WP16

open FSC

theorem gram_pad {d : ℕ} {ι : Type*} (k : ℕ) (w : ι → Coord d) :
    Matrix.gram ℝ (padNormals k w) = Matrix.gram ℝ w := by
  ext i j
  rw [Matrix.gram_apply, inner_padNormals]
  have he := (splitCoords d k).apply_symm_apply (w j, (0 : Coord k))
  change inner ℝ (w i) (splitCoords d k ((splitCoords d k).symm (w j, 0))).1 = _
  rw [he]
  rfl

theorem energy_eq_of_gram {d : ℕ} {ι : Type*} [Fintype ι]
    (v w : ι → Coord d) (hgram : Matrix.gram ℝ v = Matrix.gram ℝ w) (b : ι → ℝ) :
    capEnergy v b = capEnergy w b := by
  have he : capMass v = capMass w := funext (capMass_eq_of_gram v w hgram)
  have hv := hasDerivAt_capMass_dilate v b
  rw [he] at hv
  have hu := hv.unique (hasDerivAt_capMass_dilate w b)
  linarith

def squareNormals : Fin 4 → Coord 2 :=
  ![WeakSimplex.Coord.ofFun ![1, 0], WeakSimplex.Coord.ofFun ![0, 1],
    WeakSimplex.Coord.ofFun ![-1, 0], WeakSimplex.Coord.ofFun ![0, -1]]

def squareGram : Mat 4 := !![1, 0, -1, 0; 0, 1, 0, -1; -1, 0, 1, 0; 0, -1, 0, 1]

theorem square_gram : Matrix.gram ℝ squareNormals = squareGram := by
  ext i j
  simp only [Matrix.gram_apply, PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [squareNormals, squareGram, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk]

theorem square_correlation : WeakSimplex.IsCorrelation squareGram := by
  constructor
  · rw [← square_gram]
    exact Matrix.posSemidef_gram ℝ squareNormals
  · intro i
    fin_cases i <;> norm_num [squareGram, Matrix.cons_val, Fin.reduceFinMk]

theorem square_distinct : DistinctScores squareGram := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [squareGram, Matrix.cons_val, Fin.reduceFinMk] at *

theorem square_notPD : ¬squareGram.PosDef := by
  intro hp
  rw [← square_gram] at hp
  have h := (Matrix.linearIndependent_of_posDef_gram hp).fintype_card_le_finrank
  norm_num at h

def squareIntrinsic (j : RetainedPair squareGram 0) : Coord 1 :=
  WeakSimplex.Coord.ofFun fun _ ↦ squareNormals j 1

theorem square_intrinsic_gram :
    Matrix.gram ℝ squareIntrinsic = Matrix.gram ℝ (projectedNormal squareGram 0) := by
  rw [← gram_realizationProjectedNormal squareNormals squareGram square_correlation.1 square_gram 0]
  ext ⟨j, hj⟩ ⟨k, hk⟩
  simp only [Matrix.gram_apply, squareIntrinsic, realizationProjectedNormal, PiLp.inner_apply]
  fin_cases j <;> fin_cases k <;>
    norm_num [pairSigma, squareNormals, squareGram, Fin.sum_univ_succ,
      Matrix.cons_val, Fin.reduceFinMk] at *

theorem square_support (t : ℝ) (j : RetainedPair squareGram 0) :
    pairSupport squareGram t 0 j = t := by
  rcases j with ⟨j, hj⟩
  have hj' : j ≠ 0 ∧ -1 < squareGram 0 j ∧ squareGram 0 j < 1 := hj
  fin_cases j <;>
    norm_num [pairSupport, pairSigma, squareGram, Matrix.cons_val, Fin.reduceFinMk] at *

theorem square_intrinsic_interval (t : ℝ) :
    cap squareIntrinsic (fun _ ↦ t) = {y : Coord 1 | -t ≤ y 0 ∧ y 0 ≤ t} := by
  ext y
  constructor
  · intro hy
    have h₁ := hy (⟨1, by norm_num [squareGram, Matrix.cons_val, Fin.reduceFinMk]⟩ : RetainedPair squareGram 0)
    have h₃ := hy (⟨⟨3, by omega⟩, by norm_num [squareGram, Matrix.cons_val]⟩ : RetainedPair squareGram 0)
    simp [squareIntrinsic, squareNormals, PiLp.inner_apply, Matrix.cons_val] at h₁ h₃
    exact ⟨by linarith, h₁⟩
  · intro hy ⟨j, hj⟩
    fin_cases j <;>
      simp_all [squareIntrinsic, squareNormals, PiLp.inner_apply,
        Matrix.cons_val, Fin.reduceFinMk] <;> linarith [hy.1, hy.2]

/-- The chosen physical padded facet has the full interval energy plus one cap mass. -/
theorem square_actual_padding (v : Fin 4 → Coord 3) (hv : ∀ i, ‖v i‖ = 1)
    (hgram : Matrix.gram ℝ v = squareGram) (t : ℝ) :
    capEnergy (paddedFacetNormal (by norm_num) v hv squareGram square_correlation hgram 0)
      (fun j ↦ pairSupport squareGram t 0 j) =
      capEnergy squareIntrinsic (fun _ ↦ t) + capMass squareIntrinsic (fun _ ↦ t) := by
  have hg : Matrix.gram ℝ
      (paddedFacetNormal (by norm_num) v hv squareGram square_correlation hgram 0) =
      Matrix.gram ℝ (padNormals 1 squareIntrinsic) := by
    rw [gram_paddedFacetNormal, gram_pad, square_intrinsic_gram]
  rw [funext (square_support t), energy_eq_of_gram _ _ hg, capEnergy_padNormals]
  norm_num

theorem square_positive_energy_part (t : ℝ) (ht : 0 < t) (i : Fin 4) :
    0 < singlePinMass squareGram t i - facetPressure squareGram t i :=
  singlePinMass_sub_pressure_pos (by norm_num) squareGram square_correlation square_distinct
    square_notPD t ht i

def planarNormals : Fin 5 → Coord 2 :=
  ![WeakSimplex.Coord.ofFun ![1, 0], WeakSimplex.Coord.ofFun ![0, 1],
    WeakSimplex.Coord.ofFun ![3 / 5, 4 / 5], WeakSimplex.Coord.ofFun ![-1, 0],
    WeakSimplex.Coord.ofFun ![0, -1]]

def planarGram : Mat 5 := Matrix.gram ℝ planarNormals

theorem planar_correlation : WeakSimplex.IsCorrelation planarGram := by
  constructor
  · exact Matrix.posSemidef_gram ℝ planarNormals
  · intro i
    simp only [planarGram, Matrix.gram_apply, PiLp.inner_apply]
    fin_cases i <;>
      norm_num [planarNormals, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk]

theorem planar_distinct : DistinctScores planarGram := by
  intro i j hij
  simp only [planarGram, Matrix.gram_apply, PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [planarNormals, Fin.sum_univ_succ, Matrix.cons_val, Fin.reduceFinMk] at *

theorem planar_notPD : ¬planarGram.PosDef := by
  intro hp
  have h := (Matrix.linearIndependent_of_posDef_gram hp).fintype_card_le_finrank
  norm_num at h

/-- The actual five-direction law, with redundant and antipodal projected faces, pays its energy. -/
theorem planar_positive_energy_part (t : ℝ) (ht : 0 < t) (i : Fin 5) :
    0 < singlePinMass planarGram t i - facetPressure planarGram t i :=
  singlePinMass_sub_pressure_pos (by norm_num) planarGram planar_correlation planar_distinct
    planar_notPD t ht i

/-- Rank-two n=5 data uses all three tangent dimensions in the actual integral. -/
theorem planar_padded_components (t : ℝ) (ht : 0 < t) :
    ∃ v : Fin 5 → Coord 4, ∃ hv : ∀ i, ‖v i‖ = 1, ∃ hgram : Matrix.gram ℝ v = planarGram,
      ∀ i, singlePinMass planarGram t i = facetPressure planarGram t i +
        capEnergy (paddedFacetNormal (by norm_num) v hv planarGram planar_correlation hgram i)
          (fun j ↦ pairSupport planarGram t i j) / 3 := by
  obtain ⟨v, hv, hgram⟩ := exists_padded_unit_gram (by norm_num) planarGram planar_correlation
    planar_notPD
  refine ⟨v, hv, hgram, fun i ↦ ?_⟩
  simpa only [facetEnergy, Nat.reduceSub, Nat.cast_ofNat] using
    singlePinMass_eq_pressure_add_energy (by norm_num) v hv planarGram planar_correlation hgram
      planar_distinct t ht i

end FSCChecks.WP16

#print axioms FSCChecks.WP16.square_intrinsic_interval
#print axioms FSCChecks.WP16.square_actual_padding
#print axioms FSCChecks.WP16.square_positive_energy_part
#print axioms FSCChecks.WP16.planar_positive_energy_part
#print axioms FSCChecks.WP16.planar_padded_components
