import FSC.Definitions

/-! Public simplex correlation and zero-row-sum foundations from the pinned Gram normalization theorem. -/

noncomputable section

open Matrix
open scoped BigOperators

namespace FSC

theorem simplex_isCorrelation {n : ℕ} (hn : 2 ≤ n) : WeakSimplex.IsCorrelation (simplex n) := by
  have hI : WeakSimplex.IsCorrelation (1 : Mat n) :=
    ⟨Matrix.PosSemidef.one, fun i ↦ Matrix.one_apply_eq i⟩
  exact (WeakSimplex.gramNormalization (by omega) (1 : Mat n) hI).2.1

theorem simplex_sum_row {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    ∑ j, simplex n i j = 0 := by
  rw [simplex_eq_scaled_matrix hn]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    WeakSimplex.allOnesMatrix_apply]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Matrix.one_apply]

theorem simplex_sum_column {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    ∑ i, simplex n i j = 0 := by
  have hsym (i : Fin n) : simplex n i j = simplex n j i := by
    simpa only [star_trivial] using (simplex_isCorrelation hn).1.isHermitian.apply j i
  simp_rw [hsym]
  exact simplex_sum_row hn j

end FSC
