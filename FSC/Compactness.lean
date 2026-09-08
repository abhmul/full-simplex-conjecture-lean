import FSC.Gaussian.CDFContinuity
import Mathlib.Topology.Order.Compact

/-! Closed and compact correlation matrices in the finite product topology. -/

noncomputable section

open Matrix Set

namespace FSC

theorem isClosed_posSemidef (n : ℕ) : IsClosed {G : Mat n | G.PosSemidef} := by
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · change IsClosed {G : Mat n | G.conjTranspose = G}
    exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    unfold dotProduct mulVec
    fun_prop

theorem isClosed_corrSet (n : ℕ) : IsClosed (CorrSet n) := by
  change IsClosed ({G : Mat n | G.PosSemidef} ∩ {G : Mat n | ∀ i, G i i = 1})
  refine (isClosed_posSemidef n).inter ?_
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i ↦ isClosed_eq (by fun_prop) continuous_const

theorem isCompact_corrSet (n : ℕ) : IsCompact (CorrSet n) := by
  have hbox : IsCompact (Set.univ.pi fun _ : Fin n ↦
      Set.univ.pi fun _ : Fin n ↦ Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_corrSet n)
  intro G hG i _ j _
  exact abs_le.mp (corr_entry_abs_le_one G hG i j)

theorem corrSet_nonempty (n : ℕ) : (CorrSet n).Nonempty :=
  ⟨1, Matrix.PosSemidef.one, fun i ↦ Matrix.one_apply_eq i⟩

theorem compactSpace_correlations (n : ℕ) :
    CompactSpace {G : Mat n // WeakSimplex.IsCorrelation G} :=
  isCompact_iff_compactSpace.mp (isCompact_corrSet n)

theorem continuousOn_cdf_correlations (n : ℕ) (t : ℝ) :
    ContinuousOn (fun G : Mat n ↦ cdf G t) (CorrSet n) := by
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun G : {G : Mat n // WeakSimplex.IsCorrelation G} ↦ cdf G.1 t)
  have hp : Continuous (fun G : {G : Mat n // WeakSimplex.IsCorrelation G} ↦ (G, t)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def, Set.restrict_apply] using
    (continuous_cdf_on_correlations (n := n)).comp hp

/-- Every real threshold has an actual minimizing correlation matrix, with singular and duplicate scores admitted. -/
theorem exists_cdf_minimizer (n : ℕ) (t : ℝ) :
    ∃ G : Mat n, WeakSimplex.IsCorrelation G ∧
      ∀ H : Mat n, WeakSimplex.IsCorrelation H → cdf G t ≤ cdf H t := by
  obtain ⟨G, hG, hmin⟩ := (isCompact_corrSet n).exists_isMinOn (corrSet_nonempty n)
    (continuousOn_cdf_correlations n t)
  exact ⟨G, hG, fun H hH ↦ hmin hH⟩

end FSC
