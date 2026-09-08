import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! The compact strict linear barrier of the reviewed dossier. No envelope is differentiated. -/

open Set
open scoped Topology

namespace FSC

theorem compact_slope_comparison
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : K → ℝ → ℝ) (D d : ℝ → ℝ)
    (hf : Continuous (fun p : K × ℝ ↦ f p.1 p.2))
    (hD : Continuous D)
    (hf_bounds : ∀ k t, 0 ≤ f k t ∧ f k t ≤ 1)
    (hD_bounds : ∀ t, 0 ≤ D t ∧ D t ≤ 1)
    (hD_zero : D 0 = 0)
    (hD_deriv : ∀ t, 0 < t → HasDerivAt D (d t) t)
    (hmin_slope : ∀ k t, 0 < t →
      (∀ l, f k t ≤ f l t) →
      ∃ v : ℝ, HasDerivAt (f k) v t ∧ d t ≤ v) :
    ∀ k t, 0 ≤ t → D t ≤ f k t := by
  intro k₀ t₀ ht₀
  by_contra hfail
  have hgap : f k₀ t₀ < D t₀ := lt_of_not_ge hfail
  have ht₀pos : 0 < t₀ := by
    rcases ht₀.eq_or_lt with h | h
    · have hb := (hf_bounds k₀ 0).1
      subst t₀
      rw [hD_zero] at hgap
      linarith
    · exact h
  let ε : ℝ := (D t₀ - f k₀ t₀) / (2 * t₀)
  have hε : 0 < ε := div_pos (sub_pos.mpr hgap) (mul_pos (by norm_num) ht₀pos)
  have hεeq : ε * (2 * t₀) = D t₀ - f k₀ t₀ :=
    div_mul_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) ht₀pos))
  let T : ℝ := t₀ + 2 / ε
  have hT : t₀ < T := lt_add_of_pos_right _ (div_pos (by norm_num) hε)
  have hTpos : 0 < T := ht₀pos.trans hT
  have hεT : 1 < ε * T := by
    have hc : ε * (2 / ε) = 2 := mul_div_cancel₀ _ hε.ne'
    dsimp [T]
    nlinarith [mul_pos hε ht₀pos]
  let ψ : K × ℝ → ℝ := fun p ↦ f p.1 p.2 - D p.2 + ε * p.2
  have hψ : Continuous ψ :=
    (hf.sub (hD.comp continuous_snd)).add (continuous_const.mul continuous_snd)
  have hcompact : IsCompact ((univ : Set K) ×ˢ Icc (0 : ℝ) T) :=
    isCompact_univ.prod isCompact_Icc
  have hnonempty : ((univ : Set K) ×ˢ Icc (0 : ℝ) T).Nonempty :=
    ⟨(k₀, t₀), trivial, ht₀, hT.le⟩
  obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn hnonempty hψ.continuousOn
  have hnegative : ψ p < 0 := by
    have hle := hmin (show (k₀, t₀) ∈ (univ : Set K) ×ˢ Icc (0 : ℝ) T from
      ⟨trivial, ht₀, hT.le⟩)
    have hψ₀ : ψ (k₀, t₀) < 0 := by
      dsimp [ψ]
      nlinarith
    exact hle.trans_lt hψ₀
  have htp : 0 < p.2 := by
    have hnonneg := hp.2.1
    rcases hnonneg.eq_or_lt with hz | hz
    · have hf0 := (hf_bounds p.1 0).1
      have heq : ψ p = f p.1 0 := by simp [ψ, ← hz, hD_zero]
      rw [heq] at hnegative
      linarith
    · exact hz
  have hpt : p.2 < T := by
    have hle := hp.2.2
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · have hfT := (hf_bounds p.1 T).1
      have hdT := (hD_bounds T).2
      have hψT : ψ p = f p.1 T - D T + ε * T := by simp [ψ, heq]
      rw [hψT] at hnegative
      linarith
  have hshape : ∀ l, f p.1 p.2 ≤ f l p.2 := by
    intro l
    have hle := hmin (show (l, p.2) ∈ (univ : Set K) ×ˢ Icc (0 : ℝ) T from
      ⟨trivial, hp.2⟩)
    dsimp [ψ] at hle
    linarith
  obtain ⟨v, hv, hdv⟩ := hmin_slope p.1 p.2 htp hshape
  have hfixed : IsMinOn (fun t ↦ ψ (p.1, t)) (Icc (0 : ℝ) T) p.2 := by
    intro t ht
    exact hmin (show (p.1, t) ∈ (univ : Set K) ×ˢ Icc (0 : ℝ) T from ⟨trivial, ht⟩)
  have hlocal : IsLocalMin (fun t ↦ ψ (p.1, t)) p.2 :=
    hfixed.isLocalMin (Icc_mem_nhds htp hpt)
  have hderiv : HasDerivAt (fun t ↦ ψ (p.1, t)) (v - d p.2 + ε) p.2 := by
    have hlin : HasDerivAt (fun t : ℝ ↦ ε * t) ε p.2 :=
      (hasDerivAt_id p.2).const_mul ε |>.congr_deriv (mul_one ε)
    exact (hv.sub (hD_deriv p.2 htp)).add hlin
  have hz := hlocal.deriv_eq_zero
  rw [hderiv.deriv] at hz
  linarith

/-- After comparison, a positive-threshold contact forces equality of fixed-shape slopes. -/
theorem slope_eq_of_touch
    (f D : ℝ → ℝ) (v d t : ℝ) (ht : 0 < t)
    (hcomp : ∀ s, 0 < s → D s ≤ f s)
    (heq : f t = D t) (hf : HasDerivAt f v t) (hD : HasDerivAt D d t) :
    v = d := by
  have hmin : IsMinOn (fun s ↦ f s - D s) (Ioi (0 : ℝ)) t := by
    intro s hs
    change f t - D t ≤ f s - D s
    rw [heq, sub_self]
    exact sub_nonneg.mpr (hcomp s hs)
  have hlocal := hmin.isLocalMin (Ioi_mem_nhds ht)
  have hz := hlocal.hasDerivAt_eq_zero (hf.sub hD)
  exact sub_eq_zero.mp hz

end FSC
