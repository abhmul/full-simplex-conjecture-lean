import FSC.Definitions
import WeakSimplexConjectureLean.Maxima.CoordinateMax

/-! Exact finite-maximum event and tail dictionaries for the actual Gaussian probability. -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FSC

theorem coordinateMax_le_event {n : ℕ} (hn : 0 < n) (t : ℝ) :
    {x : Coord n | WeakSimplex.coordinateMax hn x ≤ t} = WeakSimplex.lowerOrthant t := by
  ext x
  exact WeakSimplex.coordinateMax_le_iff_mem_lowerOrthant hn x t

theorem measurableSet_coordinateMax_le {n : ℕ} (hn : 0 < n) (t : ℝ) :
    MeasurableSet {x : Coord n | WeakSimplex.coordinateMax hn x ≤ t} :=
  measurableSet_le (WeakSimplex.continuous_coordinateMax hn).measurable measurable_const

theorem coordinateMax_tail_event {n : ℕ} (hn : 0 < n) (t : ℝ) :
    {x : Coord n | t < WeakSimplex.coordinateMax hn x} = (WeakSimplex.lowerOrthant t)ᶜ := by
  rw [← coordinateMax_le_event hn t]
  ext x
  simp

/-- The public real CDF is exactly the probability of the finite maximum event. -/
theorem cdf_eq_probability_coordinateMax_le {n : ℕ} (hn : 0 < n) (G : Mat n) (t : ℝ) :
    cdf G t =
      (multivariateGaussian (0 : Coord n) G {x | WeakSimplex.coordinateMax hn x ≤ t}).toReal := by
  rw [coordinateMax_le_event]
  rfl

theorem probability_coordinateMax_tail {n : ℕ} (hn : 0 < n) (G : Mat n) (t : ℝ) :
    multivariateGaussian (0 : Coord n) G {x | t < WeakSimplex.coordinateMax hn x} =
      1 - multivariateGaussian (0 : Coord n) G (WeakSimplex.lowerOrthant t) := by
  rw [coordinateMax_tail_event, prob_compl_eq_one_sub]
  rw [← coordinateMax_le_event hn t]
  exact measurableSet_coordinateMax_le hn t

theorem probability_coordinateMax_tail_toReal {n : ℕ} (hn : 0 < n) (G : Mat n) (t : ℝ) :
    (multivariateGaussian (0 : Coord n) G {x | t < WeakSimplex.coordinateMax hn x}).toReal =
      1 - cdf G t := by
  have hs : MeasurableSet (WeakSimplex.lowerOrthant t : Set (Coord n)) := by
    rw [← coordinateMax_le_event hn t]
    exact measurableSet_coordinateMax_le hn t
  have h := prob_add_prob_compl (μ := multivariateGaussian (0 : Coord n) G) hs
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at hr
  rw [coordinateMax_tail_event]
  change _ = 1 - (multivariateGaussian (0 : Coord n) G (WeakSimplex.lowerOrthant t)).toReal
  linarith

theorem lowerOrthant_le_iff_cdf_le {n : ℕ} (G H : Mat n) (t : ℝ) :
    multivariateGaussian (0 : Coord n) G (WeakSimplex.lowerOrthant t) ≤
      multivariateGaussian (0 : Coord n) H (WeakSimplex.lowerOrthant t) ↔
        cdf G t ≤ cdf H t :=
  (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).symm

theorem coordinateMax_tail_le_iff_cdf_le {n : ℕ} (hn : 0 < n) (G H : Mat n) (t : ℝ) :
    multivariateGaussian (0 : Coord n) G {x | t < WeakSimplex.coordinateMax hn x} ≤
      multivariateGaussian (0 : Coord n) H {x | t < WeakSimplex.coordinateMax hn x} ↔
        cdf H t ≤ cdf G t := by
  rw [← ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _),
    probability_coordinateMax_tail_toReal, probability_coordinateMax_tail_toReal]
  exact sub_le_sub_iff_left 1

theorem coordinateMax_tail_lt_iff_cdf_lt {n : ℕ} (hn : 0 < n) (G H : Mat n) (t : ℝ) :
    multivariateGaussian (0 : Coord n) G {x | t < WeakSimplex.coordinateMax hn x} <
      multivariateGaussian (0 : Coord n) H {x | t < WeakSimplex.coordinateMax hn x} ↔
        cdf H t < cdf G t := by
  rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _),
    probability_coordinateMax_tail_toReal, probability_coordinateMax_tail_toReal]
  exact sub_lt_sub_iff_left 1

theorem coordinateMax_tail_eq_iff_cdf_eq {n : ℕ} (hn : 0 < n) (G H : Mat n) (t : ℝ) :
    multivariateGaussian (0 : Coord n) G {x | t < WeakSimplex.coordinateMax hn x} =
      multivariateGaussian (0 : Coord n) H {x | t < WeakSimplex.coordinateMax hn x} ↔
        cdf G t = cdf H t := by
  simp only [le_antisymm_iff, coordinateMax_tail_le_iff_cdf_le hn]
  exact and_comm

end FSC
