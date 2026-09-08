import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Componentwise quadratic comparison

Source: `docs/sources/COMPONENTWISE_COMPARISON.md`, section 1, and the reviewed scalar contracts in `docs/pro-return/INTERFACES.md`. Every component has a strictly positive remainder. No Gaussian hypothesis enters this finite scalar theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace FSC

/-- Exact two-component quadratic loss. -/
theorem quadratic_remainder (u e U E : ℝ)
    (hU : U ≠ 0) (hE : E ≠ 0) (hX : U + E ≠ 0) :
    u ^ 2 / U + e ^ 2 / E - (u + e) ^ 2 / (U + E) =
      (E * u - U * e) ^ 2 / ((U + E) * U * E) := by
  field_simp [hU, hE, hX]
  ring

/-- Quadratic-over-linear convexity with its two positive denominators explicit. -/
theorem quadratic_split_le (u e U E : ℝ) (hU : 0 < U) (hE : 0 < E) :
    (u + e) ^ 2 / (U + E) ≤ u ^ 2 / U + e ^ 2 / E := by
  have hX : 0 < U + E := add_pos hU hE
  have hR := quadratic_remainder u e U E hU.ne' hE.ne' hX.ne'
  have hnonneg : 0 ≤ (E * u - U * e) ^ 2 / ((U + E) * U * E) :=
    div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (mul_pos hX hU) hE))
  linarith

/-- The full finite componentwise comparison, with positive occupied components. -/
theorem componentwise_compare
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u e omega : ι → ℝ) (M : ℝ)
    (hu : ∀ i, 0 < u i) (he : ∀ i, 0 < e i)
    (ho : ∀ i, 0 < omega i) (hM : 0 < M)
    (homega : ∑ i, omega i = 1)
    (hcomp : ∀ i,
      (u i + e i) ^ 2 / M - (u i) ^ 2 / (∑ j, u j) ≥ omega i * e i) :
    M ≤ ∑ i, (u i + e i) := by
  classical
  let U := ∑ i, u i
  let E := ∑ i, e i
  have hU : 0 < U := Finset.sum_pos (fun i _ ↦ hu i) Finset.univ_nonempty
  have hE : 0 < E := Finset.sum_pos (fun i _ ↦ he i) Finset.univ_nonempty
  have hX : 0 < U + E := add_pos hU hE
  rw [Finset.sum_add_distrib]
  change M ≤ U + E
  by_contra h
  have hXM : U + E < M := lt_of_not_ge h
  have hstrict (i : ι) : omega i < e i / E := by
    have hsplit := quadratic_split_le (u i) (e i) U E hU hE
    have hc : omega i * e i ≤ (u i + e i) ^ 2 / M - (u i) ^ 2 / U := hcomp i
    have hquot : 0 < (u i + e i) ^ 2 / M :=
      lt_of_lt_of_le (mul_pos (ho i) (he i))
        (hc.trans (sub_le_self _ (div_nonneg (sq_nonneg _) hU.le)))
    have hsq : 0 < (u i + e i) ^ 2 := (div_pos_iff_of_pos_right hM).1 hquot
    have hdiv : (u i + e i) ^ 2 / M < (u i + e i) ^ 2 / (U + E) :=
      div_lt_div_of_pos_left hsq hX hXM
    have hh : omega i * e i < (e i / E) * e i := by
      calc
        omega i * e i < (e i) ^ 2 / E := by linarith
        _ = (e i / E) * e i := by ring
    exact (mul_lt_mul_iff_left₀ (he i)).1 (by simpa only [mul_comm] using hh)
  have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun i _ ↦ hstrict i)
  rw [homega, ← Finset.sum_div] at hsum
  change 1 < E / E at hsum
  rw [div_self hE.ne'] at hsum
  exact (lt_irrefl 1) hsum

/-- Equality identifies both normalized masses and every component mass. -/
theorem componentwise_equality
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (u e omega : ι → ℝ) (M : ℝ)
    (hu : ∀ i, 0 < u i) (he : ∀ i, 0 < e i)
    (_ho : ∀ i, 0 < omega i) (hM : 0 < M)
    (homega : ∑ i, omega i = 1)
    (hcomp : ∀ i,
      (u i + e i) ^ 2 / M - (u i) ^ 2 / (∑ j, u j) ≥ omega i * e i)
    (heq : ∑ i, (u i + e i) = M) :
    ∀ i, u i / (∑ j, u j) = omega i ∧
      e i / (∑ j, e j) = omega i ∧ u i + e i = M * omega i := by
  classical
  let U := ∑ i, u i
  let E := ∑ i, e i
  have hU : 0 < U := Finset.sum_pos (fun i _ ↦ hu i) Finset.univ_nonempty
  have hE : 0 < E := Finset.sum_pos (fun i _ ↦ he i) Finset.univ_nonempty
  have hXE : U + E = M := by simpa only [U, E, Finset.sum_add_distrib] using heq
  have hX : 0 < U + E := hXE ▸ hM
  have hle (i : ι) : omega i ≤ e i / E := by
    have hsplit := quadratic_split_le (u i) (e i) U E hU hE
    have hc : omega i * e i ≤ (u i + e i) ^ 2 / (U + E) - (u i) ^ 2 / U := by
      simpa only [hXE, U] using hcomp i
    have hh : omega i * e i ≤ (e i / E) * e i := by
      calc
        omega i * e i ≤ (e i) ^ 2 / E := by linarith
        _ = (e i / E) * e i := by ring
    exact (mul_le_mul_iff_left₀ (he i)).1 (by simpa only [mul_comm] using hh)
  have hsum : ∑ i, omega i = ∑ i, e i / E := by
    rw [homega, ← Finset.sum_div]
    exact (div_self hE.ne').symm
  have hnu (i : ι) : e i / E = omega i :=
    ((Finset.sum_eq_sum_iff_of_le (fun i _ ↦ hle i)).1 hsum i
      (Finset.mem_univ i)).symm
  intro i
  have hsplit := quadratic_split_le (u i) (e i) U E hU hE
  have hc : omega i * e i ≤ (u i + e i) ^ 2 / (U + E) - (u i) ^ 2 / U := by
    simpa only [hXE, U] using hcomp i
  have heprod : (e i) ^ 2 / E = omega i * e i := by
    calc
      (e i) ^ 2 / E = (e i / E) * e i := by ring
      _ = omega i * e i := by rw [hnu i]
  have hzero : (E * u i - U * e i) ^ 2 / ((U + E) * U * E) = 0 := by
    rw [← quadratic_remainder (u i) (e i) U E hU.ne' hE.ne' hX.ne']
    linarith
  have hcross : E * u i - U * e i = 0 := by
    have hden : (U + E) * U * E ≠ 0 := (mul_pos (mul_pos hX hU) hE).ne'
    have hsquare : (E * u i - U * e i) ^ 2 = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right hden
    exact sq_eq_zero_iff.mp hsquare
  have hfrac : u i / U = e i / E := by
    apply (div_eq_div_iff hU.ne' hE.ne').2
    nlinarith only [hcross]
  have huomega : u i / U = omega i := hfrac.trans (hnu i)
  refine ⟨huomega, hnu i, ?_⟩
  have hui : u i = omega i * U := (div_eq_iff hU.ne').1 huomega
  have hei : e i = omega i * E := (div_eq_iff hE.ne').1 (hnu i)
  rw [hui, hei, ← hXE]
  ring

end FSC
