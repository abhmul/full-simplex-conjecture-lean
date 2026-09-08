/- UNCOMPILED consultation probes. Complete proof attempts, not placeholders.
   These algebraic lemmas do not certify any Gaussian analytic interface. -/
import Mathlib

set_option autoImplicit false

namespace FSCProbes

theorem quadraticRemainder (u e U E : ℝ)
    (hU : U ≠ 0) (hE : E ≠ 0) (hX : U + E ≠ 0) :
    u ^ 2 / U + e ^ 2 / E - (u + e) ^ 2 / (U + E) =
      (E * u - U * e) ^ 2 / ((U + E) * U * E) := by
  field_simp [hU, hE, hX]
  <;> ring

theorem signedRowRemainder (n x a : ℝ) (hn : n ≠ 0) :
    (n - 2) * (1 - x) - (n * a - 1) =
      n / 2 * (1 - 2 * a - ((n - 2) / n) * x ^ 2) +
        (n - 2) / 2 * (1 - x) ^ 2 := by
  field_simp [hn]
  <;> ring

theorem pairPinOrthogonality (a b c : ℝ) (hc : 1 - c ^ 2 ≠ 0) :
    a - ((a - c * b) / (1 - c ^ 2) +
      (b - c * a) / (1 - c ^ 2) * c) = 0 := by
  field_simp [hc]
  <;> ring

theorem noiseDiagonalCancellation (t p l c q : ℝ) :
    (t * l * p + l * (-t * p - c * q)) / 2 = -(l * c * q) / 2 := by
  ring

theorem pairTraceNormalization (a b c q l : ℝ) :
    (2 * l * q - a * c * q - b * c * q) / 2 =
      q * (l - c * (a + b) / 2) := by
  ring

noncomputable def triangle (i : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2
    (![( ![(1 : ℝ), 0]), (![(0 : ℝ), 1]), (![-(3 / 5 : ℝ), 4 / 5])] i)

theorem triangleGramPSD : (Matrix.gram ℝ triangle).PosSemidef := by
  exact Matrix.posSemidef_gram ℝ triangle

theorem deterministicThirdBelow (t : ℝ) :
    -(3 / 5 : ℝ) * t + (4 / 5 : ℝ) * t = t / 5 := by
  ring

end FSCProbes
