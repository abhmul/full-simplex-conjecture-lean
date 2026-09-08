import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Shared second-order expansion, with a vector-domain remainder and no regularity oracle. -/

open scoped Topology

namespace FSC

def Peano2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (x : V) (l : V →L[ℝ] ℝ) (B : V →L[ℝ] V →L[ℝ] ℝ) : Prop :=
  Asymptotics.IsLittleO (𝓝 (0 : V))
    (fun h ↦ f (x + h) - f x - l h - (1 / 2 : ℝ) * B h h)
    (fun h ↦ ‖h‖ ^ 2)

end FSC
