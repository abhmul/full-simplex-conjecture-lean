import FSC.Gaussian.PairWeights
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.Bases

open MeasureTheory

#synth TopologicalSpace (ProbabilityMeasure (FSC.Coord 3))
instance (n : ℕ) : FirstCountableTopology (FSC.Mat n) :=
  inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))
#synth FirstCountableTopology (FSC.Mat 3)
#synth FirstCountableTopology {G : Fin 3 → Fin 3 → ℝ // WeakSimplex.IsCorrelation G}
#check TopologicalSpace.Subtype.firstCountableTopology
example (n : ℕ) : FirstCountableTopology {G : FSC.Mat n // WeakSimplex.IsCorrelation G} :=
  TopologicalSpace.Subtype.firstCountableTopology (s := {G : FSC.Mat n | WeakSimplex.IsCorrelation G})
instance (n : ℕ) : FirstCountableTopology {G : FSC.Mat n // WeakSimplex.IsCorrelation G} :=
  TopologicalSpace.Subtype.firstCountableTopology (s := {G : FSC.Mat n | WeakSimplex.IsCorrelation G})
#synth FirstCountableTopology {G : FSC.Mat 3 // WeakSimplex.IsCorrelation G}
#synth SequentialSpace (FSC.Coord 3)
#synth SequentialSpace ({G : FSC.Mat 3 // WeakSimplex.IsCorrelation G} × FSC.Coord 3)

variable (n : ℕ)
#synth FirstCountableTopology (FSC.Mat n)
#synth SequentialSpace (FSC.Coord n)
#synth SequentialSpace ({G : FSC.Mat n // WeakSimplex.IsCorrelation G} × FSC.Coord n)
