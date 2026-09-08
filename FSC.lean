import FSC.Definitions
import FSC.Gaussian.PinDefinitions
import FSC.Gaussian.AffineLaw
import FSC.Gaussian.IndependentSum
import FSC.Gaussian.SinglePin
import FSC.Gaussian.PairLaw
import FSC.Gaussian.PairWeights
import FSC.LinearAlgebra.Gram
import FSC.Support.Definitions
import FSC.Support.Dilation
import FSC.Support.Padding
import FSC.Analysis.Definitions
import FSC.Analysis.NoiseAveraging
import FSC.Analysis.PartialDerivatives
import FSC.Analysis.FinitePartialDerivatives
import FSC.Analysis.PeanoTaylor
import FSC.Scalar.Componentwise
import FSC.Threshold.LinearBarrier

/- Accepted foundations and generic theorems only. The all-dimensional FSC comparison
   and positive-threshold equality endpoints are not yet implemented. -/
