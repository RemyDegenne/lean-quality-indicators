@[expose] public noncomputable section StdSimplexCoordinates

variable {ι : Type*} [Fintype ι]

variable {R : Type*}

open Convexity

section RealTopology

theorem isClosedEmbedding_stdSimplexCoordMap (i : ι) :
    Topology.IsClosedEmbedding (stdSimplexCoordMap (R := ℝ) i) :=
  (isClosed_stdSimplexAffineSet (ι := ι)).isClosedEmbedding_subtypeVal.comp
    (stdSimplexCoordHomeomorph i).isClosedEmbedding

end RealTopology
end StdSimplexCoordinates
