namespace OAI

namespace KadisonKastler

open Generator.Tracial UnitalTomsWinter

noncomputable section

universe u

section Represented

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [Nontrivial K] [TopologicalSpace.SeparableSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {ξ : K}

theorem PointedMatrixSites.constructed_represented_expected_matrix_subfactor
    (P : PointedMatrixSites N ξ twoRatioSiteParameter)
    (hIII : TypeIIIFactor (spatialProductAlgebra M N)) :
    Nonempty (ExpectedMatrixSubfactorModel (spatialProductAlgebra M N)) :=
  P.represented_expected_matrix_subfactor hIII (P.represented_state_homogeneity hIII)

end Represented
end
end KadisonKastler
end OAI
