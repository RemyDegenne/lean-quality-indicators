public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

open CFSG.RankThree.Classical2 (orthDerived)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)

open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)

open CFSG.Quasithin (perfectCore)

open CFSG.SeitzReduction.SymplecticPilot (diagSpEntry diagSpEntry_inl diagSpEntry_inr planeEnum
  planeEnum_injective)

open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section GLLevi

theorem plusFourRefinedF6OffInput_of_eigen (h : PlusFourGLLeviEigenInput) :
    PlusFourRefinedF6OffInput :=
  plusFourRefinedF6OffInput_of_GLLevi (plusFourGLLeviF6Input_of_eigen h)

end GLLevi
end CFSG.SeitzReduction.OmegaPilot
end
