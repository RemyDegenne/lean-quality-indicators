public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SK

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LocalAnalysis.GLTheoremA.T263.DX

variable {n d : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
  {A : primeFormUnitary h (idGram K d)}

local notation "𝒜" => Matrix.GeneralLinearGroup.toLin ((A : GL (Fin d) K))

local notation "𝒳" => ((Matrix.GeneralLinearGroup.toLin ((A : GL (Fin d) K)) :
  LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K))

omit [Finite K] in
theorem unitaryBlockComponent_le_map_fix (a : K[X]) :
    KD264Lie.unitaryBlockComponent h (x := 𝒜) a ≤
      (fixSubgroup (primeFormConjSU h (idGram K d) A)).map
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K d)) d)) :=
  Subgroup.map_mono (unitaryPreimageBlock_le_fix h a)

end CFSG.LocalAnalysis.GLTheoremA.T263.SK
end
