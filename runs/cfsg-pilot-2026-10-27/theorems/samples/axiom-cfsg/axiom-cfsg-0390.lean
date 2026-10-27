public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

namespace E8Layer

open CFSG.LieType.Steinberg CFSG.Open CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.LieType.CurtisTits

open CFSG.ClassicalInvolution.Generic (Commutes)

open scoped commutatorElement

open CFSG.Timmesfeld TauCeti CFSG.RankThree.PartOne.KE CFSG.ComponentClassification.CatLeafProof

open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section Adj

theorem e8E6_nadj : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
    e8E6Node i ≠ e8E6Node j ∧ Tag.cartan .E8 (e8E6Node i) (e8E6Node j) = 0 ∧
    Tag.cartan .E8 (e8E6Node j) (e8E6Node i) = 0 := by
  decide

end Adj
end E8Layer
end CFSG.LieType.SeitzGeneration.ExcHigh
end
