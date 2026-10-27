public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits

theorem eq_zero_of_forall_e8D7Node_ne :
    ∀ i : Fin (Tag.rank .E8), (∀ k, e8D7Node k ≠ i) → i = e8Node 0 := by
  decide

end CFSG.ComponentClassification.CatLeafProof
end
