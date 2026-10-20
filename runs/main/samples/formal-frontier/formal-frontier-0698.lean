@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

theorem sphere2NorthPunctured_contractibleSpace :
    ContractibleSpace
      ((TopologicalSpace.Opens.toTopCat sphere2).obj
        sphere2NorthPunctured : Type) :=
  sphere2NorthPuncturedHomeomorph.contractibleSpace_iff.mpr inferInstance

end SphereTopology
end
end
