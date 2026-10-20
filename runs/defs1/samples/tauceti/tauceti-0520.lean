public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

/-- The comparison map `ΩΣX ⟶ X`, induced on kernels by the chosen middle map. It is the
inverse of `toLoopSuspension` in the stable category. -/
noncomputable def fromLoopSuspension (X : C) :
    hE.enoughProjectives.loopObj (hE.suspensionObj X) ⟶ X :=
  (E.isKernelCokernelPair _ (hE.suspensionPresentation X).conflation).lift
    (hE.enoughProjectives.loopInflation _ ≫ loopSuspensionInvMiddleMap hE X) (by
      rw [Category.assoc, loopSuspensionInvMiddleMap_comp_suspensionDeflation hE,
        hE.enoughProjectives.loopInflation_comp_loopDeflation])

end ExactStructure.IsFrobenius
end TauCeti
end
