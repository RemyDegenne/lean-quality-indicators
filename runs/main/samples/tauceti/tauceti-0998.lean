public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

theorem projectiveStableFunctor_map_fromLoopSuspension_comp_toLoopSuspension (X : C) :
    E.projectiveStableFunctor.map (hE.fromLoopSuspension X ≫ hE.toLoopSuspension X) = 𝟙 _ := by
  let hS := hE.enoughProjectives.conflation_loopInflation_loopDeflation (hE.suspensionObj X)
  let φ : ShortComplex.mk _ _
        (hE.enoughProjectives.loopInflation_comp_loopDeflation (hE.suspensionObj X)) ⟶
      ShortComplex.mk _ _
        (hE.enoughProjectives.loopInflation_comp_loopDeflation (hE.suspensionObj X)) :=
    { τ₁ := hE.fromLoopSuspension X ≫ hE.toLoopSuspension X
      τ₂ := loopSuspensionInvMiddleMap hE X ≫ loopSuspensionMiddleMap hE X
      τ₃ := 𝟙 _
      comm₁₂ := by simp
      comm₂₃ := by simp }
  simpa [φ] using E.projectiveStableFunctor_map_τ₁_eq_of_τ₃_eq hS
    (hE.enoughProjectives.isProjective_loopProjective _) (φ := φ) (ψ := 𝟙 _) rfl

end ExactStructure.IsFrobenius
end TauCeti
end
