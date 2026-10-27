public section

namespace TauCeti

open CategoryTheory

universe u v

variable {A : Type u} [Ring A]

variable (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
  FiniteProjectivePresentation M.obj.as)

variable (Q : ∀ N : FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ,
  FiniteProjectivePresentation N.obj.as)

/-- The inverse transpose, with the cokernels of dual right presentations as its objects.
Fullness and faithfulness uniquely determine its maps from double-transpose recovery. -/
noncomputable def stableTransposeInverse :
    (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ ⥤
      FinitelyPresentedStableModule.{u, max u v} A where
  obj N := (Q N.unop).stableRightTransposeObj
  map {N L} f := (stableTransposeFunctor P).preimage
    (((Q N.unop).stableTransposeRightIso P).hom ≫ f ≫
      ((Q L.unop).stableTransposeRightIso P).inv)
  map_id N := by
    apply (stableTransposeFunctor P).map_injective
    simp
  map_comp f g := by
    apply (stableTransposeFunctor P).map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Category.assoc,
      Iso.inv_hom_id_assoc]

end TauCeti
end
