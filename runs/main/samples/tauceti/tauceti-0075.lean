public section

open CategoryTheory Opposite Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace LocallyRingedSpace.Hom

variable {X Y Z : LocallyRingedSpace.{u}}

section Desc

variable (c : X ⟶ Y) (hq : IsQuotientMap c.base) (hc : ∀ U, IsIso (c.c.app U)) (h : X ⟶ Z)
  (hh : Function.FactorsThrough h.base c.base)

include hh in
theorem factorsThrough_comp_of_commSq {X' Y' : LocallyRingedSpace.{u}} {c' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y} (sq : CommSq u c' c v) :
    Function.FactorsThrough (u ≫ h).base c'.base := fun a b e ↦ by
  simp only [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply]
  refine hh ?_
  simpa only [← ConcreteCategory.comp_apply, ← LocallyRingedSpace.comp_base, sq.w]
    using congr(v.base $e)

end Desc
end LocallyRingedSpace.Hom
end AlgebraicGeometry
end
