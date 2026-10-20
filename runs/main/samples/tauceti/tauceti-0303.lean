public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) [Field k]

namespace GradedVectorSpace

@[simp]
theorem homUnitLinearEquiv_apply {V : GradedVectorSpace k} (f : unit k ⟶ V) :
    homUnitLinearEquiv k V f = (f 0).hom ((unitObjZeroLinearEquiv k).symm 1) := by
  simp [homUnitLinearEquiv, homUnitHomLinearEquiv_apply, unitObjZeroLinearEquiv]
  -- Mathlib has no simp lemma for `ModuleCat.homLinearEquiv`, which is `ModuleCat.Hom.hom` by
  -- definition.
  rfl

end GradedVectorSpace
end TauCeti
end
