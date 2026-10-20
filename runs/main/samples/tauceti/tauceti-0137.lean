public section

open CategoryTheory Equiv

universe u

namespace TauCeti

variable {X Y Z : TopCat.{u}}

namespace ConnectedCoveringSpace

variable (h : X ≃ₜ Y) (c : ConnectedCoveringSpace Y)

variable {x : X} {y : Y} (hx : h x = y)

@[simp]
theorem pullbackFiberEquiv_symm_apply_coe (e : ⇑c.proj ⁻¹' {y}) :
    ((pullbackFiberEquiv h c hx).symm e : ((pullback h).obj c : TopCat)) = (e : (c : TopCat)) :=
  (rfl)

end ConnectedCoveringSpace
end TauCeti
end
