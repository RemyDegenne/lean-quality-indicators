@[expose] public section

universe uR uM

open CategoryTheory

namespace ModuleCat

variable (R : Type uR) [Ring R]

/-- The contravariant dual of right modules over a fixed ring. Its values are
ordinary right-linear maps into `R`, with the canonical pointwise left action,
and its morphisms are precomposition.

The definition is reducible so that elements of its values inherit the ordinary
`LinearMap` coercion to functions. -/
@[reducible, simps obj_carrier]
def rightDual :
    (ModuleCat.{uM} Rᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max uR uM} R where
  obj X := ModuleCat.of R (X.unop →ₗ[Rᵐᵒᵖ] R)
  map h := ModuleCat.ofHom (LinearMap.lcomp R R h.unop.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    rfl
  map_comp h k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro z
    rfl

end ModuleCat
end
