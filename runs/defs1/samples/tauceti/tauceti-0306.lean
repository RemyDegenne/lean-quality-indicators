public section

open CategoryTheory

open scoped Pointwise

universe w v u

namespace IsIdempotentElem

variable {A : Type u} [Ring A] {e : A} (he : IsIdempotentElem e)

/-- **The coinduction functor** `N ↦ Hom_{eAe}(eA, N)`, from modules over the corner ring `eAe`
to modules over `A`. -/
@[expose] def cornerCoindFunctor : ModuleCat.{max u v} he.Corner ⥤ ModuleCat.{max u v} A where
  obj N := ModuleCat.of A (↥(e • (⊤ : Submodule ℤ A)) →ₗ[he.Corner] N)
  map g := ModuleCat.ofHom
    { toFun := fun f ↦ g.hom ∘ₗ f
      map_add' := fun f f' ↦ LinearMap.comp_add f f' g.hom
      map_smul' := fun _ _ ↦ rfl }

end IsIdempotentElem
end
