@[expose] public section

universe v₁ v₂ u u₁ u₂

namespace Prefunctor

/-- The identity morphism between quivers. -/
@[simps]
def id (V : Type*) [Quiver V] : Prefunctor V V where
  obj := fun X => X
  map f := f

end Prefunctor
end
