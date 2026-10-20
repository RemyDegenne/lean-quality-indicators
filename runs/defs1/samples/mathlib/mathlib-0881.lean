@[expose] public section

namespace CategoryTheory

universe v u v₁ v₂ u₁ u₂

namespace ReflQuiv

/-- The forgetful functor from categories to quivers. -/
@[simps]
def forgetToQuiv : ReflQuiv.{v, u} ⥤ Quiv.{v, u} where
  obj V := ↧V
  map F := F.toPrefunctor

end ReflQuiv
end CategoryTheory
end
