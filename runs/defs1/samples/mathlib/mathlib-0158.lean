@[expose] public section

namespace CategoryTheory

universe v u v₁ v₂ u₁ u₂

namespace ReflQuiv

/-- The underlying quiver of a reflexive quiver -/
def toQuiv (C : ReflQuiv.{v, u}) : Quiv.{v, u} := ↧C.α

end ReflQuiv
end CategoryTheory
end
