@[expose] public section

open CategoryTheory

open scoped Simplicial

namespace SemiSimplexCategory

scoped[Simplicial] notation "⦋" n "⦌ₛ" => SemiSimplexCategory.mk n

/-- The inclusion functor `SemiSimplexCategory ⥤ SimplexCategory`. -/
def toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv f).toOrderHom

end SemiSimplexCategory
end
