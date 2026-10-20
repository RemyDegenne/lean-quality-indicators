public section

open CategoryTheory

namespace TauCeti.SplitTorus

universe u v w

variable {sigma : Type u}

variable [Finite sigma]

section GroupScheme

variable (R : Type u) [CommRing R]

@[simp]
theorem relabel_one : relabel (sigma := sigma) R 1 = CategoryStruct.id _ := by
  rw [relabel, characterRelabelHom_one, DiagonalizableGroup.groupSchemeMap_id]

end GroupScheme
end TauCeti.SplitTorus
end
