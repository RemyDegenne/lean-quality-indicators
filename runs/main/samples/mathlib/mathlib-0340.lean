@[expose] public section

universe w w' v u

namespace CategoryTheory

namespace Precoverage

variable {C : Type u} [Category.{v} C]

section Functoriality

variable {D : Type*} [Category* D] {F : C ⥤ D}

variable {J K : Precoverage D}

open Limits

lemma comap_inf : (J ⊓ K).comap F = J.comap F ⊓ K.comap F := rfl

end Functoriality
end Precoverage
end CategoryTheory
end
