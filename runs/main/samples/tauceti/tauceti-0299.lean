public section

universe u

namespace TauCeti

open CategoryTheory

namespace CoveringSpace

variable {X : TopCat.{u}}

theorem proj_hom_comp_hom_left_hom {p q : CoveringSpace X} (f : p ⟶ q) :
    q.proj.hom ∘ f.hom.left.hom = p.proj.hom := by
  rw [← TopCat.coe_comp, w f]

end CoveringSpace
end TauCeti
end
