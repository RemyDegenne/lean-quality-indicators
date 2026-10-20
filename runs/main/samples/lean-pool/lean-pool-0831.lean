@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits ZeroObject

open scoped MonObj

universe v u w

section Split

variable {E : Type u}

theorem retractionSection_comp
    [Category.{v} E] [Abelian E] {K : E} {N : E} (k : K ⟶ N) (r : N ⟶ K)
    (hr : k ≫ r = 𝟙 K) :
    retractionSection k r hr ≫ r = 0 := by
  refine (cancel_epi (cokernel.π k)).1 ?_
  rw [← Category.assoc, π_retractionSection, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, hr, Category.comp_id, sub_self,
    Limits.comp_zero]

end Split
end RS
end
