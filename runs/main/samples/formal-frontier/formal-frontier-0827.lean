public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopCat TopologicalSpace

universe u

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {X : TopCat.{u}}

variable {B : Set (Opens X)} (hB : Opens.IsBasis B)

variable {F G : X.Presheaf AddCommGrpCat.{u}} {α : F ⟶ G}

include hB

theorem stalkFunctor_map_bijective_of_isBasis
    (hα : ∀ U ∈ B, Function.Bijective (α.app (op U))) (x : X) :
    Function.Bijective ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α) :=
  ⟨Presheaf.stalkFunctor_map_injective_of_isBasis hB
      (fun U hU => (hα U hU).injective) x,
    stalkFunctor_map_surjective_of_isBasis hB
      (fun U hU => (hα U hU).surjective) x⟩

end SheafCohomology.HigherDirectImageFilteredColimit
end
end
