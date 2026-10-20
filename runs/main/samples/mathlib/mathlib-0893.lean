@[expose] public section

universe u v u' v'

namespace CategoryTheory

open Category

section

variable {C : Type*} [EnrichedCategory Cat C]

namespace CatEnriched

@[simp]
theorem hComp_comp {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') :=
  ((eComp Cat a b c).toFunctor.map_comp (Y := (_, _)) (_, _) (_, _)).symm

end CatEnriched
end
end CategoryTheory
end
