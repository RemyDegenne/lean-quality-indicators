@[expose] public section

noncomputable section

open CategoryTheory

namespace FundamentalGroupoidFunctor

universe u v

section Pi

variable {I : Type u} (X : I → TopCat.{v})

@[simp]
theorem piProductIso_hom_map {a b : ∀ i, FundamentalGroupoid (X i)} (p : a ⟶ b) :
    (piProductIso X).hom.map p = Path.Homotopic.pi p :=
  rfl

end Pi
end FundamentalGroupoidFunctor
end
end
