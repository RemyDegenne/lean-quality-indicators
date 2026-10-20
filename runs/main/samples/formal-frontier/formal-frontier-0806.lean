@[expose] public section

noncomputable section

open CategoryTheory

namespace FundamentalGroupoidFunctor

universe u v

section Pi

variable {I : Type u} (X : I → TopCat.{v})

@[simp]
theorem piProductIso_inv_map {a b : FundamentalGroupoid (∀ i, X i)} (p : a ⟶ b) :
    (piProductIso X).inv.map p = fun i => Path.Homotopic.proj i p :=
  rfl

end Pi
end FundamentalGroupoidFunctor
end
end
