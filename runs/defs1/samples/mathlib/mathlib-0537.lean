@[expose] public section

open Function

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

attribute [local instance] uliftCategory

variable (C : Type u) [Category.{v} C]

namespace IsCofiltered

section Nonempty

open CategoryTheory.Limits

variable {C}

variable [IsCofiltered C]

variable (O : Finset C) (H : Finset (Σ' (X Y : C) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y))

/-- The morphisms from `inf O H`.
-/
noncomputable def infTo {X : C} (m : X ∈ O) : inf O H ⟶ X :=
  (inf_exists O H).choose_spec.choose m

end Nonempty
end IsCofiltered
end CategoryTheory
end
