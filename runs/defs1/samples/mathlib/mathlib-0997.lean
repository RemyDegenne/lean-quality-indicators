@[expose] public section

open CategoryTheory

namespace HomotopicalAlgebra

namespace ReedyStructure

variable {C : Type*} [Category* C] {W₁ W₂ : MorphismProperty C}
  [W₁.IsMultiplicative] [W₂.IsMultiplicative]
  {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure W₁ W₂ α)

/-- The degree of a morphism for a Reedy structure. It is defined as the degree of
the intermediate object in the Reedy factorization, but it is also the smallest
degree of an intermediate object in a factorization, see the lemma `degHom_le`. -/
@[no_expose]
noncomputable def degHom {X Y : C} (f : X ⟶ Y) : α := r.deg (r.mapFactorizationData f).Z

end ReedyStructure
end HomotopicalAlgebra
end
