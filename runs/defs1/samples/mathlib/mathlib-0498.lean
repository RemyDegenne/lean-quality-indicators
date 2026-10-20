@[expose] public section

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated

open Edge CompStruct

variable {X : Truncated 2} {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}

/-- In a `2`-truncated quasicategory, the right homotopy relation on edges
is transitive. -/
@[no_expose]
noncomputable def Edge.HomotopyR.trans [Quasicategory₂ X]
    {f g h : Edge x₀ x₁} (h₁ : HomotopyR f g) (h₂ : HomotopyR g h) :
    HomotopyR f h :=
  assoc (.idCompId _) h₁ h₂

end SSet.Truncated
end
