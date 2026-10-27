@[expose] public section

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated

open Edge CompStruct

variable {X : Truncated 2} {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}

/--
Two edges `f` and `g` are left homotopic if there is a `CompStruct` with
(0, 1)-edge `f`, (1, 2)-edge `Edge.id` and (0, 2)-edge `g`. We use `Nonempty` to
have a `Prop` valued `HomotopicL`.
-/
abbrev HomotopicL (f g : Edge x₀ x₁) :=
  Nonempty (HomotopyL f g)

end SSet.Truncated
end
