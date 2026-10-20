@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (J₁ J₂ : GrothendieckTopology C)

namespace GrothendieckTopology

/-- A sieve is closed for the Grothendieck topology if it contains every arrow it covers.
In the case of the usual topology on a topological space, this means that the open cover contains
every open set which it covers.

Note this has no relation to a closed subset of a topological space.
-/
def IsClosed {X : C} (S : Sieve X) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), J₁.Covers S f → S f

end GrothendieckTopology
end CategoryTheory
end
