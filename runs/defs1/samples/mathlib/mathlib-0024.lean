@[expose] public section

open CategoryTheory

namespace HomotopicalAlgebra

open MorphismProperty in
/-- A Reedy structure on a category `C` equipped with two multiplicative
classes of morphisms `W₁` and `W₂` consists of the data of a degree
map for objects `deg : C → α`, where `α` is a well ordered type. The first
two axioms `lt₁` and `lt₂` express the behaviour of the degree with
respect to morphisms in `W₁` (resp. `W₂`) that are not identities, and
the last axiom says that any morphism can be factored in a unique way
as a morphism in `W₁` followed by a morphism in `W₂`. -/
structure ReedyStructure {C : Type*} [Category* C] (W₁ W₂ : MorphismProperty C)
    [W₁.IsMultiplicative] [W₂.IsMultiplicative]
    (α : Type*) [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α] where
  /-- the degree of an object -/
  deg : C → α
  lt₁ {X Y : C} (f : X ⟶ Y) (hf : W₁ f) (hf' : ¬ identities C f) : deg Y < deg X
  lt₂ {X Y : C} (f : X ⟶ Y) (hf : W₂ f) (hf' : ¬ identities C f) : deg X < deg Y
  nonempty_unique {X Y : C} (f : X ⟶ Y) :
    Nonempty (Unique (W₁.MapFactorizationData W₂ f))

end HomotopicalAlgebra
end
