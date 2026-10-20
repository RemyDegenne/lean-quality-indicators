@[expose] public section

universe v₁ v₂ u₁ u₂

variable {C : Type u₁}

@[inherit_doc]
notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

open CategoryTheory

open CategoryTheory.MonoidalOpposite

variable [Category.{v₁} C]

namespace CategoryTheory

variable (C)

variable {C}

variable [MonoidalCategory.{v₁} C]

open Opposite MonoidalCategory CategoryTheory.Functor LaxMonoidal OplaxMonoidal

section OppositeLemmas

@[simp] lemma op_rightUnitor (X : C) : (ρ_ X).op = (ρ_ (op X)).symm := rfl

end OppositeLemmas
end CategoryTheory
end
