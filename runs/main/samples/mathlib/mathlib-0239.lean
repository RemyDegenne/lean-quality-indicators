@[expose] public section

noncomputable section

open scoped Pointwise

universe u v

section

open CategoryTheory

namespace GrpCat

variable {A B : GrpCat.{u}} (f : A ⟶ B)

namespace SurjectiveOfEpiAuxs

local notation3 "X" => Set.range (· • (f.hom.range : Set B) : B → Set B)

open XWithInfinity Equiv.Perm

local notation "X'" => XWithInfinity f

local notation "∞" => XWithInfinity.infinity

local notation "SX'" => Equiv.Perm X'

local notation "τ" => tau f

theorem τ_apply_fromCoset : τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ :=
  Equiv.swap_apply_left _ _

end SurjectiveOfEpiAuxs
end GrpCat
end
end
end
