@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory.Category CategoryTheory.Functor

open Opposite

namespace CategoryTheory

attribute [instance 100] IsConnected.is_nonempty

variable {J : Type u₁} [Category.{v₁} J]

variable {K : Type u₂} [Category.{v₂} K]

theorem isPreconnected_of_isPreconnected_op [IsPreconnected Jᵒᵖ] : IsPreconnected J :=
  isPreconnected_of_equivalent (opOpEquivalence J)

end CategoryTheory
end
end
