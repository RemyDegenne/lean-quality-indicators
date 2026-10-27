@[expose] public section

open CategoryTheory MonoidalCategory

universe v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

@[inherit_doc] notation "η_" => ExactPairing.coevaluation

@[inherit_doc] notation "ε_" => ExactPairing.evaluation

attribute [instance_reducible, instance] HasRightDual.exact

attribute [instance_reducible, instance] HasLeftDual.exact

open ExactPairing HasRightDual HasLeftDual MonoidalCategory

@[inherit_doc] prefix:1024 "ᘁ" => leftDual

@[inherit_doc] postfix:1024 "ᘁ" => rightDual

@[inherit_doc] notation f "ᘁ" => rightAdjointMate f

@[inherit_doc] notation "ᘁ" f => leftAdjointMate f

/-- A left rigid monoidal category is one in which every object has a right dual. -/
class LeftRigidCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  [leftDual : ∀ X : C, HasLeftDual X]

end CategoryTheory
end
end
