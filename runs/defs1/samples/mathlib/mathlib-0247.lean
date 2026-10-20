@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

variable {R A : C} (p₁ p₂ : R ⟶ A)

section Effective

variable (C) in
/-- A category `C` is a universally exact category if all equivalence relations in `C` are
universally effective equivalence relations. -/
class IsUniversallyEffectiveEquivalenceRelationCategory where
  isUniversallyEffectiveEquivalenceRelation (p₁ p₂ : R ⟶ A) [IsEquivalenceRelation p₁ p₂] :
    IsUniversallyEffectiveEquivalenceRelation p₁ p₂

end Effective
end CategoryTheory
end
