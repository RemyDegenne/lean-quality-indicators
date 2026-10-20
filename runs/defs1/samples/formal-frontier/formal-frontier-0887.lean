@[expose] public section

open scoped Pointwise

namespace Supernatural

noncomputable section

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- Postcompose a rational character with the standard inclusion into the circle. -/
def characterToPontryagin (c : CharacterModule A) :
    PontryaginDual (Multiplicative A) where
  toFun a := Additive.toMul (AddCircle.rationalToCircle (c a.toAdd))
  map_one' := by simp
  map_mul' a b := by
    change Additive.toMul (AddCircle.rationalToCircle (c (a.toAdd + b.toAdd))) =
      Additive.toMul (AddCircle.rationalToCircle (c a.toAdd)) *
        Additive.toMul (AddCircle.rationalToCircle (c b.toAdd))
    rw [map_add, map_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

end
end Supernatural
end
