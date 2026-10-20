public section

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

namespace StrictUnit

variable {𝒞 : AInfinityCategory R C}
  {e e' : ∀ X : C, homModule (R := R) X X}

@[simp]
theorem unary_eq_zero (h : 𝒞.StrictUnit e) (X : C) :
    𝒞.m 1 ![homInclusion X X (e X)] = 0 := by
  exact h.m_eq_zero_of_eq_unit (n := 1) (i := 0) (X := X) (by decide) _ (by simp)

end StrictUnit
end AInfinityCategory
end TauCeti
end
