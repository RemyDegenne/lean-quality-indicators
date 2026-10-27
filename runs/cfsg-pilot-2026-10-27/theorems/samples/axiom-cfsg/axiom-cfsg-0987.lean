public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Wreath

open Subgroup SemidirectProduct

variable (A : Type*) [Group A]

variable {A}

theorem base_injective {a b c d : A} : base a b = base c d ↔ a = c ∧ b = d := by
  unfold base
  rw [inl_injective.eq_iff, Prod.mk.injEq]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Wreath
end
