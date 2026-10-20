@[expose] public section

open Finset Function HahnSeries Pointwise

noncomputable section

variable {Γ Γ' R S V : Type*}

namespace HahnSeries

section PartialOrder

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

section NonAssocSemiring

variable [NonAssocSemiring R]

theorem C_zero : C (0 : R) = (0 : R⟦Γ⟧) :=
  C.map_zero

end NonAssocSemiring
end PartialOrder
end HahnSeries
end
end
