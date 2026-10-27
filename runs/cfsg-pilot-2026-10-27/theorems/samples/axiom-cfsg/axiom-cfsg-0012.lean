public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open FeitExtension NormalInducedFamily

open scoped ComplexOrder Pointwise

section Bookkeeping

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]

omit [Fintype L] [Fintype G] in
theorem coe_virtToSpanIrr_comp {M : Type*} [AddCommMonoid M] (φ : M →+ virtualChars G) (f : M) :
    ((virtToSpanIrr.comp φ f : Submodule.span ℤ (Irr G)) : G → ℂ) = (φ f : G → ℂ) := (rfl)

end Bookkeeping
end CFSG.FeitThompson
end
