public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7F2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}

namespace Hyp25T

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem RR_le_N : R ⊔ R' ≤ Nsub S R := sup_le h.R_le_N h.R'_le_N

end Hyp25T
end T7F2
end CFSG.ClassicalInvolution.Asc77
end
