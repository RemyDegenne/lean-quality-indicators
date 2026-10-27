public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

variable (p f)

theorem l6_9 (h : L6_6 p f) : L6_9 p f :=
  l6_9_of_l6_6ii p f (l6_6ii_of_l6_6 p f h)

end CFSG.ClassicalInvolution.Asc77
end
