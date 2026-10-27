public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Open

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem mem_conjClass_self (K : Subgroup G) : K ∈ conjClass K :=
  ⟨1, conjSub_one K⟩

end CFSG.ClassicalInvolution.Generic.CoreAssembly
end
