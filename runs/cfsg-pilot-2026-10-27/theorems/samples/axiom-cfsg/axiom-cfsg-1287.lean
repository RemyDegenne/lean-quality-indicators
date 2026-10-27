public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

theorem dComp_eq_of_mem {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ dComp Ω K) :
    dComp Ω L = dComp Ω K := by
  ext M
  constructor
  · intro hM
    exact hL.trans hM
  · intro hM
    exact (reflTransGen_dAdj_symm hK hL).trans hM

end T7A
end CFSG.ClassicalInvolution.Asc77
end
