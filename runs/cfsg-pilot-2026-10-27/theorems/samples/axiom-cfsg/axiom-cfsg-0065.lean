public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup

variable {Γ : Type*} [Group Γ]

theorem centralizer_le_preIn (S : Subgroup Γ) (K' : Subgroup (MulAut ↥S)) :
    centralizer (S : Set Γ) ≤ preIn S K' := by
  intro g hg
  have hgN : g ∈ normalizer (S : Set Γ) := Subgroup.centralizer_le_normalizer _ hg
  exact (mem_preIn_iff S K').2 ⟨hgN, by rw [(actFun_eq_one_iff S hgN).2 hg]; exact one_mem _⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N
end
