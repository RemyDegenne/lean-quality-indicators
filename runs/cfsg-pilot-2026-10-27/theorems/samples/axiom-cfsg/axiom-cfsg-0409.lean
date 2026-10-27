public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section PartI

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.pPrimeCore_le (S : ZDSetup X Z M) : pPrimeCore 2 X ≤ M := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  have hnorm : normalizer ((pPrimeCore 2 X : Subgroup X) : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer ((pPrimeCore 2 X : Subgroup X) : Set X))) := by
    rw [hnorm]
    exact S.two_le_pRank_zHull_top
  exact S.lemma313 (odd_card_pPrimeCore X) hrank hz (by rw [hnorm]; exact Subgroup.mem_top z)
    (self_mem_omega M) ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hzM)

end PartI
end CFSG.GH74.Uniqueness
end
