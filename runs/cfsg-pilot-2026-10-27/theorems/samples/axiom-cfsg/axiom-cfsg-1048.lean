public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem tiPair_mem_normalizer_of_commute {H A : Subgroup G}
    (hTI : ∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom = A ∨
      A ⊓ A.map (MulAut.conj h).toMonoidHom = ⊥)
    {h x : G} (hh : h ∈ H) (hxA : x ∈ A) (hx1 : x ≠ 1) (hc : h * x = x * h) :
    h ∈ normalizer (A : Set G) := by
  rcases hTI h hh with he | hbot
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · exfalso
    have hxmap : x ∈ A.map (MulAut.conj h).toMonoidHom :=
      ⟨x, hxA, by simp [MulAut.conj_apply, hc]⟩
    have hmem : x ∈ A ⊓ A.map (MulAut.conj h).toMonoidHom := ⟨hxA, hxmap⟩
    rw [hbot] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)

end CFSG.LocalAnalysis.RankThreeUC.S15
end
