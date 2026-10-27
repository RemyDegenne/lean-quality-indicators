public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.B Subgroup

theorem le_of_normal_of_isPGroup {X : Type*} [Group X] {K S : Subgroup X} [K.Normal]
    (hsimple : IsSimpleGroup (X ⧸ K)) (hnp : ¬ IsPGroup 2 (X ⧸ K)) (hS : IsPGroup 2 S)
    (hSn : ∀ g : X, ∀ s ∈ S, g * s * g⁻¹ ∈ S) : S ≤ K := by
  have hSN : S.Normal := ⟨fun s hs g => hSn g s hs⟩
  have hMn : (S.map (QuotientGroup.mk' K)).Normal :=
    Subgroup.Normal.map hSN _ (QuotientGroup.mk'_surjective K)
  have hMp : IsPGroup 2 (S.map (QuotientGroup.mk' K)) := hS.map _
  rcases hsimple.eq_bot_or_eq_top_of_normal (S.map (QuotientGroup.mk' K)) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    apply hnp
    intro x
    have hx : x ∈ S.map (QuotientGroup.mk' K) := h ▸ Subgroup.mem_top x
    obtain ⟨k, hk⟩ := hMp ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.Monster.Schur
end
