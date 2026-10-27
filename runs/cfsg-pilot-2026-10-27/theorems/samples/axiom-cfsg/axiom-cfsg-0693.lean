public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.Open CFSG.ABGLocalTools

open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.RankThree.OrthogonalInvolutions

open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

theorem exists_conj_mem_Q_ne (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    ∃ n : G, n * z * n⁻¹ ∈ Q ∧ n * z * n⁻¹ ≠ z := by
  have hS := hQ.data.setting
  have hF := hS.frame
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hF.sylowR.isPGroup hS.odd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hzZ := hQ.z_mem_Z h212
  rw [hF.sec2Z_eq] at hzZ
  have hzEA : z ∈ E ⊓ A := ⟨hzZ.1.1, hzZ.2⟩
  have hz1 : z ≠ 1 := fun h => by
    have := hQ.order
    rw [h, orderOf_one] at this
    omega
  have h8 : Nat.card (E ⊓ A ⊓ Q : Subgroup G) = 8 := by
    have h := relIndex_mul_card (E ⊓ A ⊓ Q) (E ⊓ A)
    rw [hQ.index, show E ⊓ A ⊓ Q ⊓ (E ⊓ A) = E ⊓ A ⊓ Q from inf_eq_left.mpr inf_le_left,
      hEA16] at h
    omega
  have hnle : ¬ (E ⊓ A ⊓ Q ≤ zpowers z) := fun hle => by
    have h := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hQ.order, h8] at h
    omega
  obtain ⟨w, hw, hwz⟩ := Set.not_subset.mp hnle
  have hw1 : w ≠ 1 := fun h => hwz (h ▸ one_mem _)
  have hwne : w ≠ z := fun h => hwz (h ▸ mem_zpowers z)
  obtain ⟨n, -, hn⟩ := exists_conj_eq_of_card_sixteen hF.base.hyp.standard.1 hS.type hS.odd
    inf_le_right (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) hEA16 hzEA
    (mem_inf.mp hw).1 hz1 hw1
  exact ⟨n, hn ▸ (mem_inf.mp hw).2, hn ▸ hwne⟩

end Sec2Q
end CFSG.ComponentClassification.AS81
end
