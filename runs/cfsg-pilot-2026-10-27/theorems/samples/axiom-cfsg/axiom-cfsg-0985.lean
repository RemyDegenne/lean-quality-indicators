public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G] [Finite G]

theorem normal_kernel_sylow_enlargement
    (R Q : Subgroup G) [R.Normal] (p : ℕ) (hp : p.Prime) (hQ : IsPGroup p Q) :
    ∃ T : Subgroup G, IsPGroup p T ∧ Q ≤ T ∧ T ≤ Q ⊔ R ∧ T ⊔ R = Q ⊔ R ∧
      (∃ S : Sylow p R, (S : Subgroup R).map R.subtype = T ⊓ R) := by
  let : Fact p.Prime := ⟨hp⟩
  let B := Q ⊔ R
  obtain ⟨P, hQP⟩ := hQ.comap_subtype.exists_le_sylow (G := B)
  let T := (P : Subgroup B).map B.subtype
  have hQT : Q ≤ T := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (le_sup_left : Q ≤ B)]
    exact Subgroup.map_mono hQP
  have hTB : T ≤ B := Subgroup.map_subtype_le _
  have hjoin : T ⊔ R = B :=
    le_antisymm (sup_le hTB le_sup_right) (sup_le (hQT.trans le_sup_left) le_sup_right)
  have hRimage : (R.subgroupOf B).map B.subtype = R :=
    Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hS := normal_subgroup_image_sylow_intersection p hp B (R.subgroupOf B) P
  refine ⟨T, P.isPGroup'.map B.subtype, hQT, hTB, hjoin, ?_⟩
  rw [hRimage] at hS
  exact hS

end CFSG.ShultStronglyClosedTI.CentralizerSylow
end
