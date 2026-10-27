public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

open CFSG.GH74.GLS.IVK (fixedField fixedField_apply mem_fixedField_iff)

open Matrix

open scoped commutatorElement

section Linear

variable {K : Type} [Field K]

theorem eq_comap_range_linFix {S : Type*} [Group S] (τ : S ≃* projectiveSL 3 K)
    {σ : MulAut S} {φ : K ≃+* K} (hστ : MulAut.congr τ σ = fieldAut 3 K φ)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ σ x = x) (hJC : J ≤ C) [Group.IsPerfect J]
    (hnt : J ≠ ⊥) (hsub : (J.subgroupOf C).IsSubnormal) :
    J = (linFix φ).range.comap τ.toMonoidHom := by
  have hfixτ : ∀ x : S, σ x = x → fieldAut 3 K φ (τ x) = τ x := by
    intro x hx
    rw [← hστ]
    show τ (σ (τ.symm (τ x))) = τ x
    rw [MulEquiv.symm_apply_apply, hx]
  refine eq_of_subnormal_of_le_simple ?_ ?_ hsub
    (isSimpleGroup_comap τ (isSimpleGroup_range_linFix φ)) hnt
  · rw [← Subgroup.commutator_eq_self (H := J), Subgroup.commutator_le]
    intro a ha b hb
    show τ ⁅a, b⁆ ∈ (linFix φ).range
    rw [map_commutatorElement]
    exact commutator_mem_range_linFix φ (hfixτ a ((hC a).mp (hJC ha)))
      (hfixτ b ((hC b).mp (hJC hb)))
  · rintro x ⟨g₀, hg₀⟩
    rw [hC]
    have h1 : fieldAut 3 K φ (τ x) = τ x := by
      change fieldAut 3 K φ (τ x) = τ x
      rw [← show linFix φ g₀ = τ x from hg₀]
      exact linFix_fixed φ g₀
    rw [← hστ] at h1
    change τ (σ (τ.symm (τ x))) = τ x at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact τ.injective h1

end Linear
end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
end
