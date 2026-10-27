public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem RmodN_eq_top (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (hVQ : V S g t ≤ S.Qa g) :
    RmodN S g t = ⊤ := by
  set f := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Vt S g t) with hf
  have htop : (RmodN S g t).comap f.toMonoidHom = ⊤ := by
    refine CFSG.ComponentClassification.OutcomeLocal.eq_top_of_forall_inG fun φ c hφc =>
      ⟨hφc, ?_⟩
    change f _ ∈ RmodN S g t
    have : f (CFSG.ComponentClassification.OutcomeLocal.tv φ c hφc) =
        LinearEquiv.transvection hφc := by
      ext x
      rfl
    rw [this]
    exact centreGroup_le_RmodN H ht hVQ c (transvection_mem_centreGroup hφc)
  rw [eq_top_iff]
  intro e _
  have : f.symm e ∈ (RmodN S g t).comap f.toMonoidHom := htop ▸ mem_top _
  change f (f.symm e) ∈ RmodN S g t at this
  rwa [MulEquiv.apply_symm_apply] at this

end CFSG.LargeExtraspecial.S4
end
