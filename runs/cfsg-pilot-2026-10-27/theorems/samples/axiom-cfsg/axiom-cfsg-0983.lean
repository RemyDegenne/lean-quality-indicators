public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.GSide CFSG.Monster.B.CTIB

open CFSG.Monster.B.CTIB.Native (qmul gArr liftImgsN sqCode autApply)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem n1Test_of_symm
    {y : vStab cv0}
    (hsQ : sEquiv.symm (y : Shat) ∈ Qs)
    (hsc : sEquiv.symm (y : Shat) * labelS = labelS * sEquiv.symm (y : Shat))
    (hs2 : sEquiv.symm (y : Shat) * sEquiv.symm (y : Shat) = 1)
    (hs1 : sEquiv.symm (y : Shat) ≠ 1) (hsl : sEquiv.symm (y : Shat) ≠ labelS) :
    IsConj (cE' * xhatEam) (vStabEam y) ∨
      ∃ i₁ ∈ commutator Eam, ∃ i₂ ∈ commutator Eam, i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧
        i₁ * i₂ * (i₁ * i₂) = vStabEam y := by
  obtain ⟨-, hr, -⟩ := native_inner_involution_census labelS_mem_Qs (IsConj.refl labelS)
  rcases hr _ hsQ hsc hs2 hs1 hsl with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_RB hs2 hsc h1 h2))
  · left
    have h := isConj_lamW0H_of_RA hs2 hsc h1 h2
    have ey : (⟨sEquiv (sEquiv.symm (y : Shat)), sEquiv_mem_vStab hsc⟩ : vStab cv0) = y :=
      Subtype.ext (MulEquiv.apply_symm_apply _ _)
    rw [ey] at h
    have h' := vStabEam.toMonoidHom.map_isConj h
    rw [MulEquiv.coe_toMonoidHom, vStabEam_lamW0H] at h'
    exact h'
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_Y2 hs2 hsc h1 h2))
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_cY2 hs2 hsc h1 h2))
  · exact Or.inr (dihedral_Eam_of_D8At hsc (d8At_of_Y3 hsQ hs2 hsc h1 h2))

end CFSG.EvenSmallLie.TwoE6
end
