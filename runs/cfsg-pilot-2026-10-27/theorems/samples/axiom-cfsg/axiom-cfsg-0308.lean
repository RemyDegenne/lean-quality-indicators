public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Sp

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ)

include hCE H hNo C ht ht1 hVQ hSp

theorem Wone_eq_sup_pair {k k' : S.M} (hk : S.ρ k ∈ Rbar S g t) (hk' : S.ρ k' ∈ Rbar S g t)
    (hkk' : (k' : G) * g * S.z * ((k' : G) * g)⁻¹ ∉ S.Qa ((k : G) * g)) :
    (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t) ⊔
        (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t) =
      Wone S g t ((k : G) * g) ((k' : G) * g) := by
  have htk := mem_Lbar_mul_of_mem_Rbar H ht hk
  have htk' := mem_Lbar_mul_of_mem_Rbar H ht hk'
  have dA := finrank_clSub_inf_Wt (H.mul k) (C.mul k) htk ht1 (not_V_le_Qa_mul H hVQ hk)
  have dB := finrank_clSub_inf_Wt (H.mul k') (C.mul k') htk' ht1 (not_V_le_Qa_mul H hVQ hk')
  rw [Wt_mul] at dA dB
  have dP := finrank_clSub_inf_clSub_pair H C ht ht1 hVQ hk hk' hkk'
  have dV := finrank_Vone_eq hCE H hNo C ht ht1 hVQ hSp hk hk' hkk'
  have dW := finrank_Wone (S := S) (g := g) (t := t) ((k : G) * g) ((k' : G) * g)
  have dQ := S.finrank_Qt_eq_two_mul_width
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t)
    (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t)
  have e : (S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ Wt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) ⊓ Wt S g t) =
      S.clSub (S.QG ⊓ S.Qa ((k : G) * g)) ⊓ S.clSub (S.QG ⊓ S.Qa ((k' : G) * g)) := by
    rw [← inf_inf_distrib_right,
      inf_eq_left.mpr (clSub_inf_clSub_le_Wt_pair H C ht ht1 hVQ hk hk' hkk')]
  rw [e] at hs
  refine Submodule.eq_of_le_of_finrank_le
    (sup_le (clSub_inf_Wt_le_Wone_pair H C ht ht1 hVQ hk hk' hkk')
      (clSub_inf_Wt_le_Wone_pair' H C ht ht1 hVQ hk hk' hkk')) ?_
  omega

end Sp
end CFSG.LargeExtraspecial.S6
end
