namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois

set_option autoImplicit false

noncomputable section

universe u

p2m_open

namespace GoodReductionJacobian

namespace RelativeGroupLaw

namespace TorsorPhi

p2m_open

variable {K : Type u} [Field K] {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of K)}

section Descent

variable (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
  {V : Scheme.{u}} {g : V ⟶ Spec (CommRingCat.of K)} (D : TorsorData LA g)
  (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = baseExt K K')

@[reassoc]
theorem fK_fst : fK K' LA hc D P hP ≫ pullback.fst fA (baseExt K K') = (psiPt K' LA hc D P hP).1 :=
  pullback.lift_fst _ _ _

end Descent
end TorsorPhi
end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
