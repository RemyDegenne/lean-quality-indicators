namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

universe u

p2m_open

noncomputable section

namespace GoodReductionJacobian

namespace RelativeGroupLaw

namespace WeilExtField

namespace DOM

p2m_open

scoped instance isDomain_sections_spec (k : Type u) [Field k] :
    IsDomain Γ(Spec (CommRingCat.of k), ⊤) :=
  MulEquiv.isDomain k (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

scoped instance isIntegrallyClosed_sections_spec (k : Type u) [Field k] :
    IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
  IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm

section Main

variable {R : Type u} [CommRing R] {T : Scheme.{u}}

def prSnd (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) : (prodOpen t V).toScheme ⟶ V.toScheme :=
  (pullback t t).homOfLE inf_le_right ≫ (pullback.snd t t ∣_ V)

end Main
end DOM
end WeilExtField
end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension_of_dense
