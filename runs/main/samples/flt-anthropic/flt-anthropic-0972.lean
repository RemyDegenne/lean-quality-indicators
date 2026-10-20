namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing

set_option autoImplicit false

p2m_open

universe u

noncomputable section

namespace GoodReductionJacobian

namespace ProdCommRingAux

p2m_open

variable {R : Type u} [CommRing R] {B C : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  {h : C ⟶ Spec (CommRingCat.of R)}

theorem main (hB : AbelianSchemePropertyBundle R g) (hC : AbelianSchemePropertyBundle R h) :
    AbelianSchemePropertyBundle R (prodStr g h) := by
  haveI := hB.smooth
  haveI := hC.smooth
  haveI := hB.proper
  haveI := hC.proper
  obtain ⟨LB⟩ := hB.hasGroupLaw
  obtain ⟨LC⟩ := hC.hasGroupLaw
  exact
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := isConnected_fibre hB hC
      hasGroupLaw := ⟨LB.prod LC⟩ }

end ProdCommRingAux
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_prodStr_commRing
