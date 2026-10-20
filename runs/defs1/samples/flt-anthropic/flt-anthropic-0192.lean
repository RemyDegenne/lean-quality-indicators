namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxHeartbeats 3200000

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GoodReductionJacobian

namespace LevelL3

p2m_open

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

def torsLift (n : ℕ) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hQ : L.nsmul (𝟙 _) n Q = L.one (𝟙 _)) : Spec (CommRingCat.of S) ⟶ L.schemeKer n :=
  pullback.lift Q.1 (𝟙 _) (by rw [comp_schemeNsmul, hQ, Category.id_comp])

end LevelL3
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit
