namespace P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul

set_option autoImplicit false

p2m_open

universe u

p2m_open

open scoped CategoryTheory.MonObj

p2m_open

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry

namespace RelPicard

p2m_open

namespace HomNu2Aux

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c')

def Phi {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t) :
    RigidifiedLineBundle c' ε' t :=
  RigidifiedLineBundle.ofInvertible (ε := ε') (psi f hf t M) (psi_isInvertible f hf t M)

end HomNu2Aux
end RelPicard
end AlgebraicGeometry
end
end P2MW.S_ModularCurve_XOneP_existsUnique_schemeHomOver_prodStr_comp_eq_of_comp_splitTorus_eq_one_specialFibre_baseChange_x1_mul
