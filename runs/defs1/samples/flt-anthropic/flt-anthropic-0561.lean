namespace P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mDomExt536

section Assoc

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))

variable (D : (pullback y y).Opens) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)

def mulFst : DD y D ⟶ pullback y y :=
  pullback.lift (f := y) (g := y) (Q12 y D ≫ M.1) (Q23 y D ≫ D.ι ≫ pullback.snd y y)
    (by simp only [Category.assoc, M_y, fst_y, Q12_snd_assoc])

end Assoc
end P2mDomExt536
end
end P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
