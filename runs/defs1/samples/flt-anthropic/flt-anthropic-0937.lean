namespace P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian TopologicalSpace Topology

universe u

namespace P2mLaw535S

section Assoc

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))

variable (D : (pullback y y).Opens) (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)

scoped instance : IsIso (kA y D M) := ⟨kB y D M, kA_kB y D M, kB_kA y D M⟩

abbrev A0' : Scheme.{u} := pullback (pullback.snd y y) (D.ι ≫ pullback.fst y y)

end Assoc
end P2mLaw535S
end
end P2MW.S_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
