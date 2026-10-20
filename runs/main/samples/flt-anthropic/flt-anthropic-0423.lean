namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion

set_option autoImplicit false

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian

namespace PDivBCAux

open GoodReductionJacobian GoodReductionJacobian.RelativeGroupLaw NeronModelInfra

universe u

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']

variable (σ : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

theorem baseChange_one_fst :
    ((L.baseChange σ).one (𝟙 (Spec (CommRingCat.of R')))).1 ≫ pullback.fst f σ =
      σ ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h1 := congrArg Subtype.val (baseChangePointToBase_one σ L (𝟙 (Spec (CommRingCat.of R'))))
  rw [baseChangePointToBase_coe] at h1
  have h2 := congrArg Subtype.val
    (L.one_natural (𝟙 (Spec (CommRingCat.of R))) (𝟙 (Spec (CommRingCat.of R')) ≫ σ) σ
      (by rw [Category.comp_id, Category.id_comp]))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h2
  exact h1.trans h2.symm

end PDivBCAux
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_closedImmersion_isIso_torsion_tensorProduct_baseChange_of_isIso_torsion
