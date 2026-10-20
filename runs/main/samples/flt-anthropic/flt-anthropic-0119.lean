namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage

attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

p2m_reactivate

p2m_reactivate

noncomputable section

open scoped TensorProduct Quaternion NumberField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace PkgDesc17

open PkgDesc18

variable {R : Type} [CommRing R] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

p2m_reactivate

p2m_reactivate

section transition

variable (u w : FakeEllipticCurve Λ N R) {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  (φ : A →ₐ[R] B)
  (eA : pullback u.f (ι A) ⟶ pullback w.f (ι A)) (eA_snd : eA ≫ pullback.snd w.f (ι A) = pullback.snd u.f (ι A))
  (eB : pullback u.f (ι B) ⟶ pullback w.f (ι B)) (eB_snd : eB ≫ pullback.snd w.f (ι B) = pullback.snd u.f (ι B))
  (hq : q u.f φ ≫ eA = eB ≫ q w.f φ)

include hq eA_snd eB_snd in

theorem q_mulB : q (f2 u) φ ≫ mulB u w A eA eA_snd = mulB u w B eB eB_snd ≫ q w.f φ := by
  rw [mulB, mulB]
  exact q_baseChange_mul u φ w _ _ _ _
    (by rw [← Category.assoc, q_ptX, Category.assoc, Category.assoc, hq])
    (by rw [← Category.assoc, q_ptY, Category.assoc, Category.assoc, hq])

end transition
end PkgDesc17
end
end
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage
