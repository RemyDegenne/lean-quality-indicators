namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage

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

p2m_reactivate

namespace PkgDesc17

open PkgDesc18

section ActClosure

variable {R : Type} [CommRing R] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

variable {A : Type} [CommRing A] [Algebra R A] (u w : FakeEllipticCurve Λ N R)
  (e : pullback u.f (ι A) ⟶ pullback w.f (ι A)) (e_snd : e ≫ pullback.snd w.f (ι A) = pullback.snd u.f (ι A))

abbrev sAct' (E : FakeEllipticCurve Λ N R) (x : ↥Λ) : pullback E.f (ι A) ⟶ pullback E.f (ι A) :=
  pullback.lift (pullback.fst E.f (ι A) ≫ E.act x) (pullback.snd E.f (ι A)) (by rw [Category.assoc, E.act_over x, pullback.condition])

end ActClosure
end PkgDesc17
end
end
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_of_stdIsoPackage
