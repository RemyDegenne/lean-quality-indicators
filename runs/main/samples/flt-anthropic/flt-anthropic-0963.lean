namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_presentationLabel_unique_and_leg_eq_of_ptR_eq_pr

attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup instTopologicallyFGOfFiniteType

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

p2m_open

namespace C1Aux

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]

theorem exists_geomPoint [Nontrivial S] : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k), Nonempty (S →+* k) := by
  obtain ⟨x⟩ : Nonempty ↥(Spec (CommRingCat.of S)) := inferInstance
  exact ⟨AlgebraicClosure x.asIdeal.ResidueField, inferInstance, inferInstance,
    ⟨(algebraMap x.asIdeal.ResidueField (AlgebraicClosure x.asIdeal.ResidueField)).comp (algebraMap S x.asIdeal.ResidueField)⟩⟩

end C1Aux
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_presentationLabel_unique_and_leg_eq_of_ptR_eq_pr
