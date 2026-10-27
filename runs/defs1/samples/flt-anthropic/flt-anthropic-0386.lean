namespace P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback

set_option autoImplicit false

set_option linter.unusedVariables false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace RelRepX

open CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

section LayerB

open CerednikDrinfeld.QM.FakeEllipticCurve

def qmapO {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) {C : Type} [CommRing C] [Algebra 𝒪 C]
    {T T' : Type} [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    [CommRing T'] [Algebra C T'] [Algebra 𝒪 T'] [IsScalarTower 𝒪 C T'] (φ : T →ₐ[C] T') :
    (T ⧸ Ideal.span {algebraMap 𝒪 T π}) →+* (T' ⧸ Ideal.span {algebraMap 𝒪 T' π}) :=
  Ideal.quotientMap (Ideal.span {algebraMap 𝒪 T' π}) ((φ.restrictScalars 𝒪 : T →ₐ[𝒪] T') : T →+* T')
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_comap.mpr
      (by rw [show ((φ.restrictScalars 𝒪 : T →ₐ[𝒪] T') : T →+* T') (algebraMap 𝒪 T π) = algebraMap 𝒪 T' π from
            (φ.restrictScalars 𝒪).commutes π]
          exact Ideal.subset_span rfl))))

end LayerB
end RelRepX
end P2MW.S_CerednikDrinfeld_QM_RigidifiedPairClass_exists_stratumPoint_of_forall_representsOn_of_isPullback
