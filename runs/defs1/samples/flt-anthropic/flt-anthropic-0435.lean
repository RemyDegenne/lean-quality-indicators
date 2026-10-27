namespace P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

open scoped TensorProduct

p2m_open

namespace HopfAlgebra

namespace FFHopfKerPID

p2m_open

universe u

section Fibre

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

variable {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]

variable {H' : Type} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']

variable (qc : H →ₐc[R] H') (p : Ideal R) [p.IsPrime]

noncomputable def φ : p.ResidueField ⊗[R] ↥(hopfKer qc) →ₐ[p.ResidueField] p.ResidueField ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
    (IsScalarTower.toAlgHom R ↥(hopfKer qc) H)

end Fibre
end FFHopfKerPID
end HopfAlgebra
end P2MW.S_HopfAlgebra_faithfullyFlat_hopfKer_of_surjective_of_isPrincipalIdealRing
