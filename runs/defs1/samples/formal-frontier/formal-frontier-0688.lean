public section

open scoped TensorProduct

namespace Ideal

universe u v

variable {K : Type u} [Field K] [IsAlgClosed K]

variable {S : Type v} [CommRing S] [Algebra K S] [Algebra.FiniteType K S]

/-- At a closed point of a finite-type algebra over an algebraically closed
field, the local cotangent space is the fibre of the module of Kähler
differentials of the original algebra. -/
noncomputable def cotangentSpaceEquivTensorKaehlerOfIsAlgClosed
    (m : Ideal S) [m.IsMaximal] :
    IsLocalRing.CotangentSpace (Localization.AtPrime m) ≃ₗ[m.ResidueField]
      (m.ResidueField ⊗[S] Ω[S⁄K]) := by
  let Rm := Localization.AtPrime m
  exact
    (IsLocalRing.cotangentSpaceEquivTensorKaehlerOfResidueEquiv
      (m.residueFieldAlgEquivOfIsAlgClosed (K := K))).trans <|
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K S Rm).symm.baseChange
        Rm m.ResidueField _ _).trans <|
        TensorProduct.AlgebraTensorModule.cancelBaseChange
          S Rm m.ResidueField m.ResidueField Ω[S⁄K]

end Ideal
end
