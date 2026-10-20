@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace MarkoffRiemannRoch

open _root_.FunctionField

namespace FunctionField

open Chart

variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

local instance instDecidableEqRatFuncCoordinateFreeDivisor : DecidableEq k⟮X⟯ :=
  Classical.decEq _

namespace Place

noncomputable local instance finiteVspAlgebra
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    Algebra k (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
  ((algebraMap (ringOfIntegers k K)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w)).comp
      (algebraMap k (ringOfIntegers k K))).toAlgebra

local instance finiteVspTower
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    IsScalarTower k (ringOfIntegers k K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The finite-chart residue field is the intrinsic residue field. -/
noncomputable def finiteResidueAlgEquiv
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    (ringOfIntegers k K ⧸ w.asIdeal) ≃ₐ[k]
      (Place.ofChart k K (Sum.inl w)).residueField := by
  let e₀ : (ringOfIntegers k K ⧸ w.asIdeal) ≃ₐ[k] w.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k (ringOfIntegers k K ⧸ w.asIdeal) w.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField w.asIdeal)
  let e₁ : w.asIdeal.ResidueField ≃ₐ[k]
      IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
    IsLocalRing.ResidueField.mapAlgEquiv
      ((IsDedekindDomain.HeightOneSpectrum.localizationAlgEquiv (K := K) w).restrictScalars k)
  let e₂ : IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) ≃ₐ[k]
      (Place.ofChart k K (Sum.inl w)).residueField :=
    IsLocalRing.ResidueField.mapAlgEquiv (finiteValuationSubringAlgEquiv k K w)
  exact e₀.trans (e₁.trans e₂)

end Place
end FunctionField
end MarkoffRiemannRoch
end
end
