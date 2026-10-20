public section

open Manifold

open scoped ContDiff Manifold Matrix.Norms.Operator

noncomputable section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Matrix.linftyOpTopologicalSpace

local notation "SpinUnitsRange(" n ")" =>
  MonoidHom.range (spinGroup.toUnits (Q := realCliffordForm n 0))

local notation "SpecialOrthogonalUnitsRange(" n ")" =>
  MonoidHom.range (QuadraticMap.specialOrthogonalToGeneralLinear
    (realCliffordForm n 0 : QuadraticForm ℝ (Fin n → ℝ)))

local notation "SpinLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm n 0))) (SpinUnitsRange(n)))

local notation "SpecialOrthogonalLieModel(" n ")" =>
  LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
    (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
    (SpecialOrthogonalUnitsRange(n)))

/-- The Lie algebra of the positive-definite real special-orthogonal carrier, in
skew-symmetric-matrix coordinates. -/
noncomputable def realCliffordSpecialOrthogonalLieEquivSo (n : ℕ) :
    LeftInvariantDerivation 𝓘(ℝ, SpecialOrthogonalLieModel(n))
        (SpecialOrthogonalUnitsRange(n)) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ :=
  (realCliffordSpecialOrthogonalEmbeddedLieSubgroupData n)
    |>.lieEquivLieSubalgebraOfSubgroup.trans (specialOrthogonalAmbientCoordinateLieEquiv n)

end TauCeti.CliffordAlgebra
end
end
