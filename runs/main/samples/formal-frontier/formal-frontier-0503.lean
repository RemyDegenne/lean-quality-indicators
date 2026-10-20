@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CartesianMonoidalCategory CategoryTheory.MonObj

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [LinearOrder n]

theorem upperTriangularUFirstIso_mul_lift
    {test : Over (Spec (.of K))}
    (unit unit' : test ⟶ unitriangularGroupUnderlyingScheme K n)
    (diag diag' : test ⟶ diagonalGroupUnderlyingScheme K n) :
    lift (unit * (lift diag unit' ≫ upperTriangularDiagonalConj K n))
        (diag * diag') ≫ (upperTriangularUFirstIso K n).hom =
      (lift unit diag ≫ (upperTriangularUFirstIso K n).hom) *
        (lift unit' diag' ≫ (upperTriangularUFirstIso K n).hom) := by
  simp only [upperTriangularUFirstIso_hom, MonObj.comp_mul,
    ← Category.assoc, lift_fst, lift_snd, MonObj.mul_comp]
  rw [upperTriangularDiagonalConj_lift_comp_inclusion]
  group

end AlgebraicGeometry
end
end
