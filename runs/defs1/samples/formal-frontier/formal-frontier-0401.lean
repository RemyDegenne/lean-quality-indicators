public section

open Function Set

open CategoryTheory

universe u v w

namespace Module

variable {R : Type u} [CommRing R]

/-- Refining the components `e i` by a second complete orthogonal family
`d j` does not change the explicit model. -/
noncomputable def componentwiseFreeModelRefineRightEquiv
    {I J : Type*} [Fintype I] [Fintype J]
    (e : I → R) (n : I → ℕ) (d : J → R)
    (he : CompleteOrthogonalIdempotents e)
    (hd : CompleteOrthogonalIdempotents d) :
    ComponentwiseFreeModel e n ≃ₗ[R]
      (i : I) → Fin (n i) → (j : J) → Ideal.span {e i * d j} :=
  LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun _ ↦
    spanFamilyEquiv (fun j ↦ e i * d j) (e i)
      (orthogonalIdempotents_mul_left hd.toOrthogonalIdempotents (he.idem i)) (by
        rw [← Finset.mul_sum, hd.complete, mul_one])

end Module
end
