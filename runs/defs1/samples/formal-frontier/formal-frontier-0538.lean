@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

/-- The single finitely generated algebra `A[T]/(T^n-a)` adjoining a root. -/
noncomputable def powerRootAlgebra (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) :
    FGAlgCat.{u} K :=
  ⟨CommAlgCat.of K (AdjoinRoot (powerRootPolynomial K n A a)), inferInstance⟩

end General
end AlgebraicGeometry
end
