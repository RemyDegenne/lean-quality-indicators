@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

theorem powerRootAlgebra_free (n : ℕ) (A : FGAlgCat.{u} K)
    (a : (A.obj : Type u)ˣ) (hn : 0 < n) :
    Module.Free (A.obj : Type u) (AdjoinRoot (powerRootPolynomial K n A a)) := by
  exact (Polynomial.monic_X_pow_sub_C (a : A.obj) (Nat.ne_of_gt hn)).free_adjoinRoot

end General
end AlgebraicGeometry
end
