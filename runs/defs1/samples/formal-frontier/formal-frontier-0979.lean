@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

/-- Signed barycentric subdivision of an affine simplex. A zero-simplex is
unchanged; in positive degree, cone the subdivided oriented boundary to its center. -/
noncomputable def subdivideSimplex {m : ℕ} (n : ℕ) : AffineSimplex m n → AffineChain m n :=
  match n with
  | 0 => fun a ↦ Finsupp.single a 1
  | n + 1 => fun a ↦
    affineCone m n a.center
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • subdivideSimplex n (a.face i))

end Convexity.StdSimplex
end
end
