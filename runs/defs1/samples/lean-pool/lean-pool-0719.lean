@[expose] public section

namespace Biswal.Theorem23

/-- The Chebyshev-type polynomial sequence `P n` over a commutative ring, defined by
`P 0 = P 1 = 1` and `P (n + 2) = P (n + 1) - X * P n`. -/
noncomputable def polyP (R : Type*) [CommRing R] : ℕ → Polynomial R
  | 0 => 1
  | 1 => 1
  | (n + 2) => polyP R (n + 1) - Polynomial.X * polyP R n

end Biswal.Theorem23
end
