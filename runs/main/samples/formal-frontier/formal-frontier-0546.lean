public section

namespace ArtinSchreierTwistedLine

open scoped TensorProduct

noncomputable section

universe u v

variable (R : Type u) [CommRing R]

open CategoryTheory AlgebraicGeometry

variable (L : Type v) [CommRing L] [Algebra R L]

theorem scheme_connectedSpace_of_ne_zero
    (K : Type u) [Field K] {p : ℕ} (hp : p.Prime) [CharP K p]
    {t : K} (ht : t ≠ 0) : ConnectedSpace (scheme K p t).left := by
  let _ : IsDomain (CoordinateRing K p t) := coordinateRing_isDomain_of_ne_zero K hp ht
  change ConnectedSpace (PrimeSpectrum (CoordinateRing K p t))
  infer_instance

end
end ArtinSchreierTwistedLine
end
