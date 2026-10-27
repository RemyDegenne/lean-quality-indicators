public section

namespace TauCeti.FiniteQuadraticModule

/-- Multiplication by five preserves the quadratic cyclic form of order two.
This is Nikulin's relation 1.8.2(i) for odd coefficients; the same identity holds for
the degenerate extension with an even coefficient. -/
noncomputable def dyadicCyclicOneIsometryFiveMul (θ : ℤ) :
    Isometry (dyadicCyclic 1 θ) (dyadicCyclic 1 (5 * θ)) :=
  Classical.choice <| by
    rw [nonempty_isometry_dyadicCyclic_iff]
    refine ⟨1, ?_⟩
    -- The unit `1` has integer representative `1`; its doubled denominator is `4`.
    rw [show (1 : (ZMod (2 ^ 1))ˣ).val.val = 1 by decide]
    change (θ : ZMod 4) = ((5 * θ * (1 : ℤ) ^ 2 : ℤ) : ZMod 4)
    -- Reducing the integer cast modulo four identifies the coefficient `5` with `1`.
    rw [one_pow, mul_one, Int.cast_mul, Int.cast_ofNat,
      show (5 : ZMod 4) = 1 by decide, one_mul]

end TauCeti.FiniteQuadraticModule
end
