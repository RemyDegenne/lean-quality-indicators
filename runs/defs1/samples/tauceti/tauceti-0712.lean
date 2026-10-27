public section

universe u v

namespace CliffordAlgebra

open TauCeti (halfOneAdd)

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

variable [Invertible (2 : R)]

/-- **The odd-dimensional splitting, run on the volume element.** For a pairwise orthogonal list of
vectors spanning `M`, of odd length, whose volume element has been rescaled by `s` so as to square
to `1`, the Clifford algebra is the product of two copies of its even subalgebra.

The normalization hypothesis is exactly `(s ω)² = 1` read through
`CliffordAlgebra.prod_map_ι_sq_scalar`; it forces each `Q vᵢ` to be a unit, so it carries the
nondegeneracy the statement needs without naming it. -/
noncomputable def equivEvenProdOfOddLength {l : List M} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Odd l.length) (hspan : Submodule.span R {x : M | x ∈ l} = ⊤) {s : R}
    (hs : s * s * ((-1 : R) ^ l.length.choose 2 * (l.map Q).prod) = 1) :
    CliffordAlgebra Q ≃ₐ[R] (↥(even Q) × ↥(even Q)) :=
  equivEvenProd Q (s • (l.map (ι Q)).prod)
    (fun x => (Subalgebra.mem_center_iff.mp
      (Subalgebra.smul_mem _ (prod_map_ι_mem_center_of_odd_length hl hlen hspan) s)
        (x : CliffordAlgebra Q)).symm)
    (Submodule.smul_mem _ s (prod_map_ι_mem_evenOdd_one_of_odd_length hlen))
    (by rw [smul_mul_assoc, mul_smul_comm, prod_map_ι_sq_scalar hl, smul_smul, Algebra.smul_def,
      ← map_mul, hs, map_one])

end CliffordAlgebra
end
