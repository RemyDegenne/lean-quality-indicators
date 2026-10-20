@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v w

namespace ZariskiSpace

variable {K : Type u} {σ : Type v}

variable [Field K]

theorem isTopologicalBasis_basicOpen :
    TopologicalSpace.IsTopologicalBasis
      (Set.range (basicOpen (K := K) (σ := σ))) := by
  have hSets : Set.range (basicOpen (K := K) (σ := σ)) =
      (Set.preimage (pointToPoint (K := K) (σ := σ))) ''
        Set.range (fun p : MvPolynomial σ K =>
          (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial σ K)))) := by
    ext U
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(PrimeSpectrum.basicOpen p : Set _), ⟨p, rfl⟩,
        (basicOpen_eq_preimage p).symm⟩
    · rintro ⟨S, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, basicOpen_eq_preimage p⟩
  rw [hSets]
  exact (Topology.IsInducing.induced (pointToPoint (K := K) (σ := σ))).isTopologicalBasis
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := MvPolynomial σ K))

end ZariskiSpace
end MvPolynomial
end
end
