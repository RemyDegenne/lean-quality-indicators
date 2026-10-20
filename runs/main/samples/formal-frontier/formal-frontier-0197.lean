@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v w

namespace ZariskiSpace

variable {K : Type u} {σ : Type v}

variable [Field K]

theorem isEmbedding_zeroLocusClosedPoint (I : Ideal (MvPolynomial σ K)) :
    Topology.IsEmbedding (zeroLocusClosedPoint I) := by
  have hcomp : (PrimeSpectrum.comap (Ideal.Quotient.mk I)) ∘
      (fun x : zeroLocus I => (zeroLocusClosedPoint I x).val) =
        (pointToPoint (K := K) (σ := σ)) ∘ (fun x : zeroLocus I => x.val) := by
    funext x
    apply PrimeSpectrum.ext
    ext p
    change (Ideal.Quotient.mkₐ K I p) ∈ (zeroLocusClosedPoint I x).val.asIdeal ↔
      p ∈ MvPolynomial.vanishingIdeal K {x.val.toFun}
    rw [zeroLocusClosedPoint_mem_iff, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  have hpoint : Topology.IsEmbedding
      ((pointToPoint (K := K) (σ := σ)) ∘ (fun x : zeroLocus I => x.val)) :=
    (isEmbedding_pointToPoint (K := K) (σ := σ)).comp Topology.IsEmbedding.subtypeVal
  have hquotient : Topology.IsEmbedding
      (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    PrimeSpectrum.isEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  have hval : Topology.IsEmbedding
      (fun x : zeroLocus I => (zeroLocusClosedPoint I x).val) :=
    hquotient.of_comp_iff.mp (by simpa only [hcomp] using hpoint)
  exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hval

end ZariskiSpace
end MvPolynomial
end
end
