@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v w

namespace ZariskiSpace

variable {K : Type u} {σ : Type v}

variable [Field K]

theorem zeroLocusClosedPoint_mem_iff (I : Ideal (MvPolynomial σ K))
    (x : zeroLocus I) (p : MvPolynomial σ K) :
    Ideal.Quotient.mkₐ K I p ∈ (zeroLocusClosedPoint I x).val.asIdeal ↔
      aeval x.val.toFun p = 0 :=
  MvPolynomial.zeroLocusClosedPoint_mem_iff I (zeroLocusEquiv I x) p

end ZariskiSpace
end MvPolynomial
end
end
