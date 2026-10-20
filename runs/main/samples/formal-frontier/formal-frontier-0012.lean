@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v w

namespace ZariskiSpace

variable {K : Type u} {σ : Type v}

variable [Field K]

theorem isClosed_zeroLocus (I : Ideal (MvPolynomial σ K)) :
    IsClosed (zeroLocus I) := (isClosed_iff _).2 ⟨I, rfl⟩

end ZariskiSpace
end MvPolynomial
end
end
