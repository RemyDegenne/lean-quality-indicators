@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v w

namespace ZariskiSpace

variable {K : Type u} {σ : Type v}

variable [Field K]

theorem isOpen_iff (U : Set (ZariskiSpace K σ)) :
    IsOpen U ↔ ∃ I : Ideal (MvPolynomial σ K), Uᶜ = zeroLocus I := by
  rw [← isClosed_compl_iff]
  exact isClosed_iff Uᶜ

end ZariskiSpace
end MvPolynomial
end
end
