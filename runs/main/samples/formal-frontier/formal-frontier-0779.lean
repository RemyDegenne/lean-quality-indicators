@[expose] public section

noncomputable section

namespace MvPolynomial

universe u v w

namespace ZariskiSpace

variable {K : Type u} {σ : Type v}

variable [Field K]

@[simp] theorem mem_zeroLocus {I : Ideal (MvPolynomial σ K)} {x : ZariskiSpace K σ} :
    x ∈ zeroLocus I ↔ x.toFun ∈ MvPolynomial.zeroLocus K I := Iff.rfl

end ZariskiSpace
end MvPolynomial
end
end
