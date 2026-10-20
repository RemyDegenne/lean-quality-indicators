@[expose] public section

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

namespace MvPolynomial

section Rename

section

variable {f : σ → τ} (hf : Function.Injective f) {p : MvPolynomial τ R}

lemma killCompl_monomial_eq_monomial_comapDomain_of_subset {s : τ →₀ ℕ} (c : R)
    (hs : ↑s.support ⊆ Set.range f) :
    (monomial s c).killCompl hf = monomial (s.comapDomain f hf.injOn) c := by
  nth_rw 1 [← s.mapDomain_comapDomain f hf hs, killCompl_monomial_mapDomain]

end
end Rename
end MvPolynomial
end
end
