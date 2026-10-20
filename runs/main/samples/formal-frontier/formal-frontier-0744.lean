@[expose] public section

open Function

namespace Module.Basis

variable {ι A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

variable {K : Type*} [Field K] [Infinite K] [Algebra K A]
  [Module K M] [IsScalarTower K A M] [Finite (MaximalSpectrum A)]

lemma exists_basis_subset_finset (b : Basis ι A M) (W : Submodule K M)
    (hW : Submodule.span A (W : Set M) = ⊤) (s : Finset ι) :
    ∃ b' : Basis ι A M, (∀ i ∈ s, b' i ∈ W) ∧ ∀ i ∉ s, b' i = b i := by
  exact exists_basis_subset_finset_aux b (W : Set M)
    (fun f hf ↦ LinearMap.exists_mem_isUnit_apply W hW f hf) s

end Module.Basis
end
