@[expose] public section

open Function

namespace Module.Basis

variable {ι A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

variable {K : Type*} [Field K] [Infinite K] [Algebra K A]
  [Module K M] [IsScalarTower K A M] [Finite (MaximalSpectrum A)]

variable {R B L : Type*} [CommRing R] [IsLocalRing R]
  [Infinite (IsLocalRing.ResidueField R)] [CommRing B] [Algebra R B]
  [AddCommGroup L] [Module B L] [Module R L] [IsScalarTower R B L]
  [Finite (MaximalSpectrum B)]

lemma exists_basis_subset_finset_of_le_jacobson (b : Basis ι B L) (W : Submodule R L)
    (hW : Submodule.span B (W : Set L) = ⊤)
    (hJ : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤
      (Ideal.jacobson (⊥ : Ideal B))) (s : Finset ι) :
    ∃ b' : Basis ι B L, (∀ i ∈ s, b' i ∈ W) ∧ ∀ i ∉ s, b' i = b i := by
  exact exists_basis_subset_finset_aux b (W : Set L)
    (fun f hf ↦ LinearMap.exists_mem_isUnit_apply_of_le_jacobson W hW hJ f hf) s

end Module.Basis
end
