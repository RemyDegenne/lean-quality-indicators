public section

open Matrix

namespace TauCeti

open Submodule

variable {F ι κ : Type*} [Field F]

section Aut

variable {R : Type*} [CommSemiring R] [Fintype ι] {C : Submodule R (ι → R)}

theorem dotProductContragredient_eq_self_of_mem_permutationGroup [DecidableEq ι]
    {f : (ι → R) ≃ₗ[R] (ι → R)} (hf : f ∈ permutationGroup R ι) :
    f.dotProductContragredient = f := by
  obtain ⟨e, rfl⟩ := mem_permutationGroup.1 hf
  rw [← monomialEquiv_one, dotProductContragredient_monomialEquiv, inv_one]

end Aut
end TauCeti
end
