namespace P2MW.S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 800000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

open scoped TensorProduct

universe u v

namespace S17Torsor

variable {k : Type u} [CommRing k] {H : Type v} [CommRing H] [HopfAlgebra k H]

variable (K : Subalgebra k H)

variable (hΔ : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
  Submodule.span k {t : H ⊗[k] H | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})

noncomputable def β : H ⊗[↥K] H →ₐ[H] C K :=
  Algebra.TensorProduct.lift (Algebra.ofId H (C K)) (g K hΔ) (fun _ _ => Commute.all _ _)

end S17Torsor
end P2MW.S_HopfAlgebra_faithfullyFlat_map_toAlgHom_tensor_of_free_map_of_ker_eq_span
