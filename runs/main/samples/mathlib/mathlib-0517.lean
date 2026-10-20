@[expose] public section

noncomputable section

open Matrix Module LinearMap Submodule Set Function

universe u v w

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable (e : Basis ι R M)

namespace LinearMap

variable {A : Type*} [CommRing A] [Module A M]

variable {κ : Type*} [Fintype κ]

@[simp]
theorem det_conj {N : Type*} [AddCommGroup N] [Module A N] (f : M →ₗ[A] M) (e : M ≃ₗ[A] N) :
    LinearMap.det ((e : M →ₗ[A] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[A] M)) = LinearMap.det f := by
  classical
    by_cases H : ∃ s : Finset M, Nonempty (Basis s A M)
    · rcases H with ⟨s, ⟨b⟩⟩
      rw [← det_toMatrix b f, ← det_toMatrix (b.map e), toMatrix_comp (b.map e) b (b.map e),
        toMatrix_comp (b.map e) b b, ← Matrix.mul_assoc, Matrix.det_conj_of_mul_eq_one]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.symm_trans_self, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
      · rw [← toMatrix_comp, LinearEquiv.comp_coe, e.self_trans_symm, LinearEquiv.refl_toLinearMap,
          toMatrix_id]
    · have H' : ¬∃ t : Finset N, Nonempty (Basis t A N) := by
        contrapose H
        rcases H with ⟨s, ⟨b⟩⟩
        exact ⟨_, ⟨(b.map e.symm).reindexFinsetRange⟩⟩
      simp only [coe_det, H, H', MonoidHom.one_apply, dite_eq_right, not_false_eq_true]

end LinearMap
end
end
