@[expose] public section

universe u v

namespace AdicCompletion

variable {R : Type u} [CommRing R] {I : Ideal R}

variable {M : Type v} [AddCommGroup M] [Module R M]

open Submodule Finsupp

theorem pow_smul_top_eq_ker_eval_of_fg_pow {n : ℕ} (h : (I ^ n).FG) :
    (I ^ n) • (⊤ : Submodule R (AdicCompletion I M)) = (AdicCompletion.eval I M n).ker := by
  classical
  refine le_antisymm (pow_smul_top_le_ker_eval ..) ?_
  rcases h with ⟨s, hs⟩
  simp only [← hs, span_smul_eq]
  rw [← restrictScalars_top R (AdicCompletion I R) (AdicCompletion I M),
    ← restrictScalars_image_smul_eq (R := AdicCompletion I R),
    ← restrictScalars_range_ofPowSMul_eq_ker_eval, restrictScalars_le,
    image_smul_top_eq_range_lsum]
  simp only [SetLike.coe_sort_coe]
  rw [← LinearMap.range_comp_of_range_eq_top
      (f := (finsuppLEquivDirectSum ..).symm.toLinearMap) _ (by simp),
    lsum_smul_comp_finsuppLEquivDirectSum_symm,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top_of_surjective _ <|
      Function.RightInverse.surjective (g := map I (finsuppLEquivDirectSum R M s)) (fun _ ↦ by
        simp [← LinearMap.comp_apply, map_comp]))]
  rintro _ ⟨x, rfl⟩
  let f : (s →₀ M) →ₗ[R] M := lsum R fun i : s ↦ i.val • (LinearMap.id : M →ₗ[R] M)
  have hfRange : f.range = I ^ n • (⊤ : Submodule R M) := by
    rw [← hs, span_smul_eq, smul_top_eq_range_lsum]
    rfl
  have hf : ∀ x, f x ∈ I ^ n • (⊤ : Submodule R M) := by
    intro x
    rw [← hfRange]
    exact LinearMap.mem_range_self f x
  have : Function.Surjective (f.codRestrict (I ^ n • ⊤) hf) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, hfRange]
    simp
  rcases map_surjective I this x with ⟨x, rfl⟩
  exact ⟨x, by rw [← LinearMap.comp_apply, map_comp, LinearMap.subtype_comp_codRestrict]⟩

end AdicCompletion
end
