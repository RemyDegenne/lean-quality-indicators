public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Matrix

variable {K : Type} [Field K] {m : ℕ}

theorem s16k_conj_group {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Γ : Subgroup (GL ι K)) {F : Subgroup (GL ι K)} (hF : F ≤ Γ) {g : GL ι K} (hg : g ∈ Γ)
    (hFp : IsPGroup 3 ↥F) (hFc : ¬ IsCyclic ↥F)
    {v w : ι → K} (hfix : ∀ f ∈ F, (f : Matrix ι ι K) *ᵥ v = v ∧
      (f : Matrix ι ι K) *ᵥ w = w) :
    ∃ F' : Subgroup (GL ι K), F' ≤ Γ ∧ IsPGroup 3 ↥F' ∧ ¬ IsCyclic ↥F' ∧
      ∀ f' ∈ F', (f' : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) =
          ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v ∧
        (f' : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) =
          ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w := by
  refine ⟨F.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hx
    change (MulAut.conj g⁻¹) f ∈ Γ
    rw [MulAut.conj_apply, inv_inv]
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (hF hf)) hg
  · exact hFp.of_equiv (Subgroup.equivMapOfInjective F (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)
  · intro hcyc
    exact hFc ((Subgroup.equivMapOfInjective F (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).isCyclic.mpr hcyc)
  · intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hf'
    refine ⟨?_, ?_⟩
    · change (((MulAut.conj g⁻¹) f : GL ι K) : Matrix ι ι K) *ᵥ
          (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
      rw [MulAut.conj_apply, inv_inv, s16k_conj_mulVec, (hfix f hf).1]
    · change (((MulAut.conj g⁻¹) f : GL ι K) : Matrix ι ι K) *ᵥ
          (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w
      rw [MulAut.conj_apply, inv_inv, s16k_conj_mulVec, (hfix f hf).2]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
end
