set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace CountableEndomorphism

universe u v

variable (S : Type u) (M : Type v) [Semiring S] [AddCommGroup M] [Module S M]

variable [Nontrivial M]

theorem kernel_nonzero :
    ∃ k : LinearMap.ker
      (dotProductBilin (Module.End S (ℕ →₀ M)) (Module.End S (ℕ →₀ M))ᵐᵒᵖ
        (row S M)), k ≠ 0 := by
  refine ⟨(kernelEquiv S M).symm
    (fun _ : Fin 1 => (1 : Module.End S (ℕ →₀ M))), ?_⟩
  intro hzero
  apply x₁_ne_zero S M
  calc
    x₁ S M = ((kernelEquiv S M).symm
      (fun _ : Fin 1 => (1 : Module.End S (ℕ →₀ M)))).1 0 := by
        simpa using (kernelEquiv_symm_apply_zero S M (1 : Module.End S (ℕ →₀ M))).symm
    _ = 0 := by rw [hzero]; rfl

end CountableEndomorphism
end
