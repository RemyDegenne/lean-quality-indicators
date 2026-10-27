public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups commutatorElement

namespace CFSG.Quasithin.SL3Model

open CFSG.Quasithin.SL2Model

variable {F : Type*} [Field F]

theorem mem_Qv_conj {v : Fin 3 → F} (γ A : SL(3, F)) :
    γ * A * γ⁻¹ ∈ Qv (γ • v) ↔ A ∈ Qv v := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · have : γ • (A • v) = γ • v := by
        rw [← mul_smul]
        simpa [mul_smul] using h1
      exact MulAction.injective γ this
    · obtain ⟨c, hc⟩ := h2 (γ • x)
      refine ⟨c, ?_⟩
      have : γ • (A • x) = γ • (x + c • v) := by
        rw [smul_add, smul_comm γ c v]
        simpa [mul_smul] using hc
      exact MulAction.injective γ this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · simp [mul_smul, h1]
    · obtain ⟨c, hc⟩ := h2 (γ⁻¹ • x)
      refine ⟨c, ?_⟩
      simp [mul_smul, hc, smul_add, smul_comm γ c v]

end CFSG.Quasithin.SL3Model
end
