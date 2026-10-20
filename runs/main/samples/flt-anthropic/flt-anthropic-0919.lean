namespace P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section DeskModule31

set_option autoImplicit false

noncomputable section

open FLT.PrincipalSeriesGL2Padic FLT.PrincipalSeriesGL2Padic.PSCarrier LocalNewvector LocalNewvector.PSCarrier

namespace P6B

open LocalNewvector

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

p2m_reactivate

section Twisted

variable {χ : ℚ_[p]ˣ →* ℂˣ} {cχ : ℕ} (hcχ : HasCharConductor p χ cχ)

theorem diagU_mem_padicK1 {u : ℚ_[p]ˣ} (hu : ‖(u : ℚ_[p])‖ = 1) (m : ℕ) :
    diagU p u ∈ LocalNewvector.padicK1 p m := by
  have h0 : diagU p u ∈ LocalNewvector.padicK1 p 0 := by
    rw [LocalNewvector.padicK1_zero_eq_integralSubgroup]
    exact (borelElem_mem_integralSubgroup_iff p u 1 0).mpr ⟨hu, by simp, by simp⟩
  obtain ⟨y, hy, -, -⟩ := h0
  have hM := congrArg (fun g : GL (Fin 2) ℚ_[p] => (g : Matrix (Fin 2) (Fin 2) ℚ_[p])) hy
  simp only [Matrix.GeneralLinearGroup.map, RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply] at hM
  have h10 : (((y : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 : ℤ_[p]) : ℚ_[p]) = 0 := by
    have := congrFun (congrFun hM 1) 0
    simpa [diagU, borelElem, Matrix.map_apply] using this
  have h11 : (((y : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 1 : ℤ_[p]) : ℚ_[p]) = 1 := by
    have := congrFun (congrFun hM 1) 1
    simpa [diagU, borelElem, Matrix.map_apply] using this
  refine ⟨y, hy, ?_, ?_⟩
  · rw [show (y : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 = 0 from Subtype.ext h10]
    exact Ideal.zero_mem _
  · rw [show (y : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 1 = 1 from Subtype.ext h11, sub_self]
    exact Ideal.zero_mem _

end Twisted
end P6B
end
end DeskModule31
end P2MW.S_LocalNewvector_PSCarrier_finrank_inf_fixedSubmodule_padicK1_of_stable
