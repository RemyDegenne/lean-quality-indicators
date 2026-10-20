namespace P2MW.S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero

set_option autoImplicit false

open UpperHalfPlane Filter Topology ModularCurve.Period

open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularCurve

namespace PeriodMapNonvanishing

p2m_open

variable {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

section WeightZero

variable (Γ)

variable [Γ.FiniteIndex]

def weightZeroModularForm
    (hholo : ∀ τ : ℍ, DifferentiableAt ℂ (F ∘ ofComplex) ↑τ)
    (hinv : ∀ γ ∈ Γ, ∀ z : ℍ, F (γ • z) = F z)
    (hlim : ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) :
    ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0 where
  toFun := F
  slash_action_eq' := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
    show F ∣[(0 : ℤ)] γ = F
    funext τ
    exact (slash_zero_apply F γ τ).trans (hinv γ hγ τ)
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    intro z hz
    exact (hholo ⟨z, hz⟩).differentiableWithinAt
  bdd_at_cusps' := by
    intro c hc
    have hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
      rintro g ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩
    obtain ⟨δ, rfl⟩ := isCusp_SL2Z_iff'.mp (hc.mono hle)
    rw [OnePoint.isBoundedAt_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ δ) rfl]
    obtain ⟨L, hL⟩ := hlim δ
    have hslash : F ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ δ)
        = fun w : ℍ => F (δ • w) := by
      funext τ
      exact slash_zero_apply F δ τ
    rw [hslash]
    exact hL.isBigO_one ℝ

end WeightZero
end PeriodMapNonvanishing
end ModularCurve
end
end P2MW.S_ModularCurve_Period_CuspForm_periodHom_ne_zero_of_ne_zero
