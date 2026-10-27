namespace P2MW.S_CuspForm_exists_gamma1_frickeRational_sigmaTransport

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeCuspTransport

local notation "Δ" => ModularForm.discriminant

section Params

variable {N : ℕ} [NeZero N]

variable (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)

section Main

local notation "𝔢" => ev fricke jf K id (algebraMap K ℂ)

local notation "𝔢'" => ev fricke jf K (ds s) φ

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (k : ℤ) (a b m : ℕ) (hk : k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ))

variable {k a b m}

def Φ (f : CuspForm (Γ₁ℝ N) k) : ℍ → ℂ := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m

end Main
end Params
end FrickeCuspTransport
end
end P2MW.S_CuspForm_exists_gamma1_frickeRational_sigmaTransport
