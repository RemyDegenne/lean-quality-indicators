namespace P2MW.S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

p2m_open

namespace QExpN

section Main

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

variable (f g : LaurentSeries ℚ) (F : ℍ → ℂ)
  (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
  (hG : ∀ τ : ℍ, HasSum (fun m : ℤ => ((g.coeff m : ℚ) : ℂ) * 𝕢 ℓ (τ : ℂ) ^ m) (F (ModularGroup.S • τ)))
  (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : ℍ, F (γ • τ) = F τ)

include hF hG hinv in

theorem isIntegral_adjoin_jq : IsIntegral (Algebra.adjoin ℚ {jq}) f := by
  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  haveI : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  exact isIntegral_of_data ℓ hzu.unit hζ (sigma ℓ hzu.unit hζ) (sigma_zeta ℓ hzu.unit hζ) f g F hF hG hinv

end Main
end QExpN
end ModularCurve
end
end P2MW.S_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant
