namespace P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped Quaternion TensorProduct NumberField Pointwise

open QuaternionAlgebra CerednikDrinfeld ModularCurve

namespace Ws3

namespace StepDictBody

noncomputable section

variable {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]

variable {a b : ℚ}

section N

variable {X₀ W : WeierstrassCurve κ} [X₀.IsElliptic] [W.IsElliptic]

variable {θ : ↥(WeierstrassCurve.rationalEndSubring κ X₀) →+* ℍ[ℚ, a, b]}

variable {χ : X₀.toAffine.Point →+ W.toAffine.Point} {d : (ℍ[ℚ, a, b])ˣ}

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}

def homsIntoSubgroup (hθ : Function.Injective θ) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₀ W) (hχs : Function.Surjective χ)
    (hχK : θ '' (WeierstrassCurve.kernelIdealSet κ X₀ W χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]))
    (J : Submodule ℤ ℍ[ℚ, a, b]) : AddSubgroup (W.toAffine.Point →+ X₀.toAffine.Point) where
  carrier := homsInto X₀ W θ χ d J
  zero_mem' := by
    refine (mem_homsInto_iff J 0).mpr ⟨WeierstrassCurve.zero_mem_rationalHomSet κ W X₀, compEnd hχ (WeierstrassCurve.zero_mem_rationalHomSet κ W X₀), rfl, ?_⟩
    have h0 : compEnd hχ (WeierstrassCurve.zero_mem_rationalHomSet κ W X₀) = 0 :=
      Subtype.ext (by rw [coe_compEnd]; ext P; rfl)
    rw [h0, map_zero]; exact J.zero_mem
  add_mem' := by
    intro ρ σ hρ hσ
    obtain ⟨hρ, e₁, he₁, h₁⟩ := (mem_homsInto_iff J ρ).mp hρ
    obtain ⟨hσ, e₂, he₂, h₂⟩ := (mem_homsInto_iff J σ).mp hσ
    refine (mem_homsInto_iff J _).mpr ⟨WeierstrassCurve.add_mem_rationalHomSet κ W X₀ hρ hσ, e₁ + e₂, ?_, ?_⟩
    · rw [Subring.coe_add, he₁, he₂]; exact (AddMonoidHom.add_comp ρ σ χ).symm
    · rw [map_add]; exact J.add_mem h₁ h₂
  neg_mem' := by
    intro ρ hρ
    obtain ⟨hρ, e, he, h⟩ := (mem_homsInto_iff J ρ).mp hρ
    refine (mem_homsInto_iff J _).mpr ⟨neg_mem_rationalHomSet_of_ker hθ hχ hχs hχK hρ, -e, ?_, ?_⟩
    · rw [Subring.coe_neg, he]; exact (AddMonoidHom.neg_comp ρ χ).symm
    · rw [map_neg]; exact J.neg_mem h

end N
end
end StepDictBody
end Ws3
end P2MW.S_CerednikDrinfeld_forall_exists_natCard_eq_image_setOf_comp_eq_star_smul_ofFiniteIdele_mul_of_mem_primeHeckeSet
