namespace P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

p2m_open

section Sigma

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

def sigma (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) :
    CyclotomicField ℓ ℚ →+* ℂ :=
  letI : Algebra ℚ (CyclotomicField ℓ ℚ) := CyclotomicField.algebra ℓ ℚ
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI := CyclotomicField.isCyclotomicExtension ℓ ℚ
  ((hζ.embeddingsEquivPrimitiveRoots ℂ (Polynomial.cyclotomic.irreducible_rat hℓ.out.pos)).symm
    ⟨expRoot ℓ, (mem_primitiveRoots hℓ.out.pos).mpr (isPrimitiveRoot_expRoot ℓ)⟩).toRingHom

end Sigma
end ModularCurve
end
end P2MW.S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff
