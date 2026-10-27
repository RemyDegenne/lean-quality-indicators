set_option autoImplicit false

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup

open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace CuspForm.PeterssonCoset

section pairing

variable {Λ : Subgroup SL(2, ℤ)} {k : ℤ}

variable (Λ) [Fintype (SL(2, ℤ) ⧸ Λ)]

def pair (k : ℤ) (F G : ℍ → ℂ) : ℂ :=
  ∫ x in (𝒟 : Set ℍ), cosum Λ 1 (UpperHalfPlane.petersson k F G) x

end pairing
end CuspForm.PeterssonCoset
end
