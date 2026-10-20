namespace P2MW.S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd

set_option autoImplicit false

open scoped Topology Real MatrixGroups Matrix CongruenceSubgroup ModularForm Manifold

open UpperHalfPlane hiding I

open EisensteinSeries Filter Complex

noncomputable section

namespace WZE

section MF

variable (L : ℕ) [NeZero L] (χ : DirichletCharacter ℂ L)

def E1 (τ : ℍ) : ℂ := (cst χ)⁻¹ * E0 L χ τ

end MF
end WZE
end
end P2MW.S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
