namespace P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace GammaOneGaloisEven

variable (N : ℕ)

section Group

variable (N : ℕ)

local notation "Δ" => ModularForm.discriminant

def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN N γ)

end Group
end GammaOneGaloisEven
end
end P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even
