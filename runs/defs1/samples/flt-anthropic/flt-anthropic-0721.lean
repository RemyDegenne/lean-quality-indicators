namespace P2MW.S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq

set_option autoImplicit false

open CongruenceSubgroup ModularForm

open scoped ModularForm MatrixGroups BigOperators

namespace HasseLiftOrthE96

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

def H : ModularForm (Gamma1 p) 0 := (((p : ℂ) - 2)) • (1 : ModularForm (Gamma1 p) 0)

end
end HasseLiftOrthE96
end P2MW.S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
