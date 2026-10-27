namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

set_option autoImplicit false

set_option linter.unusedVariables false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

noncomputable section

namespace ThetaDescentAux

section Loc

variable {B : Type} [CommRing B]

def prodCover {n n' : ℕ} (f : Fin n → B) (g : Fin n' → B) : Fin (n * n') → B :=
  fun l => f (finProdFinEquiv.symm l).1 * g (finProdFinEquiv.symm l).2

end Loc
end ThetaDescentAux
end
end P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule
