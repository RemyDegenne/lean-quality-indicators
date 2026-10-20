public noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped ModularForm MatrixGroups Pointwise

variable {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

open TauCeti TauCeti.UpperHalfPlane

namespace ModularForm

/-- **The conjugate form** `f_ρ(τ) = conj (f (-conj τ))` of a modular form `f` for `𝒢`, as a
modular form for any `𝒢'` conjugated into `𝒢` by `J = !![-1, 0; 0, 1]`. It is the slash of `f`
by the determinant `-1` matrix `J`, so its `q`-expansion has the complex-conjugate
coefficients (`ModularForm.qExpansion_conj`). -/
def conj (hJ : 𝒢' ≤ ConjAct.toConjAct J⁻¹ • 𝒢) (f : ModularForm 𝒢 k) : ModularForm 𝒢' k :=
  _root_.ModularForm.restrict hJ (_root_.ModularForm.translate f J)

end ModularForm
end
