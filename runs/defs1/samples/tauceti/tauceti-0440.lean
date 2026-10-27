public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]

section Level

open IntermediateField NumberField

variable {K} {E : IntermediateField K (SeparableClosure K)} [NumberField E]
  {U : OpenSubgroup (AbsoluteGaloisGroup K)} (hU : fixedField U.toSubgroup = E)

/-- **The level of the idele formation is the idele group of the fixed field**: if the fixed
field of the open subgroup `U` is the finite subextension `E`, then `ideleCoeffOfIntermediateField`
identifies the ideles `I_E` of `E` with the level `(I_{Kˢ})^U` of `ideleFormation K`. Applied to
the open normal subgroup fixing a finite Galois extension `L/K`, it identifies the top level of
the layer of `L` with `I_L`. -/
def ideleLevelEquiv : Additive (IdeleGroup (𝓞 E) E) ≃+ (ideleFormation K).level U :=
  AddEquiv.ofBijective (ideleLevelHom hU) (bijective_ideleLevelHom hU)

end Level
end TauCeti.ClassFieldTheory
end
end
