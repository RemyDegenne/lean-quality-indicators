set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups

namespace CuspForm

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ)

def IntTwoCuspForms : Type :=
  TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)

end CuspForm
end
