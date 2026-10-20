set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

def JZeroTorsionFinite (M : ℕ) [NeZero M] (n : ℕ) : Prop :=
  Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar M) n)

end ModularCurve
end
