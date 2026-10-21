namespace OAI

noncomputable section

namespace MatrixMultiplication.Foundation.CWLocalConstruction

open Tensor OrientationRates CWOriginalWords PolynomialLocalConstruction

variable {AX AY AZ Label : Type*}

variable [Fintype AX] [Fintype AY] [Fintype AZ] [Fintype Label] [DecidableEq Label]

variable {m a b c : ℕ}

variable (P : CWPrimitive (AX := AX) (AY := AY) (AZ := AZ) (Label := Label) m a b c)

namespace Admissible

variable {P} {physical : Site m → Orientation}

theorem rankBound_pos (h : Admissible P physical) : 0 < P.rankBound :=
  lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos P.leftDim_pos P.middleDim_pos)
    P.rightDim_pos) h.pairing_budget

end Admissible
end MatrixMultiplication.Foundation.CWLocalConstruction
end
end OAI
