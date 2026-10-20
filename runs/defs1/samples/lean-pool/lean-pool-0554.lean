@[expose] public section

open Matrix Function

namespace BollobasNikiforov

variable {ι : Type*} {r : ℕ}

noncomputable section

variable {k p : ℕ}

open Finset

/-- Extension by zero off the `T`-indices. -/
def extendByZeroT (R : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (ConfigIdx k p) (ConfigIdx k p) ℝ :=
  fun α β =>
    match configIdxEquiv k p α, configIdxEquiv k p β with
    | Sum.inr j, Sum.inr ℓ => R j ℓ
    | _, _ => 0

end
end BollobasNikiforov
end
