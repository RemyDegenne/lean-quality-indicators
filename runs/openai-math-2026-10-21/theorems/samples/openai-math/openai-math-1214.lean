namespace OAI

namespace TuringRigidity.UniformArithmetic

open Encodable CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing

open IndexPresentation NumericalIdeal

noncomputable section

theorem value_tableOracle {B : Oracle} {e : ℕ} (h : Dom B e) :
    value B e = degree (tableOracle B e) :=
  value_eq ((valid_tableOracle B e).mp h)

end
end TuringRigidity.UniformArithmetic
end OAI
