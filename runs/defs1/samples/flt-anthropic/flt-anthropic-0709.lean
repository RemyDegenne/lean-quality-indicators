namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3

set_option autoImplicit false

namespace W4DOM

open MeasureTheory Set Real

noncomputable def Mmaj (n : ℕ) (x00 x01 x10 x11 : ℝ) : ℝ :=
  |x00| ^ (-(1/2):ℝ) * |x10| ^ (-(1/2):ℝ) * ((1 + x00 ^ 2) ^ n * (1 + x10 ^ 2) ^ n) *
    ((1 + x01 ^ 2) ^ n * (1 + x11 ^ 2) ^ n)

end W4DOM
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_unfoldedTorusPairIntegrand_jacquetVector3
