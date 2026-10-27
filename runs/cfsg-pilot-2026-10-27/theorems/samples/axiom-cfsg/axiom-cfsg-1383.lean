public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Native

open scoped Matrix

section Aa

theorem isRows_gE (e₀ e₁ e₂ e₃ : ℕ) :
    IsRows (rowsGE e₀ e₁ e₂ e₃) (gA 0 ^ e₀ * gA 1 ^ e₁ * gA 2 ^ e₂ * gA 3 ^ e₃) :=
  (((isRows_gAa1.pow e₀).mul (isRows_gAa2.pow e₁)).mul (isRows_gAa3.pow e₂)).mul
    (isRows_gAa4.pow e₃)

end Aa
end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
end
