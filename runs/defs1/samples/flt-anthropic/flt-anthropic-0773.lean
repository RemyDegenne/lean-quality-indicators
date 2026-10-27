namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

namespace LBA

section Fibre

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  {Λ : JZeroNeronObjectAtP.LevelData N₀ p A} (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)

noncomputable abbrev Hκ : Scheme.{0} := RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) (dκ O)

end Fibre
end LBA
end P2MW.S_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le
