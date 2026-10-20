namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP ModularCurve.CharacterLattice

attribute [local instance 2000] ValuationSubring.instAlgebraSubtypeMem

noncomputable section

namespace ToricReadAsm

section main

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)
  {m : ℕ} (hm : 0 < m)

abbrev NodeDatum (O : JHNeronObjectAtP p M H hpM A hA Λ) : Type := ↥O.ssFinset → Additive (ResidueField ↥A)ˣ

end main
end ToricReadAsm
end
end P2MW.S_ModularCurve_JHNeronObjectAtP_exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit
