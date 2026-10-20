public section

namespace NFChoice

namespace Fol

open colimit omegaColimit

universe u

open HenkinLanguageFunctions

/-- Flypitch construction `bounded_formula'_comparison`, retained by the first-order soundness
and completeness development.
-/
@[reducible, expose]
def boundedFormula'Comparison {L : Language.{u}} :
    LimitCarrier (@henkinBoundedFormulaChain' L) → boundedFormula (LInfty L) 1 :=
  @boundedFormulaComparison L 1 0

end Fol
end NFChoice
end
