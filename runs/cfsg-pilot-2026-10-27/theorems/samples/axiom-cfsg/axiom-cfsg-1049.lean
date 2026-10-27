public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley

open scoped commutatorElement

variable {K : Type} [Field K]

theorem map_simplePosSubgroup_d4Graph (ε : ℕ) (i : Fin Tag.D4.rank) :
    (simplePosSubgroup Tag.D4 K i).map (d4Graph K ε).toMonoidHom =
      simplePosSubgroup Tag.D4 K ((d4Rho ^ ε) i) :=
  map_simplePosSubgroup_of_adjX (f := fun c => c) Function.surjective_id (d4Graph_adjX ε i)

end CFSG.HardMathSupport.Lang.D4Three
end
