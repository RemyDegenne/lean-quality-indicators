public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem E_e1_five : e6Data.E K 5 (Finsupp.single i1 (1 : K)) = 0 :=
  E_single_zero K 5 (by decide) i1 tgt_e1.2.1

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
end
