namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.HilbertPadding

open OperatorAmplification CyclicColumns

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

local instance doubleCopiesIndexDecidableEq : DecidableEq ι := Classical.decEq ι

theorem doubleCopies_commutator_norm
    (Y : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (a : H →L[ℂ] H) :
    ‖extend (doubleCopies ι) Y*diagonal (H:=H) ((Fin 2)×ι) a-
      diagonal (H:=H) ((Fin 2)×ι) a*extend (doubleCopies ι) Y‖=
        ‖Y*diagonal (H:=H) ι a-diagonal (H:=H) ι a*Y‖ :=
  norm_extend_commutator _ _ _ _ (doubleCopies_diagonal ι a) (doubleCopies_adjoint_diagonal ι a)

end Kadison.HilbertPadding
end
end
end
end OAI
