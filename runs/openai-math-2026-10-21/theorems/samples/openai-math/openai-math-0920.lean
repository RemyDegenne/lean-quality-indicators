namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators Classical

namespace ContinuumCoulomb

namespace HubbardGlobal

theorem oneBodyOperator_add {Q : ℕ} (K L : Fin (Q+1) → Fin (Q+1) → ℂ) :
    oneBodyOperator (fun a b => K a b+L a b) = oneBodyOperator K+oneBodyOperator L := by
  simp only [oneBodyOperator,add_smul,Finset.sum_add_distrib]

end HubbardGlobal
end ContinuumCoulomb
end
end OAI
