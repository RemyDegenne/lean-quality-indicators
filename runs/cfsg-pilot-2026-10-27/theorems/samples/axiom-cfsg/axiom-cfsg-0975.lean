public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl

variable {r : ℕ} {K : Type} [Field K]

theorem map_spAct_inv (g : StatedSp r K) (W : Submodule K (Fin r ⊕ Fin r → K)) :
    (W.map (spAct g)).map (spAct g⁻¹) = W := by
  rw [← map_spAct_mul, inv_mul_cancel, map_spAct_one]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
end
