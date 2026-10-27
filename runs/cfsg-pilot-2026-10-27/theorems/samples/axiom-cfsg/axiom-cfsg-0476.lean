public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

section Toolbox

variable {W : Type*} [CommGroup W]

theorem ne_bot_of_mem_irrSet {X : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet X) :
    I ≠ ⊥ := by
  intro hbot
  exact not_le_fixV_of_mem_irrSet hI (by rw [hbot]; exact bot_le)

end Toolbox
end CFSG.LocalAnalysis.WeakClosure81
end
