@[expose] public section

noncomputable section

open RCLike Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace Complexification

/-- The real-part projection `(x, y) ↦ x` as a continuous `ℝ`-linear map. -/
def fstL : Complexification H →L[ℝ] H :=
  fstₗ.mkContinuous 1 fun u => by rw [one_mul]; exact norm_fst_le u

end Complexification
end
end
