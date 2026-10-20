@[expose] public section

namespace Utilities.Certificate.DegenerateSpec

open Utilities.Certificate

open Utilities

open Finset ExplicitPotential SubdivisionGraph

namespace DegSpec

variable {n p : ℕ} (d : DegSpec n p)

theorem pathAt_interior {e : Fin p} {k : ℕ} (h0 : k ≠ 0) (hk : k < d.length e) :
    d.pathAt e k = d.interiorVertex e ⟨k - 1, by omega⟩ := by
  unfold pathAt
  rw [d.pathVertex_interior e (d.clampPos e k)
      (by simp only [clampPos]; omega) (by simp only [clampPos]; omega)]
  exact congrArg (d.interiorVertex e)
    (Fin.ext (by change min k (d.length e) - 1 = k - 1; omega))

end DegSpec
end Utilities.Certificate.DegenerateSpec
end
