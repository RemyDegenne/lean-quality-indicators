public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open exteriorPower Matrix

variable (K : Type*) [Field K]

variable {K}

theorem e_mem_W2 {i : Fin 6} (hi : i.val < 2) : e K i ∈ W2 K := by
  intro j hj
  have : j ≠ i := fun h => by subst h; omega
  simp [Pi.single_apply, this]

end CFSG.RankThree.GF2n.Smith81.A5Cube
end
