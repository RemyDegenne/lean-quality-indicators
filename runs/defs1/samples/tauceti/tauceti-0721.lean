open Set Topology

public section

namespace CliffordAlgebra

open TauCeti

noncomputable section

/-- The last coordinate unit vector as a point of the compact real Clifford unit level. -/
def realCliffordSpinLastUnit (n : ℕ) : realCliffordUnitLevel (n + 1) :=
  ⟨Pi.single (Fin.last n) 1, by
    rw [mem_realCliffordUnitLevel]
    exact realCliffordForm_zero_single_one (n + 1) (Fin.last n)⟩

end
end CliffordAlgebra
end
