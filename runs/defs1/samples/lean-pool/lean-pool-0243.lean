@[expose] public section

namespace Utilities.Certificate

open Finset

open ExplicitPotential

namespace CoreVertexCut.Data

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

/-- Executable number of ordered core slots in the complementary side. -/
def rightSlotCount (c : CoreVertexCut.Data core) : ℕ :=
  c.rightSlots.card

end CoreVertexCut.Data
end Utilities.Certificate
end
