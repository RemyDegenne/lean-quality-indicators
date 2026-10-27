@[expose] public section

namespace Stafford38.Characteristic.ArtinianEquation33TraceProducer

open Matrix

noncomputable section

universe u

variable {B Abar K : Type u}

variable [Ring B] [CommRing Abar] [Field K]

variable {n : ℕ}

/-- Strict upper triangularity over an arbitrary coefficient ring. -/
def IsStrictUpperTriangularOver {S : Type u} [Zero S]
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) S) : Prop :=
  ∀ i j, j ≤ i → M i j = 0

end
end Stafford38.Characteristic.ArtinianEquation33TraceProducer
end
