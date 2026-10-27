@[expose] public section

open Bornology Set

namespace Schoenflies

variable {C J P Ω Ω' W V : Set Plane} {x y z : Plane}

namespace ClosedPolygon

variable {m : ℕ} {C : ClosedPolygon m} {a : ZMod (m + 3)} {k : ℕ}

/-- The arc of `C` that leaves vertex `a` and runs forward through `k` edges, as a set: the
blueprint's `A₁` for `k` edges and `A₂` for the remaining `m + 3 - k`. -/
def arc (C : ClosedPolygon m) (a : ZMod (m + 3)) (k : ℕ) : Set Plane := cover (C.arcPieces a k)

end ClosedPolygon
end Schoenflies
end
