@[expose] public section

open Metric Set unitInterval

namespace Schoenflies

open Plane

namespace PrePolygon

variable {m : ℕ}

/-- The same closed polygon, read from vertex `a` onwards. -/
def rotate (P : PrePolygon m) (a : ZMod (m + 3)) : PrePolygon m where
  vertex j := P.vertex (a + j)
  vertex_inj i j h := add_left_cancel (P.vertex_inj h)
  edges_meet i j hij := by
    have hi : a + (i + 1) = a + i + 1 := by ring
    have hj : a + (j + 1) = a + j + 1 := by ring
    simp only [hi, hj]
    exact P.edges_meet _ _ fun h => hij (add_left_cancel h)

end PrePolygon
end Schoenflies
end
