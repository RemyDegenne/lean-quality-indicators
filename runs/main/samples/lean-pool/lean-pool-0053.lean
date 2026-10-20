@[expose] public section

open MeasureTheory Metric Filter Topology

open NRR.Geometry

namespace NRR

namespace ConvexSubbody

variable {K : Geometry.ConvexBody Plane}

theorem supportFunction_eq_geometry (C : ConvexSubbody K) (G : Geometry.ConvexBody Plane)
    (h : (C.body : Set Plane) = (G : Set Plane)) (u : Plane) :
    C.supportFunction u = G.supportFunction u := by
  rw [supportFunction_eq_sSup, Geometry.ConvexBody.supportFunction_eq_sSup, h]

end ConvexSubbody
end NRR
end
