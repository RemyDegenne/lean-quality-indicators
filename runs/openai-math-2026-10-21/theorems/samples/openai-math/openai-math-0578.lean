namespace OAI

namespace SharpPlanar.IntegerGrid

open IntegerIntervals IntegerCompact

lemma p0_50_contains : p0_50.Contains (quadraturePoint 0 50) := by
  have ht : p0_50.t.Contains (quadraturePoint 0 50) := by
    have he : (RBox.rat 1 12).add ((nodeLookup ⟨50,by decide⟩).scale 1 12) = p0_50.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 0 ⟨50,by decide⟩
  have he : PointBox.calc p0_50.t = p0_50 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)

end SharpPlanar.IntegerGrid
end OAI
