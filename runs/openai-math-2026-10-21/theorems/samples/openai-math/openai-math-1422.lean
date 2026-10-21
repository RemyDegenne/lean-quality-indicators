namespace OAI

namespace SharpPlanar.IntegerGrid

open IntegerIntervals IntegerCompact

lemma p5_76_contains : p5_76.Contains (quadraturePoint 5 76) := by
  have ht : p5_76.t.Contains (quadraturePoint 5 76) := by
    have he : (RBox.rat 11 12).add ((nodeLookup ⟨76,by decide⟩).scale 1 12) = p5_76.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 5 ⟨76,by decide⟩
  have he : PointBox.calc p5_76.t = p5_76 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)

end SharpPlanar.IntegerGrid
end OAI
