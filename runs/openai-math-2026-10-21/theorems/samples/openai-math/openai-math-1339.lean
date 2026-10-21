namespace OAI

namespace SharpPlanar.IntegerGrid

open IntegerIntervals IntegerCompact

lemma p4_97_contains : p4_97.Contains (quadraturePoint 4 97) := by
  have ht : p4_97.t.Contains (quadraturePoint 4 97) := by
    have he : (RBox.rat 9 12).add ((nodeLookup ⟨97,by decide⟩).scale 1 12) = p4_97.t := by decide +kernel
    rw [← he]
    exact quadraturePoint_contains 4 ⟨97,by decide⟩
  have he : PointBox.calc p4_97.t = p4_97 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)

end SharpPlanar.IntegerGrid
end OAI
