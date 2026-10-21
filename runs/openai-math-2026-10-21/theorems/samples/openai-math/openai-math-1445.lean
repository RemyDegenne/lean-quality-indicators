namespace OAI

universe u1

noncomputable section

namespace QuadricCounterexample

open Set MvPolynomial Matrix

open BinaryForms

noncomputable section

namespace EqualizerData

variable (D : EqualizerData)

lemma kernelFactor_divisor (i j : StandardChart) {z : BaseCoordinates}
    (hz : z∈coordinateOverlap i j) :
    kernelFactor i j z*(firstFactor i j z*secondFactor i j z)^3=topFactor i j z := by
  have hs := secondFactor_ne_zero hz
  unfold kernelFactor topFactor
  field_simp

end EqualizerData
end
end QuadricCounterexample
end
end OAI
