namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset

open scoped ENNReal NNReal BoundedContinuousFunction

namespace SmoothObstruction.QR

open MeasureTheory Filter Topology InnerProductSpace

variable {d : ℕ}

lemma basis_apply (e : Frame d) (i : Fin d) : basis e i=e.val i := by
  rw [basis,gramSchmidtOrthonormalBasis_apply_of_orthogonal]
  · simp [e.property.norm_eq_one]
  · exact e.property.2
  · exact e.property.ne_zero i

end SmoothObstruction.QR
end
end OAI
