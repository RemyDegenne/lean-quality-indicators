public section

open CategoryTheory WithConv

open scoped TensorProduct

namespace TauCeti

universe u v w x

section ObjectProperty

variable (k : Type u) [Field k]

theorem geometricallySemisimplePointsCommHopfAlgProperty.tensorProduct
    (H K : CommHopfAlgCat.{v} k)
    (hH : geometricallySemisimplePointsCommHopfAlgProperty k H)
    (hK : geometricallySemisimplePointsCommHopfAlgProperty k K) :
    geometricallySemisimplePointsCommHopfAlgProperty k
      (CommHopfAlgCat.of k (H ⊗[k] K)) := by
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff] at hH hK ⊢
  intro g
  rw [HopfAlgebra.isSemisimplePoint_pointsMulEquiv_iff]
  exact ⟨hH _, hK _⟩

end ObjectProperty
end TauCeti
end
