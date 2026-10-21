namespace OAI

noncomputable section

open scoped TensorProduct

open scoped InnerProductSpace

open scoped BigOperators

open Set Module

open Topology

open NormedSpace

open scoped ComplexOrder

open scoped ComplexOrder

open scoped InnerProductSpace

open scoped InnerProductSpace

open NormedSpace

open scoped TensorProduct InnerProductSpace

open UniformSpace

variable [KirchbergRordam.GenericRW.Size]

local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

variable [KirchbergRordam.GenericRW.PauliData]

omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

open Filter Topology BoundedContinuousFunction

open Filter Topology

open Topology

open scoped TensorProduct CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open NormedSpace

open scoped ComplexOrder

open scoped ComplexOrder

open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.UnitaryDisplacement

variable {A : Type*} [CStarAlgebra A]

lemma displacement_near_fixed (u : unitary A) (a b : A) (hb : conj u b=b) :
    displacement u a ≤ 2*‖a-b‖ := by
  have he : conj u a-a=(conj u a-conj u b)+(b-a) := by rw [hb]; abel
  unfold displacement
  rw [he]
  calc
    _ ≤ ‖conj u a-conj u b‖+‖b-a‖ := norm_add_le _ _
    _ = _ := by rw [norm_sub,norm_sub_rev]; ring

end KirchbergRordam.UnitaryDisplacement
end
end OAI
