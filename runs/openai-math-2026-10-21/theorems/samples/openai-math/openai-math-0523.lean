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

variable [instSize : KirchbergRordam.GenericRW.Size]

local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

variable [instPauliData : KirchbergRordam.GenericRW.PauliData]

namespace KirchbergRordam.GenericRW.ConeCube

open scoped CStarAlgebra BigOperators ComplexOrder

open ConeModel _root_.OAI.KirchbergRordam.GenericRW.MaxTensor

lemma κ_first (n : ℕ) (f : C(unitInterval,ℂ)) :
    κ (n+1) (f.comp (first (n+1)))=includeLeft (scalar f) := κ_coordinate (n+1) 0 f

end KirchbergRordam.GenericRW.ConeCube
end
end OAI
