public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [Ring R]

variable (X) in
/-- The natural section of the quotient map from unnormalized to normalized cubical chains,
induced by the normalization. -/
def toCubicalChain (n : ℕ) : NormalizedCubicalChain X R n →ₗ[R] CubicalChain X R n :=
  Submodule.liftQ _ (normalize R n) fun _ hf ↦ normalize_eq_zero_of_mem_degenerate R hf

end NormalizedCubicalChain
end TauCeti
end
end
