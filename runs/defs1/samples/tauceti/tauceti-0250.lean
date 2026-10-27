public section

namespace TauCeti

open Equiv _root_.Nat

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight `z_μ = ∏ᵢ i ^ mᵢ · mᵢ !` of a partition `μ`, where `mᵢ = partMultiplicity μ i` is
the multiplicity of the part `i`.

It is the order of the centralizer of a permutation whose cycle lengths are the parts of `μ`, so
the conjugacy class of that permutation has `n ! / zPart μ` elements. -/
def zPart {n : ℕ} (μ : n.Partition) : ℕ :=
  ∏ i ∈ μ.parts.toFinset, i ^ partMultiplicity μ i * (partMultiplicity μ i)!

end TauCeti
end
