/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology
import AdicModules.Valuation.Completeness
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Completeness of valued rings and their integer subrings

Completeness of a valued ring is equivalent to completeness of its integer subring.
The ambient uniformity is the one supplied by `Valued`; the integer subring is the stock
`Valuation.integer` with its canonical subtype uniformity. Neither uniformity is replaced.
The ring need not be commutative, a field, or separated, and the value group is unrestricted.

The forward implication uses closedness of the integer subring. Conversely, completeness
of the subtype makes its carrier a complete neighborhood of zero in the ambient ring.

## References

* Adic Modules' `IsRightUniformAddGroup.completeSpace_of_isComplete_mem_nhds` supplies
  the complete-zero-neighborhood criterion. Its proof generalizes the right-uniform group
  argument of Patrick Massot and Johannes Hölzl in
  `Mathlib.Topology.Algebra.IsUniformGroup.Basic`.
* Mathlib supplies the stock valuation integer subring, its closedness and openness,
  and the equivalence between completeness of a subtype and completeness of its carrier.
-/

@[expose] public section

universe uR uΓ

namespace Valued

/-- A supplied valued ring is complete if and only if its integer subring is complete
with the inherited uniformity. No separation or rank hypothesis is required.

The reverse implication uses Adic Modules' complete-zero-neighborhood criterion,
following Mathlib's right-uniform group completeness argument. -/
theorem completeSpace_iff_completeSpace_integer
    {R : Type uR} [Ring R]
    {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued R Γ₀] :
    CompleteSpace R ↔ CompleteSpace ((Valued.v : Valuation R Γ₀).integer) := by
  constructor
  · intro hR
    let : CompleteSpace R := hR
    exact (isClosed_integer R).isComplete.completeSpace_coe
  · intro hO
    exact IsRightUniformAddGroup.completeSpace_of_isComplete_mem_nhds
      ((Valued.v : Valuation R Γ₀).integer : Set R)
      (completeSpace_coe_iff_isComplete.mp hO)
      ((isOpen_integer R).mem_nhds (Valued.v : Valuation R Γ₀).integer.zero_mem)

end Valued
