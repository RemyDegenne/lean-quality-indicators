set_option autoImplicit false

public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {G : Type v} [Group G] [TopologicalSpace G]

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable (X : TopRep.{max v w} k G)

variable [IsTopologicalGroup G] [DiscreteTopology X]

/-- The open subgroup on which a continuous crossed homomorphism vanishes.
It is not required to be normal. -/
def zeroOpenSubgroup (f : continuousCrossedHom X) : OpenSubgroup G where
  carrier := {g | f.1 g = 0}
  one_mem' := continuousCrossedHom_apply_one X f
  mul_mem' := by
    intro g h hg hh
    change f.1 g = 0 at hg
    change f.1 h = 0 at hh
    change f.1 (g * h) = 0
    rw [f.2 g h, hh, map_zero, zero_add, hg]
  inv_mem' := by
    intro g hg
    change f.1 g = 0 at hg
    change f.1 g⁻¹ = 0
    have hf := f.2 g⁻¹ g
    simpa only [inv_mul_cancel, hg, map_zero, zero_add,
      continuousCrossedHom_apply_one X f] using hf.symm
  isOpen' := by
    change IsOpen (f.1 ⁻¹' {0})
    exact (isOpen_discrete {0}).preimage f.1.continuous

end ContinuousCohomology
end
