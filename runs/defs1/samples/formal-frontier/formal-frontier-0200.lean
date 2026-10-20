@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Opens of `X` and of its soberification correspond via the unit. -/
def opensOrderIso (X : Type u) [TopologicalSpace X] :
    Opens X ≃o Opens (IrreducibleCloseds X) where
  toFun := openSet
  invFun U := ⟨(unit X) ⁻¹' (U : Set _), U.isOpen.preimage (unit X).continuous⟩
  left_inv := by
    intro U
    exact Opens.ext (unit_preimage_openSet U)
  right_inv := by
    intro U
    obtain ⟨V, hV⟩ := (isOpen_iff (U : Set (IrreducibleCloseds X))).mp U.isOpen
    have hUV : U = openSet V := SetLike.coe_injective hV
    subst U
    have hInv : (⟨(unit X) ⁻¹' (openSet V : Set _),
        (openSet V).isOpen.preimage (unit X).continuous⟩ : Opens X) = V :=
      Opens.ext (unit_preimage_openSet V)
    exact congrArg openSet hInv
  map_rel_iff' := by
    intro U V
    constructor
    · intro h
      change (U : Set X) ⊆ V
      simpa only [unit_preimage_openSet] using
        (Set.preimage_mono (f := unit X) (show (openSet U : Set _) ⊆ openSet V from h))
    · intro h F hF
      obtain ⟨x, hxF, hxU⟩ := hF
      exact ⟨x, hxF, h hxU⟩

end TopologicalSpace.IrreducibleCloseds
end
