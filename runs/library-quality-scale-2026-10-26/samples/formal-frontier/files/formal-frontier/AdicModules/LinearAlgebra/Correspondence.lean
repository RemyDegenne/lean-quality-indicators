/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AdicModules.LinearAlgebra.Span.Basic

/-!
# Kernel–range correspondence for submodules

A semilinear map from an additive group to an additive monoid induces an order
isomorphism between submodules containing its kernel and submodules contained in
its range. The forward map is `Submodule.map` and the inverse is `Submodule.comap`.
Surjectivity of the scalar homomorphism is required for the image construction;
the semilinear map itself need not be surjective.

The construction uses Mathlib's map/comap API and `OrderIso.ofHomInv`, together
with `Submodule.comap_map_eq_sup_ker`.

## References

The order isomorphism uses Mathlib's `Submodule.map`, `Submodule.comap` and
`OrderIso.ofHomInv`, together with `Submodule.comap_map_eq_sup_ker` from
`AdicModules.LinearAlgebra.Span.Basic`.
-/

@[expose] public section

universe uR uS uM uP

namespace Submodule

variable {R : Type uR} {S : Type uS} {M : Type uM} {P : Type uP}
variable [Semiring R] [Semiring S] [AddCommGroup M] [AddCommMonoid P]
variable [Module R M] [Module S P] {σ : R →+* S} [RingHomSurjective σ]
variable (f : M →ₛₗ[σ] P)

/-- The map/comap order isomorphism between submodules containing the kernel and
submodules contained in the range of a semilinear map. -/
def orderIsoMapComapKerRange :
    Set.Ici (LinearMap.ker f) ≃o Set.Iic (LinearMap.range f) :=
  OrderIso.ofHomInv
    { toFun := fun N => ⟨map f N.1, LinearMap.map_le_range⟩
      monotone' := by
        intro N N' h
        exact map_mono h }
    { toFun := fun Q => ⟨comap f Q.1, LinearMap.ker_le_comap f⟩
      monotone' := by
        intro Q Q' h
        exact comap_mono h }
    (by
      apply DFunLike.ext
      intro Q
      apply Subtype.ext
      exact map_comap_eq_of_le Q.2)
    (by
      apply DFunLike.ext
      intro N
      apply Subtype.ext
      exact (comap_map_eq_sup_ker f N.1).trans (sup_eq_left.mpr N.2))

/-- The forward kernel–range correspondence takes the direct image. -/
@[simp]
theorem coe_orderIsoMapComapKerRange_apply (N : Set.Ici (LinearMap.ker f)) :
    (orderIsoMapComapKerRange f N : Submodule S P) = map f (N : Submodule R M) := by
  rfl

/-- The inverse kernel–range correspondence takes the inverse image. -/
@[simp]
theorem coe_orderIsoMapComapKerRange_symm_apply (Q : Set.Iic (LinearMap.range f)) :
    ((orderIsoMapComapKerRange f).symm Q : Submodule R M) = comap f (Q : Submodule S P) := by
  rfl

/-- For a bijective map with group source, the forward value agrees with the
whole-lattice map/comap order isomorphism. -/
theorem coe_orderIsoMapComapKerRange_apply_of_bijective (hf : Function.Bijective f)
    (N : Set.Ici (LinearMap.ker f)) :
    (orderIsoMapComapKerRange f N : Submodule S P) =
      orderIsoMapComapOfBijective f hf (N : Submodule R M) := by
  rfl

/-- For a bijective map with group source, the inverse value agrees with the
whole-lattice map/comap order isomorphism. -/
theorem coe_orderIsoMapComapKerRange_symm_apply_of_bijective (hf : Function.Bijective f)
    (Q : Set.Iic (LinearMap.range f)) :
    ((orderIsoMapComapKerRange f).symm Q : Submodule R M) =
      (orderIsoMapComapOfBijective f hf).symm (Q : Submodule S P) := by
  rfl

end Submodule
