/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Endomorphisms of an invertible module

This file packages the scalar-action map as a ring equivalence from a
commutative ring to the endomorphism ring of an invertible module. It also
records the equivalent statement that every module endomorphism is
multiplication by a unique scalar.
-/

@[expose] public section

namespace Module.Invertible

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Scalar multiplication identifies the base ring with the endomorphism ring
of an invertible module. -/
noncomputable def toModuleEndRingEquiv [Module.Invertible R M] :
    R ≃+* Module.End R M :=
  RingEquiv.ofBijective (Module.toModuleEnd R (S := R) M)
    (Module.Invertible.toModuleEnd_bijective R M)

/-- The forward map of `toModuleEndRingEquiv` is scalar multiplication. -/
@[simp] theorem toModuleEndRingEquiv_apply [Module.Invertible R M]
    (r : R) (m : M) :
    toModuleEndRingEquiv R M r m = r • m :=
  rfl

/-- Every endomorphism of an invertible module is multiplication by a unique
scalar. -/
theorem existsUnique_eq_smul [Module.Invertible R M] (f : Module.End R M) :
    ∃! r : R, ∀ m : M, f m = r • m := by
  let e := toModuleEndRingEquiv R M
  refine ⟨e.symm f, ?_, ?_⟩
  · intro m
    exact DFunLike.congr_fun (e.apply_symm_apply f).symm m
  · intro r hr
    apply e.injective
    rw [e.apply_symm_apply]
    ext m
    exact (hr m).symm

end Module.Invertible
