/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

@[expose] public section

/-!
# The endpoints of the snake sequence

For a `ShortComplex.SnakeInput`, the kernels and cokernels of its two horizontal
endpoint arrows extend the six terms of the snake lemma without requiring the
upper-left arrow to be monic or the lower-right arrow to be epic.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*,
  corrected second edition, (1.3.1).
* Mathlib's `CategoryTheory.ShortComplex.SnakeInput.snake_lemma`.
-/

universe v u

namespace CategoryTheory.ShortComplex.SnakeInput

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex.SnakeInput C)

/-- The kernel of the upper-left arrow maps into the kernel of the first vertical arrow. -/
noncomputable def kernelToL₀X₁ : kernel S.L₁.f ⟶ S.L₀.X₁ :=
  (KernelFork.IsLimit.lift' S.h₀τ₁ (kernel.ι S.L₁.f) (by
    apply (cancel_mono S.L₂.f).mp
    rw [Category.assoc, S.v₁₂.comm₁₂, ← Category.assoc,
      kernel.condition, zero_comp, zero_comp])).1

/-- The left endpoint map factors the upper-left kernel inclusion. -/
@[reassoc (attr := simp)]
theorem kernelToL₀X₁_comp_v₀₁ :
    S.kernelToL₀X₁ ≫ S.v₀₁.τ₁ = kernel.ι S.L₁.f :=
  (KernelFork.IsLimit.lift' S.h₀τ₁ (kernel.ι S.L₁.f) (by
    apply (cancel_mono S.L₂.f).mp
    rw [Category.assoc, S.v₁₂.comm₁₂, ← Category.assoc,
      kernel.condition, zero_comp, zero_comp])).2

/-- The left endpoint map vanishes after the first kernel-row arrow. -/
@[reassoc (attr := simp)]
theorem kernelToL₀X₁_comp_f : S.kernelToL₀X₁ ≫ S.L₀.f = 0 := by
  apply (cancel_mono S.v₀₁.τ₂).mp
  rw [Category.assoc, ← S.v₀₁.comm₁₂, ← Category.assoc,
    S.kernelToL₀X₁_comp_v₀₁, kernel.condition, zero_comp]

/-- The left endpoint map exhibits the kernel of the first kernel-row arrow. -/
noncomputable def kernelToL₀X₁IsKernel :
    IsLimit (KernelFork.ofι S.kernelToL₀X₁ S.kernelToL₀X₁_comp_f) := by
  haveI : Mono S.kernelToL₀X₁ := mono_of_mono_fac S.kernelToL₀X₁_comp_v₀₁
  apply KernelFork.IsLimit.ofι'
  intro T t ht
  let lift := KernelFork.IsLimit.lift' (kernelIsKernel S.L₁.f)
    (t ≫ S.v₀₁.τ₁) (by
      rw [Category.assoc, S.v₀₁.comm₁₂, ← Category.assoc, ht, zero_comp])
  refine ⟨lift.1, ?_⟩
  apply (cancel_mono S.v₀₁.τ₁).mp
  rw [Category.assoc, S.kernelToL₀X₁_comp_v₀₁]
  exact lift.2

/-- The last vertical cokernel descends to the cokernel of the lower-right arrow. -/
noncomputable def L₃X₃ToCokernel : S.L₃.X₃ ⟶ cokernel S.L₂.g :=
  (CokernelCofork.IsColimit.desc' S.h₃τ₃ (cokernel.π S.L₂.g) (by
    apply (cancel_epi S.L₁.g).mp
    rw [← Category.assoc, ← S.v₁₂.comm₂₃, Category.assoc,
      cokernel.condition, comp_zero, comp_zero])).1

/-- The right endpoint map factors the lower-right cokernel projection. -/
@[reassoc (attr := simp)]
theorem v₂₃_comp_L₃X₃ToCokernel :
    S.v₂₃.τ₃ ≫ S.L₃X₃ToCokernel = cokernel.π S.L₂.g :=
  (CokernelCofork.IsColimit.desc' S.h₃τ₃ (cokernel.π S.L₂.g) (by
    apply (cancel_epi S.L₁.g).mp
    rw [← Category.assoc, ← S.v₁₂.comm₂₃, Category.assoc,
      cokernel.condition, comp_zero, comp_zero])).2

/-- The last cokernel-row arrow vanishes after the right endpoint map. -/
@[reassoc (attr := simp)]
theorem g_comp_L₃X₃ToCokernel : S.L₃.g ≫ S.L₃X₃ToCokernel = 0 := by
  apply (cancel_epi S.v₂₃.τ₂).mp
  rw [← Category.assoc, S.v₂₃.comm₂₃, Category.assoc,
    S.v₂₃_comp_L₃X₃ToCokernel, cokernel.condition, comp_zero]

/-- The right endpoint map exhibits the cokernel of the last cokernel-row arrow. -/
noncomputable def L₃X₃ToCokernelIsCokernel :
    IsColimit (CokernelCofork.ofπ S.L₃X₃ToCokernel S.g_comp_L₃X₃ToCokernel) := by
  haveI : Epi S.L₃X₃ToCokernel := epi_of_epi_fac S.v₂₃_comp_L₃X₃ToCokernel
  apply CokernelCofork.IsColimit.ofπ'
  intro T t ht
  let desc := CokernelCofork.IsColimit.desc' (cokernelIsCokernel S.L₂.g)
    (S.v₂₃.τ₃ ≫ t) (by
      rw [← Category.assoc, ← S.v₂₃.comm₂₃, Category.assoc, ht, comp_zero])
  refine ⟨desc.1, ?_⟩
  apply (cancel_epi S.v₂₃.τ₃).mp
  rw [← Category.assoc, S.v₂₃_comp_L₃X₃ToCokernel]
  exact desc.2

/-- The eight objects of the extended snake sequence, with the two outer terms
retained even if they are nonzero. -/
noncomputable abbrev composableArrowsWithEndpoints : ComposableArrows C 7 :=
  ((ComposableArrows.mk₅ S.L₀.g S.δ S.L₃.f S.L₃.g S.L₃X₃ToCokernel).precomp
    S.L₀.f).precomp S.kernelToL₀X₁

/-- The first arrow of the extended snake sequence is the left endpoint map. -/
@[simp high]
theorem composableArrowsWithEndpoints_map_zero_one :
    S.composableArrowsWithEndpoints.map' 0 1 = S.kernelToL₀X₁ := rfl

/-- The last arrow of the extended snake sequence is the right endpoint map. -/
@[simp high]
theorem composableArrowsWithEndpoints_map_six_seven :
    S.composableArrowsWithEndpoints.map' 6 7 = S.L₃X₃ToCokernel := rfl

/-- The last object of the extended snake sequence is the lower-right cokernel. -/
@[simp high]
theorem composableArrowsWithEndpoints_obj_seven :
    S.composableArrowsWithEndpoints.obj' 7 = cokernel S.L₂.g := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Deleting the two outer objects gives Mathlib's original six-term diagram. -/
theorem composableArrowsWithEndpoints_middle :
    S.composableArrowsWithEndpoints.δ₀.δlast = S.composableArrows := by
  apply ComposableArrows.ext₅ (f := S.composableArrowsWithEndpoints.δ₀.δlast)
    (g := S.composableArrows) rfl rfl rfl rfl rfl rfl <;>
    (simp [ComposableArrows.Precomp.map, ComposableArrows.mk₅,
      ComposableArrows.mk₄, ComposableArrows.mk₃, ComposableArrows.mk₂,
      ComposableArrows.mk₁])

/-- Exactness at the four middle positions is Mathlib's snake lemma. -/
theorem composableArrowsWithEndpoints_middle_exact :
    S.composableArrowsWithEndpoints.δ₀.δlast.Exact := by
  rw [S.composableArrowsWithEndpoints_middle]
  exact S.snake_lemma

/-- The eight-object snake sequence of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, corrected second edition, (1.3.1), generalized
from abelian groups to arbitrary abelian categories: exactness at all six inner
objects without assuming either exterior object vanishes. -/
theorem snake_lemma_with_endpoints : S.composableArrowsWithEndpoints.Exact := by
  apply ComposableArrows.exact_of_δ₀
  · change (ComposableArrows.mk₂ S.kernelToL₀X₁ S.L₀.f).Exact
    exact (ShortComplex.exact_of_f_is_kernel
      (S := ShortComplex.mk S.kernelToL₀X₁ S.L₀.f S.kernelToL₀X₁_comp_f)
      S.kernelToL₀X₁IsKernel).exact_toComposableArrows
  · apply ComposableArrows.exact_of_δlast
    · exact S.composableArrowsWithEndpoints_middle_exact
    · change (ComposableArrows.mk₂ S.L₃.g S.L₃X₃ToCokernel).Exact
      exact (ShortComplex.exact_of_g_is_cokernel
        (S := ShortComplex.mk S.L₃.g S.L₃X₃ToCokernel S.g_comp_L₃X₃ToCokernel)
        S.L₃X₃ToCokernelIsCokernel).exact_toComposableArrows

end CategoryTheory.ShortComplex.SnakeInput
