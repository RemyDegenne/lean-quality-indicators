/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-!
# Endomorphisms congruent to the identity

An endomorphism pointwise congruent to the identity modulo `I • ⊤` is injective
on an `I`-adically Hausdorff module and is a unit on an `I`-adically complete
module. The ideal and module are arbitrary; no finiteness assumptions or
completeness of the endomorphism module are needed.

Surjectivity follows from Mathlib's `surjective_of_mkQ_comp_surjective` on the
original module. For injectivity, the difference from the identity raises the
ideal-power filtration, so separatedness kills the kernel. The standard
`Module.End.isUnit_iff` supplies the unit and its existing inverse API.

On the regular module `M = R`, with `f = r • LinearMap.id`, the pointwise
hypothesis is equivalent to `r - 1 ∈ I`. The existing equivalence
`(RingEquiv.toOpposite R).trans (RingEquiv.moduleEndSelf R)` sends `r` to the
same endomorphism: its action is `x ↦ x * r`, equal to `x ↦ r * x` by
commutativity. Applying `MulEquiv.isUnit_map` identifies its unit predicate
with `IsUnit r`. This recovers the scalar unit criterion from
`IsAdicComplete.le_jacobson_bot` and
`Ideal.isUnit_of_sub_one_mem_jacobson_bot`, without a second scalar theorem.

## References

The adic-completion framework and quotient-surjectivity argument are from
Mathlib's `RingTheory.AdicCompletion.Basic` and
`RingTheory.AdicCompletion.Functoriality`, formalized by Kenny Lau, Judith
Ludwig, Christian Merten and Jiedong Jiang. The unit characterization and
regular-module equivalence use Mathlib's linear-map and linear-equivalence API.
-/

@[expose] public section

universe u v

namespace Module.End

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- An endomorphism congruent to the identity modulo `I` is injective on an
`I`-adically Hausdorff module. -/
theorem injective_of_sub_mem_smul (I : Ideal R) [IsHausdorff I M]
    (f : Module.End R M) (hf : ∀ m, f m - m ∈ I • (⊤ : Submodule R M)) :
    Function.Injective f := by
  let g : Module.End R M := f - 1
  have hg : (⊤ : Submodule R M).map g ≤ I • (⊤ : Submodule R M) := by
    rw [Submodule.map_le_iff_le_comap]
    intro x _
    exact hf x
  have hstep (n : ℕ) :
      (I ^ n • (⊤ : Submodule R M)).map g ≤ I ^ (n + 1) • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'', pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mono le_rfl hg
  have hzero (x : M) (hx : f x = 0) : x = 0 := by
    apply IsHausdorff.haus' (I := I) x
    intro n
    apply SModEq.zero.mpr
    induction n with
    | zero =>
        simpa only [pow_zero, Ideal.one_eq_top, Submodule.top_smul] using
          (Submodule.mem_top : x ∈ (⊤ : Submodule R M))
    | succ n hn =>
        have hgx := hstep n (Submodule.mem_map_of_mem hn)
        have hneg : -x ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
          simpa only [g, LinearMap.sub_apply, Module.End.one_apply, hx, zero_sub] using hgx
        simpa only [neg_neg] using
          (I ^ (n + 1) • (⊤ : Submodule R M)).neg_mem hneg
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

/-- An endomorphism of an `I`-adically complete module is a unit if its difference
from the identity takes every element into `I • ⊤`.

Mathlib's `surjective_of_mkQ_comp_surjective` gives surjectivity on the original
module from the induced quotient map. Hausdorffness gives injectivity, and
Mathlib's `Module.End.isUnit_iff` then supplies the unit. -/
theorem isUnit_of_sub_mem_smul (I : Ideal R) [IsAdicComplete I M]
    (f : Module.End R M) (hf : ∀ m, f m - m ∈ I • (⊤ : Submodule R M)) :
    IsUnit f := by
  have hq : Function.Surjective ((I • (⊤ : Submodule R M)).mkQ.comp f) := by
    intro q
    obtain ⟨m, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective q
    refine ⟨m, ?_⟩
    exact (Submodule.Quotient.eq _).2 (hf m)
  exact (Module.End.isUnit_iff f).2
    ⟨Module.End.injective_of_sub_mem_smul (I := I) (f := f) hf,
      surjective_of_mkQ_comp_surjective (I := I) (f := f) hq⟩

end Module.End
