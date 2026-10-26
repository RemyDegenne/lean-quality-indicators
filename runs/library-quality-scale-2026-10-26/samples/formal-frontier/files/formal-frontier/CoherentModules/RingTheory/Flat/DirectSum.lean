/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Faithful flatness of dependent direct sums

A dependent direct sum is faithfully flat precisely when every component is
flat and each proper ideal of the coefficient ring has a nontrivial
quotient-tensor fiber in at least one component. The detecting component may
depend on the ideal. One faithfully flat component is sufficient when all
components are flat, but is not necessary.

The ring, index type and module carriers have independent universes. Empty
index types and subsingleton coefficient rings are allowed.

## References

The characterization follows Mathlib's proper-ideal criterion for faithful
flatness, flatness of direct sums, tensor distribution over direct sums, and
quotient-tensor equivalences. The component constructor uses the surjective
linear-map constructor for faithful flatness.
-/

@[expose] public section

open scoped DirectSum TensorProduct

universe u v w

namespace Module.FaithfullyFlat

private theorem nontrivial_directSum_iff
    {ι : Type v} (N : ι → Type w) [∀ i, AddCommMonoid (N i)] :
    Nontrivial (⨁ i, N i) ↔ ∃ i, Nontrivial (N i) := by
  classical
  constructor
  · intro h
    let : Nontrivial (⨁ i, N i) := h
    obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := ⨁ i, N i)
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (DirectSum.ext h)
    exact ⟨i, ⟨x i, y i, hi⟩⟩
  · rintro ⟨i, hi⟩
    let : Nontrivial (N i) := hi
    exact (DirectSum.of_injective (β := N) i).nontrivial

/-- A dependent direct sum is faithfully flat if and only if every component
is flat and every proper ideal has a nontrivial quotient-tensor fiber in at
least one component. The detecting component may depend on the ideal. -/
theorem directSum_iff
    (R : Type u) {ι : Type v} (M : ι → Type w)
    [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Module.FaithfullyFlat R (⨁ i, M i) ↔
      (∀ i, Module.Flat R (M i)) ∧
        ∀ I : Ideal R, I ≠ ⊤ → ∃ i, Nontrivial ((R ⧸ I) ⊗[R] M i) := by
  classical
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal, Module.Flat.directSum_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun I ↦ imp_congr_right fun _ ↦ ?_
  exact Submodule.Quotient.nontrivial_iff.symm.trans <|
    (TensorProduct.quotTensorEquivQuotSMul (⨁ i, M i) I).toEquiv.nontrivial_congr.symm.trans <|
    (TensorProduct.directSumRight R R (R ⧸ I) M).toEquiv.nontrivial_congr.trans <|
    nontrivial_directSum_iff _

/-- A dependent direct sum of flat modules is faithfully flat if one chosen
component is faithfully flat. -/
theorem directSum_of_component
    {R : Type u} {ι : Type v} (M : ι → Type w)
    [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] (i : ι) [Module.FaithfullyFlat R (M i)] :
    Module.FaithfullyFlat R (⨁ j, M j) := by
  classical
  apply Module.FaithfullyFlat.of_surjective (DirectSum.component R ι M i)
  intro x
  exact ⟨DirectSum.lof R ι M i x, DirectSum.component.lof_self R (M := M) i x⟩

end Module.FaithfullyFlat
