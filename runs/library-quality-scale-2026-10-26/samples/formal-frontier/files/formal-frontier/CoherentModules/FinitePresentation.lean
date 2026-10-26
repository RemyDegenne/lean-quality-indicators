/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formal Frontier AI agents
-/
module

public import CoherentModules.Basic

/-!
# Finitely presented modules over coherent rings

This file identifies finitely presented modules with coherent modules over a
coherent ring and deduces finite presentation of kernels between them.  The
results hold for arbitrary rings and modules in independent universes.  It also
gives a five-term exact-sequence criterion for finite presentation of the
middle module.

## Main declarations

* `Module.FinitePresentation.isCoherent`: a finitely presented module over a
  coherent ring is coherent.
* `Module.isCoherent_iff_finitePresentation`: coherence is equivalent to finite
  presentation over a coherent ring.
* `Module.FinitePresentation.ker`: the kernel of a map between finitely
  presented modules over a coherent ring is finitely presented.
* `Module.FinitePresentation.of_exact_five`: in a sequence of five modules
  exact at the middle three, suitable finiteness hypotheses on the other four
  imply finite presentation of the middle module.
-/

@[expose] public section

universe u v w v1 v2 v3 v4 v5

namespace Module

variable {R : Type u} [Ring R]

namespace FinitePresentation

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finitely presented module over a coherent ring is coherent. -/
theorem isCoherent [IsCoherentRing R] [Module.FinitePresentation R M] :
    Module.IsCoherent R M := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
  let _ : Module.IsCoherent R (Fin n → R) := Module.IsCoherent.of_free R
  let _ : Module.IsCoherent R ((Fin n → R) ⧸ K) :=
    Module.IsCoherent.quotient K hK
  exact Module.IsCoherent.of_equiv e.symm

/-- The kernel of a linear map between finitely presented modules over a
coherent ring is finitely presented. -/
theorem ker [IsCoherentRing R]
    {N : Type w} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) : Module.FinitePresentation R (LinearMap.ker f) := by
  let _ : Module.IsCoherent R M := Module.FinitePresentation.isCoherent
  let _ : Module.IsCoherent R N := Module.FinitePresentation.isCoherent
  exact Module.IsCoherent.finitePresentation_ker f

/-- In a sequence of five modules that is exact at the middle three, the middle
module is finitely presented if the first module is finite and the second,
fourth, and fifth modules are finitely presented. -/
theorem of_exact_five [IsCoherentRing R]
    {M1 : Type v1} {M2 : Type v2} {M3 : Type v3}
    {M4 : Type v4} {M5 : Type v5}
    [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2]
    [AddCommGroup M3] [Module R M3]
    [AddCommGroup M4] [Module R M4]
    [AddCommGroup M5] [Module R M5]
    [Module.Finite R M1]
    [Module.FinitePresentation R M2]
    [Module.FinitePresentation R M4]
    [Module.FinitePresentation R M5]
    (f12 : M1 →ₗ[R] M2) (f23 : M2 →ₗ[R] M3)
    (f34 : M3 →ₗ[R] M4) (f45 : M4 →ₗ[R] M5)
    (h2 : Function.Exact f12 f23)
    (h3 : Function.Exact f23 f34)
    (h4 : Function.Exact f34 f45) :
    Module.FinitePresentation R M3 := by
  let _ : Module.FinitePresentation R (LinearMap.range f23) :=
    Module.finitePresentation_of_surjective f23.rangeRestrict
      (LinearMap.surjective_rangeRestrict f23) (by
        rw [LinearMap.ker_rangeRestrict, h2.linearMap_ker_eq]
        exact Submodule.fg_range f12)
  let _ : Module.FinitePresentation R (LinearMap.ker f34) := by
    rw [h3.linearMap_ker_eq]
    infer_instance
  let _ : Module.FinitePresentation R (LinearMap.range f34) := by
    rw [← h4.linearMap_ker_eq]
    exact Module.FinitePresentation.ker f45
  let _ : Module.FinitePresentation R (LinearMap.ker f34.rangeRestrict) := by
    rw [LinearMap.ker_rangeRestrict]
    infer_instance
  exact Module.finitePresentation_of_ker f34.rangeRestrict
    (LinearMap.surjective_rangeRestrict f34)

end FinitePresentation

/-- Over a coherent ring, a module is coherent exactly when it is finitely
presented. -/
theorem isCoherent_iff_finitePresentation
    {M : Type v} [AddCommGroup M] [Module R M] [IsCoherentRing R] :
    Module.IsCoherent R M ↔ Module.FinitePresentation R M := by
  constructor
  · intro h
    let _ : Module.IsCoherent R M := h
    infer_instance
  · intro h
    let _ : Module.FinitePresentation R M := h
    exact Module.FinitePresentation.isCoherent

end Module
