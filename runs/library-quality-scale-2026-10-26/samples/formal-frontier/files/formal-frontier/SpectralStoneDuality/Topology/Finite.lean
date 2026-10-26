/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Sober
public import Mathlib.Topology.Spectral.Basic

/-!
# Generic points and spectral finite spaces

Every finite irreducible subset of a topological space contains a generic point of its
closure. Consequently, every finite topological space is quasi-sober, without any
separation or nonemptiness assumption. Every finite T₀ topological space is spectral,
including the empty space.

## References

- Mathlib, `Topology.Sober` and `Topology.Spectral.Basic`, for the formalized
  generic-point, quasi-sobriety and spectral-space notions. The finite-set
  generic-point argument is supplied here, rather than imported as a theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- A finite irreducible set contains a generic point of its closure. -/
theorem IsIrreducible.exists_isGenericPoint_closure_of_finite
    {X : Type u} [TopologicalSpace X] {s : Set X} (hs : IsIrreducible s)
    (hfinite : s.Finite) : ∃ x ∈ s, IsGenericPoint x (closure s) := by
  let t : Finset (Set X) := hfinite.toFinset.image fun x => closure {x}
  have hclosed : ∀ z ∈ t, IsClosed z := by
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact isClosed_closure
  have hcover : s ⊆ ⋃₀ (t : Set (Set X)) := by
    intro x hx
    apply Set.mem_sUnion.mpr
    exact ⟨closure {x}, Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨x, hfinite.mem_toFinset.mpr hx, rfl⟩),
      subset_closure (Set.mem_singleton x)⟩
  obtain ⟨z, hz, hsz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hs) t hclosed hcover
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have hxs : x ∈ s := hfinite.mem_toFinset.mp hx
  refine ⟨x, hxs, ?_⟩
  apply Set.Subset.antisymm
  · exact closure_mono (Set.singleton_subset_iff.mpr hxs)
  · simpa only [closure_closure] using closure_mono hsz

/-- A finite irreducible closed set contains a generic point. -/
theorem IsIrreducible.exists_isGenericPoint_of_finite
    {X : Type u} [TopologicalSpace X] {s : Set X} (hs : IsIrreducible s)
    (hfinite : s.Finite) (hclosed : IsClosed s) :
    ∃ x ∈ s, IsGenericPoint x s := by
  simpa only [hclosed.closure_eq] using hs.exists_isGenericPoint_closure_of_finite hfinite

/-- Every finite topological space is quasi-sober. -/
instance (priority := 90) instQuasiSoberOfFinite
    (X : Type u) [TopologicalSpace X] [Finite X] : QuasiSober X where
  sober hs hclosed := by
    obtain ⟨x, _, hx⟩ := hs.exists_isGenericPoint_of_finite (Set.toFinite _) hclosed
    exact ⟨x, hx⟩

/-- A finite T₀ topological space is spectral, including the empty space. -/
instance (priority := 90) instSpectralSpaceOfFinite
    (X : Type u) [TopologicalSpace X] [Finite X] [T0Space X] : SpectralSpace X where
  __ := (inferInstance : T0Space X)
  __ := (inferInstance : CompactSpace X)
  __ := (inferInstance : QuasiSober X)
  __ := (inferInstance : QuasiSeparatedSpace X)
  __ := (inferInstance : PrespectralSpace X)
