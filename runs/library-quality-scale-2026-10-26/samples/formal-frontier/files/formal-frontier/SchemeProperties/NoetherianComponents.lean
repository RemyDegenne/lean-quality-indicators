/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ConnectedComponents
public import SchemeProperties.Integral
public import SchemeProperties.Normal
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.JacobsonSpace

public section

/-!
# Connected components of Noetherian schemes

Noetherian spaces are locally connected, so a Noetherian scheme has finitely
many open connected components. This file equips each component open subscheme
with its connected and Noetherian instances and packages the components as an
open cover. In particular, normality may be checked componentwise, and every
component of a normal Noetherian scheme is integral. The file also proves that
closed-point homogeneous Noetherian Jacobson spaces have irreducible connected
components.

The component coproduct isomorphism itself is the more general
`Scheme.connectedComponentSigmaIso` from `SchemeProperties.ConnectedComponents`.

## References

- J. S. Milne, *Algebraic Groups* (2017), Appendix A.14, for the Noetherian
  finite-clopen-component fact used in component-algebra arguments.
- Mathlib's `NoetherianSpace.finite_irreducibleComponents`,
  `IsClopen.connectedComponent_subset` and `nonempty_inter_closedPoints` for
  the finite-component and closed-point methods used here.
-/

open Set Topology TopologicalSpace CategoryTheory

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Connected components of a Noetherian space are open. This is the openness
part of the finite-clopen-component fact in Milne, *Algebraic Groups* (2017),
Appendix A.14. The proof here uses Mathlib's finite irreducible components. -/
theorem NoetherianSpace.isOpen_connectedComponent [NoetherianSpace X]
    (x : X) : IsOpen (connectedComponent x) := by
  let S : Set (Set X) :=
    {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}
  have hSf : S.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun _ hZ ↦ hZ.1
  have hSc : IsClosed (⋃₀ S) := by
    rw [Set.sUnion_eq_biUnion]
    exact hSf.isClosed_biUnion fun Z hZ ↦
      isClosed_of_mem_irreducibleComponents Z hZ.1
  apply isClosed_compl_iff.mp
  rw [show (connectedComponent x)ᶜ = ⋃₀ S by
    apply Set.Subset.antisymm
    · intro y hy
      refine Set.mem_sUnion_of_mem mem_irreducibleComponent ?_
      exact ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h ↦ hy (h mem_irreducibleComponent)⟩
    · intro y hy
      obtain ⟨Z, hZS, hyZ⟩ := Set.mem_sUnion.mp hy
      intro hyx
      apply hZS.2
      have hZy : Z ⊆ connectedComponent y :=
        hZS.1.1.isConnected.subset_connectedComponent hyZ
      rw [connectedComponent_eq hyx]
      exact hZy]
  exact hSc

/-- Every connected component of a closed-point homogeneous Noetherian Jacobson
space is irreducible. -/
theorem isIrreducible_connectedComponent_of_closedPoints_homogeneous
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [JacobsonSpace X]
    (hhom : ∀ x y : closedPoints X, ∃ e : X ≃ₜ X, e x.1 = y.1)
    (x : X) : IsIrreducible (connectedComponent x) := by
  let Z := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X :=
    irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨U, hUo, hUne, hUZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨z, hzU, hzc⟩ :=
    nonempty_inter_closedPoints hUne hUo.isLocallyClosed
  let zc : closedPoints X := ⟨z, hzc⟩
  have hz_unique (W : Set X) (hW : W ∈ irreducibleComponents X) (hzW : z ∈ W) :
      W = Z := by
    have hWZ : W ⊆ Z :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hW.1.2 hUo
        ⟨z, hzW, hzU⟩).trans <|
        closure_minimal (fun _ hy ↦ hUZ hy.2)
          (isClosed_of_mem_irreducibleComponents Z hZ)
    exact Set.Subset.antisymm hWZ (hW.2 hZ.1 hWZ)
  have hclosed_unique (q : closedPoints X) (W V : Set X)
      (hW : W ∈ irreducibleComponents X) (hV : V ∈ irreducibleComponents X)
      (hqW : q.1 ∈ W) (hqV : q.1 ∈ V) : W = V := by
    obtain ⟨e, he⟩ := hhom zc q
    have hpreW : e ⁻¹' W ∈ irreducibleComponents X :=
      preimage_mem_irreducibleComponents hW e.isOpenEmbedding <| by
        rw [e.surjective.range_eq, Set.inter_univ]
        exact hW.1.1
    have hpreV : e ⁻¹' V ∈ irreducibleComponents X :=
      preimage_mem_irreducibleComponents hV e.isOpenEmbedding <| by
        rw [e.surjective.range_eq, Set.inter_univ]
        exact hV.1.1
    have hzpreW : z ∈ e ⁻¹' W := by
      change e z ∈ W
      rw [show e z = q.1 by simpa [zc] using he]
      exact hqW
    have hzpreV : z ∈ e ⁻¹' V := by
      change e z ∈ V
      rw [show e z = q.1 by simpa [zc] using he]
      exact hqV
    apply e.surjective.preimage_injective
    exact (hz_unique _ hpreW hzpreW).trans (hz_unique _ hpreV hzpreV).symm
  have hcomponents_eq_of_nonempty_inter (W V : Set X)
      (hW : W ∈ irreducibleComponents X) (hV : V ∈ irreducibleComponents X)
      (hWV : (W ∩ V).Nonempty) : W = V := by
    obtain ⟨q, ⟨hqW, hqV⟩, hqc⟩ := nonempty_inter_closedPoints hWV <|
      ((isClosed_of_mem_irreducibleComponents W hW).inter
        (isClosed_of_mem_irreducibleComponents V hV)).isLocallyClosed
    exact hclosed_unique ⟨q, hqc⟩ W V hW hV hqW hqV
  have hZcompl : Zᶜ = ⋃₀ (irreducibleComponents X \ {Z}) := by
    apply Set.Subset.antisymm
    · intro y hy
      refine Set.mem_sUnion_of_mem mem_irreducibleComponent ⟨
        irreducibleComponent_mem_irreducibleComponents y, ?_⟩
      rw [Set.mem_singleton_iff]
      intro hyZ
      exact hy (hyZ ▸ mem_irreducibleComponent)
    · intro y hy hyZ
      obtain ⟨W, ⟨hW, hWZ⟩, hyW⟩ := Set.mem_sUnion.mp hy
      exact hWZ <| Set.mem_singleton_iff.mpr <|
        hcomponents_eq_of_nonempty_inter W Z hW hZ ⟨y, hyW, hyZ⟩
  have hZopen : IsOpen Z := by
    apply isClosed_compl_iff.mp
    rw [hZcompl, Set.sUnion_eq_biUnion]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  rw [show connectedComponent x = Z by
    apply Set.Subset.antisymm
    · exact IsClopen.connectedComponent_subset
        (⟨isClosed_of_mem_irreducibleComponents Z hZ, hZopen⟩ : IsClopen Z)
        mem_irreducibleComponent
    · exact irreducibleComponent_subset_connectedComponent]
  exact hZ.1

/-- Every Noetherian topological space is locally connected. -/
instance NoetherianSpace.toLocallyConnectedSpace [NoetherianSpace X] :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF x hx
  rw [connectedComponentIn_eq_image hx]
  exact hF.isOpenMap_subtype_val _
    (NoetherianSpace.isOpen_connectedComponent (⟨x, hx⟩ : F))

namespace AlgebraicGeometry

/-- A connected-component open subscheme of a Noetherian scheme is connected. -/
instance Scheme.connectedComponentOpen.connectedSpace
    (X : Scheme.{u}) [IsNoetherian X] (c : ConnectedComponents X) :
    ConnectedSpace (X.connectedComponentOpen c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  apply Subtype.connectedSpace
  change _root_.IsConnected
    (X.connectedComponentOpen (ConnectedComponents.mk x) : Set X)
  rw [X.connectedComponentOpen_mk x]
  exact isConnected_connectedComponent

/-- A connected-component open subscheme of a Noetherian scheme is Noetherian. -/
instance Scheme.connectedComponentOpen.isNoetherian
    (X : Scheme.{u}) [IsNoetherian X] (c : ConnectedComponents X) :
    IsNoetherian (X.connectedComponentOpen c) where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := by
    let _ : NoetherianSpace (X.connectedComponentOpen c) :=
      NoetherianSpace.set (X.connectedComponentOpen c : Set X)
    exact inferInstance

/-- The open cover of a Noetherian scheme by its connected components. -/
def Scheme.connectedComponentOpenCover (X : Scheme.{u}) [IsNoetherian X] :
    X.OpenCover where
  I₀ := ConnectedComponents X
  X c := X.connectedComponentOpen c
  f c := (X.connectedComponentOpen c).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨ConnectedComponents.mk x,
      ⟨x, X.mem_connectedComponentOpen _ _ |>.mpr rfl⟩, rfl⟩, ?_⟩
    exact fun _ ↦ inferInstance

/-- A Noetherian scheme is normal if and only if all its connected-component
open subschemes are normal. -/
theorem IsNormal.iff_connectedComponentOpen (X : Scheme.{u}) [IsNoetherian X] :
    IsNormal X ↔ ∀ c : ConnectedComponents X, IsNormal (X.connectedComponentOpen c) := by
  constructor
  · intro h
    let _ : IsNormal X := h
    exact fun _ ↦ inferInstance
  · intro h
    let _ : ∀ i : X.connectedComponentOpenCover.I₀,
        IsNormal (X.connectedComponentOpenCover.X i) := fun c ↦ by
      change IsNormal (X.connectedComponentOpen c)
      exact h c
    exact IsNormal.of_openCover X X.connectedComponentOpenCover

/-- Every connected component of a normal Noetherian scheme is integral. -/
instance Scheme.connectedComponentOpen.isIntegral
    (X : Scheme.{u}) [IsNoetherian X] [IsNormal X]
    (c : ConnectedComponents X) : IsIntegral (X.connectedComponentOpen c) :=
  isIntegral_of_isNoetherian_of_connectedSpace_of_stalk_isDomain _

end AlgebraicGeometry
