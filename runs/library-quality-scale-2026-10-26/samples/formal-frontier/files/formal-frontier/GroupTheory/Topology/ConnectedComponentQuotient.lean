/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Connected.Clopen

/-!
# Quotient by the connected component of the identity

For a topological group `G`, the quotient by `Subgroup.connectedComponentOfOne G`
is Hausdorff and totally disconnected, even when `G` is not Hausdorff.
Every continuous group homomorphism from `G` into a totally disconnected group
factors uniquely and continuously through the canonical quotient map. The
target group need not have continuous multiplication or inversion.

This continuous universal property is a precise interpretation of the largest
totally disconnected quotient in Neukirch--Schmidt--Wingberg, *Cohomology of
Number Fields*, corrected second edition, Chapter I, §1, (1.1.9)(i). It holds
without local compactness. The printed assertion that the identity component
is the intersection of all open normal subgroups is not used here; that
assertion is false for general locally compact groups.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, electronic version 2.3 (May 2020), Chapter I, §1,
  (1.1.9)(i) and its preceding paragraph, printed p. 8 / PDF p. 22.
* Mathlib's `Subgroup.connectedComponentOfOne`, `QuotientGroup.lift`,
  `QuotientGroup.instT3Space` and `Topology.IsCoinducing.image_connectedComponent`.
-/

@[expose] public section

universe u v w

namespace Subgroup

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The identity component is normal in every topological group; compare the
paragraph preceding Neukirch--Schmidt--Wingberg, (1.1.9)(i). -/
instance normal_connectedComponentOfOne : (connectedComponentOfOne G).Normal := by
  refine ⟨fun element helement conjugator => ?_⟩
  have hconnected : IsConnected
      ((fun component : G => conjugator * component * conjugator⁻¹) ''
        connectedComponent (1 : G)) :=
    isConnected_connectedComponent.image _
      (IsTopologicalGroup.continuous_conj conjugator).continuousOn
  apply hconnected.subset_connectedComponent
    (show (1 : G) ∈ _ from ⟨1, mem_connectedComponent, by simp⟩)
  exact ⟨element, helement, rfl⟩

/-- The identity component is closed without a separation hypothesis, as in the
paragraph preceding Neukirch--Schmidt--Wingberg, (1.1.9)(i). -/
instance isClosed_connectedComponentOfOne :
    IsClosed ((connectedComponentOfOne G : Subgroup G) : Set G) := by
  change IsClosed (connectedComponent (1 : G))
  exact isClosed_connectedComponent

variable {H : Type v} [Group H] [TopologicalSpace H] [TotallyDisconnectedSpace H]

/-- A continuous homomorphism to a totally disconnected group kills the identity component. -/
theorem connectedComponentOfOne_le_ker (hom : G →ₜ* H) :
    connectedComponentOfOne G ≤ hom.toMonoidHom.ker := by
  intro element helement
  have himage := hom.continuous_toFun.image_connectedComponent_eq_singleton (1 : G)
  have hmem : (hom.toMonoidHom : G → H) element ∈
      (hom.toMonoidHom : G → H) '' connectedComponent (1 : G) :=
    ⟨element, helement, rfl⟩
  have hvalue : (hom.toMonoidHom : G → H) element =
      (hom.toMonoidHom : G → H) (1 : G) :=
    Set.mem_singleton_iff.mp (himage ▸ hmem)
  change (hom.toMonoidHom : G → H) element = 1
  simpa only [map_one] using hvalue

end Subgroup

namespace QuotientGroup

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The ordinary quotient of a topological group by its identity component. -/
abbrev connectedComponentQuotient := G ⧸ Subgroup.connectedComponentOfOne G

/-- The quotient by the identity component is totally disconnected. The
Hausdorff topology follows from Mathlib's closed-normal quotient instances.
Neukirch--Schmidt--Wingberg, (1.1.9)(i), states the locally compact case;
this result does not require local compactness. -/
instance instTotallyDisconnectedSpaceConnectedComponentQuotient :
    TotallyDisconnectedSpace (connectedComponentQuotient G) := by
  have hfibers : ∀ quotient : connectedComponentQuotient G,
      IsConnected ((QuotientGroup.mk : G → connectedComponentQuotient G) ⁻¹' {quotient}) := by
    intro quotient
    rcases QuotientGroup.mk_surjective quotient with ⟨representative, rfl⟩
    have hfiber : ((QuotientGroup.mk : G → connectedComponentQuotient G) ⁻¹'
        {(representative : connectedComponentQuotient G)}) =
        (fun component : G => representative * component) '' connectedComponent (1 : G) := by
      ext element
      constructor
      · intro helement
        have heq : (representative : connectedComponentQuotient G) = element :=
          (Set.mem_singleton_iff.mp helement).symm
        rcases (QuotientGroup.mk'_eq_mk' (Subgroup.connectedComponentOfOne G)).mp heq with
          ⟨component, hcomponent, rfl⟩
        exact ⟨component, hcomponent, rfl⟩
      · rintro ⟨component, hcomponent, rfl⟩
        exact ((QuotientGroup.mk'_eq_mk' (Subgroup.connectedComponentOfOne G)).mpr
          ⟨component, hcomponent, rfl⟩).symm
    rw [hfiber]
    exact isConnected_connectedComponent.image _
      (continuous_const_mul representative).continuousOn
  apply totallyDisconnectedSpace_iff_connectedComponent_one.mpr
  have himage :=
    (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isCoinducing.image_connectedComponent
      hfibers (1 : G))
  have htop : QuotientGroup.mk '' connectedComponent (1 : G) =
      ({(1 : connectedComponentQuotient G)} : Set (connectedComponentQuotient G)) := by
    ext quotient
    constructor
    · rintro ⟨element, helement, rfl⟩
      exact QuotientGroup.eq_one_iff element |>.mpr helement
    · intro hquotient
      have hquotient' : quotient = 1 := Set.mem_singleton_iff.mp hquotient
      exact ⟨1, mem_connectedComponent, by simpa using hquotient'.symm⟩
  simpa only [QuotientGroup.mk_one] using himage.symm.trans htop

/-- The canonical continuous homomorphism to the identity-component quotient. -/
def connectedComponentQuotientMk : G →ₜ* connectedComponentQuotient G where
  toMonoidHom := mk' (Subgroup.connectedComponentOfOne G)
  continuous_toFun := continuous_mk

@[simp]
theorem connectedComponentQuotientMk_apply (element : G) :
    connectedComponentQuotientMk G element =
      (element : connectedComponentQuotient G) := rfl

variable {G}
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- Descend a continuous homomorphism to a totally disconnected group through
the quotient by the identity component. This continuous universal property
interprets and generalizes Neukirch--Schmidt--Wingberg, (1.1.9)(i), rather than
quoting a printed theorem: local compactness and continuity of target operations
are not needed. -/
def connectedComponentQuotientLift [TotallyDisconnectedSpace H] (hom : G →ₜ* H) :
    connectedComponentQuotient G →ₜ* H where
  toMonoidHom := QuotientGroup.lift (Subgroup.connectedComponentOfOne G)
    hom.toMonoidHom (Subgroup.connectedComponentOfOne_le_ker G hom)
  continuous_toFun := by
    apply QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    change Continuous (fun element : G => hom element)
    exact hom.continuous_toFun

variable [TotallyDisconnectedSpace H]

@[simp]
theorem connectedComponentQuotientLift_mk_apply (hom : G →ₜ* H) (element : G) :
    connectedComponentQuotientLift hom (connectedComponentQuotientMk G element) =
      hom element := by
  rfl

/-- The factorization agrees with the original homomorphism after projection. -/
theorem connectedComponentQuotientLift_comp_mk (hom : G →ₜ* H) :
    (connectedComponentQuotientLift hom).comp (connectedComponentQuotientMk G) = hom := by
  ext element
  exact connectedComponentQuotientLift_mk_apply hom element

/-- A continuous homomorphism out of the quotient is determined by its
composite with the canonical projection. -/
theorem connectedComponentQuotientLift_unique (hom : G →ₜ* H)
    (candidate : connectedComponentQuotient G →ₜ* H)
    (hcandidate : candidate.comp (connectedComponentQuotientMk G) = hom) :
    candidate = connectedComponentQuotientLift hom := by
  ext quotient
  induction quotient using QuotientGroup.induction_on with
  | _ element =>
    calc
      candidate (element : connectedComponentQuotient G) = hom element := by
        exact congrArg (fun map : G →ₜ* H => map element) hcandidate
      _ = connectedComponentQuotientLift hom (element : connectedComponentQuotient G) :=
        (connectedComponentQuotientLift_mk_apply hom element).symm

variable {K : Type w} [Group K] [TopologicalSpace K] [TotallyDisconnectedSpace K]

/-- Factoring commutes with postcomposition by continuous homomorphisms. -/
theorem connectedComponentQuotientLift_comp (hom : G →ₜ* H) (posthom : H →ₜ* K) :
    connectedComponentQuotientLift (posthom.comp hom) =
      posthom.comp (connectedComponentQuotientLift hom) := by
  symm
  apply connectedComponentQuotientLift_unique (posthom.comp hom) _
  ext element
  change posthom (connectedComponentQuotientLift hom
    (connectedComponentQuotientMk G element)) = posthom (hom element)
  exact
    congrArg posthom (connectedComponentQuotientLift_mk_apply hom element)

/-- Continuous homomorphisms to a totally disconnected group correspond to
continuous homomorphisms out of the identity-component quotient. This packages
the interpretation of Neukirch--Schmidt--Wingberg, (1.1.9)(i), supplied by
`connectedComponentQuotientLift`, without local compactness. -/
def connectedComponentQuotientHomEquiv :
    (G →ₜ* H) ≃ (connectedComponentQuotient G →ₜ* H) where
  toFun := connectedComponentQuotientLift
  invFun := fun candidate => candidate.comp (connectedComponentQuotientMk G)
  left_inv := by
    intro hom
    exact connectedComponentQuotientLift_comp_mk hom
  right_inv := by
    intro candidate
    exact (connectedComponentQuotientLift_unique _ candidate rfl).symm

@[simp]
theorem connectedComponentQuotientHomEquiv_apply (hom : G →ₜ* H) :
    connectedComponentQuotientHomEquiv hom = connectedComponentQuotientLift hom := rfl

@[simp]
theorem connectedComponentQuotientHomEquiv_symm_apply
    (candidate : connectedComponentQuotient G →ₜ* H) :
    connectedComponentQuotientHomEquiv.symm candidate =
      candidate.comp (connectedComponentQuotientMk G) := rfl

end QuotientGroup

end
