/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageResolution

set_option warningAsError true

/-!
# Discreteness of native continuous cohomology

For a compact topological group and a discrete continuous representation, the
native homogeneous cochains, cocycles, and continuous cohomology are discrete in
every degree. No continuity of the action in both variables is required.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]

/-- Every degree of homogeneous cochains of a compact topological group with
discrete coefficients has the discrete topology. -/
theorem discreteTopology_homogeneousCochains (n : ℕ) :
    DiscreteTopology ((TopRep.homogeneousCochains X).X n) := by
  have : DiscreteTopology (TopRep.resolutionX X (n + 1)) :=
    discreteTopology_resolutionX X (n + 1)
  change DiscreteTopology ↥((TopRep.resolutionX X (n + 1)).ρ.invariants)
  infer_instance

private theorem discreteTopology_cocycles (n : ℕ) :
    DiscreteTopology ((TopRep.homogeneousCochains X).cycles n) := by
  let C := TopRep.homogeneousCochains X
  have : DiscreteTopology ((C.sc n).X₂) := by
    change DiscreteTopology (C.X n)
    exact discreteTopology_homogeneousCochains X n
  let differential := (C.sc n).g
  let fork := KernelFork.ofι (TopModuleCat.kerι differential)
    (TopModuleCat.kerι_comp differential)
  let e : TopModuleCat.ker differential ≅ C.cycles n :=
    (C.sc n).isoCyclesOfIsLimit (kf := fork) (TopModuleCat.isLimitKer differential)
  have : DiscreteTopology (TopModuleCat.ker differential) := by
    change DiscreteTopology differential.hom.ker
    exact DiscreteTopology.of_continuous_injective continuous_subtype_val Subtype.val_injective
  exact e.toContinuousLinearEquiv.toHomeomorph.discreteTopology

/-- Every degree of native continuous cohomology of a compact topological group
with a discrete coefficient representation has the discrete topology. -/
theorem discreteTopology_continuousCohomology (n : ℕ) :
    DiscreteTopology (continuousCohomology n X) := by
  let C := TopRep.homogeneousCochains X
  let S := C.sc n
  have : DiscreteTopology S.cycles := discreteTopology_cocycles X n
  let f : S.X₁ ⟶ S.cycles := S.toCycles
  let e : TopModuleCat.coker f ≅ S.homology :=
    IsColimit.coconePointUniqueUpToIso
      (TopModuleCat.isColimitCoker f) S.homologyIsCokernel
  have : DiscreteTopology (TopModuleCat.coker f) := by
    change DiscreteTopology (S.cycles ⧸ f.hom.range)
    apply discreteTopology_iff_forall_isOpen.mpr
    intro U
    exact (Submodule.isQuotientMap_mkQ f.hom.range).isOpen_preimage.mp (isOpen_discrete _)
  exact e.toContinuousLinearEquiv.toHomeomorph.discreteTopology

end ContinuousCohomology
