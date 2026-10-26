/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.CompactAddCommGroup
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-!
# Compact finite products and three-term homology

This file equips a finite `Finsupp` product of a compact Hausdorff additive
commutative group with the topology transported from the corresponding finite
function space.  It also packages the closed-kernel/closed-range presentation
of the homology of a continuous three-term complex.

No scalar-ring topology is used.  Instantiation for finite bar complexes and
comparison with algebraic homology are separate later layers.
-/

public section

set_option warningAsError true

open CategoryTheory Topology

namespace CompHausAddCommGrp

universe u

/-- The finite-product topology on finitely supported functions, transported
from the equivalent finite function space. -/
@[instance_reducible, expose]
noncomputable def finiteFinsuppTopology (X : CompHausAddCommGrp.{u})
    (I : Type u) [Finite I] : TopologicalSpace (I →₀ X) :=
  TopologicalSpace.induced Finsupp.equivFunOnFinite inferInstance

/-- The defining homeomorphism from finite-support functions to the finite
function space. -/
noncomputable def finiteFinsuppHomeomorph (X : CompHausAddCommGrp.{u})
    (I : Type u) [Finite I] :
    @Homeomorph (I →₀ X) (I → X) (finiteFinsuppTopology X I) inferInstance := by
  letI : TopologicalSpace (I →₀ X) := finiteFinsuppTopology X I
  exact Finsupp.equivFunOnFinite.toHomeomorphOfIsInducing
    (Topology.IsInducing.induced _)

/-- A finite product of a compact Hausdorff additive commutative group,
presented as a `Finsupp`. -/
@[expose] noncomputable def finiteFinsupp (X : CompHausAddCommGrp.{u})
    (I : Type u) [Finite I] : CompHausAddCommGrp.{u} := by
  letI : TopologicalSpace (I →₀ X) := finiteFinsuppTopology X I
  let e := finiteFinsuppHomeomorph X I
  let _ : CompactSpace (I →₀ X) := e.symm.compactSpace
  let _ : T2Space (I →₀ X) := e.symm.t2Space
  let _ : IsTopologicalAddGroup (I →₀ X) :=
    isTopologicalAddGroup_induced
      (Finsupp.linearEquivFunOnFinite ℤ X I).toLinearMap
  exact of (I →₀ X)

/-- An additive map between finite products is continuous if every
single-input/single-output matrix coefficient is continuous. -/
@[expose] noncomputable def finiteFinsuppMap
    (X Y : CompHausAddCommGrp.{u}) (I J : Type u) [Fintype I] [Fintype J]
    (f : (I →₀ X) →+ (J →₀ Y))
    (hf : ∀ i j, Continuous (fun x ↦ f (Finsupp.single i x) j)) :
    finiteFinsupp X I ⟶ finiteFinsupp Y J := by
  letI : TopologicalSpace (I →₀ X) := finiteFinsuppTopology X I
  letI : TopologicalSpace (J →₀ Y) := finiteFinsuppTopology Y J
  apply ConcreteCategory.ofHom
  refine
    { toAddMonoidHom := f
      continuous_toFun := ?_ }
  let eI : (I →₀ X) ≃ₜ (I → X) :=
    Finsupp.equivFunOnFinite.toHomeomorphOfIsInducing
      (Topology.IsInducing.induced _)
  let eJ : (J →₀ Y) ≃ₜ (J → Y) :=
    Finsupp.equivFunOnFinite.toHomeomorphOfIsInducing
      (Topology.IsInducing.induced _)
  have hcoord (j : J) :
      Continuous (fun x : I → X ↦ f (eI.symm x) j) := by
    have hsum :
        Continuous (fun x : I → X ↦ ∑ i, f (Finsupp.single i (x i)) j) :=
      continuous_finsetSum Finset.univ fun i _ ↦
        (hf i j).comp (continuous_apply i)
    convert hsum using 1
    funext x
    rw [show eI.symm x = Finsupp.equivFunOnFinite.symm x by rfl]
    rw [Finsupp.equivFunOnFinite_symm_eq_sum, map_sum]
    simp
  have hpi : Continuous (fun x : I → X ↦ eJ (f (eI.symm x))) :=
    continuous_pi hcoord
  have hcomp : Continuous (fun x : I →₀ X ↦ eJ (f x)) := by
    convert hpi.comp eI.continuous using 1
    funext x
    exact congrArg (fun z ↦ eJ (f z)) (eI.symm_apply_apply x).symm
  have hfinal := eJ.symm.continuous.comp hcomp
  have hfun : (eJ.symm ∘ fun x ↦ eJ (f x)) = fun x ↦ f x := by
    funext x
    exact eJ.symm_apply_apply (f x)
  rw [hfun] at hfinal
  exact hfinal

@[simp]
lemma finiteFinsuppMap_apply
    (X Y : CompHausAddCommGrp.{u}) (I J : Type u) [Fintype I] [Fintype J]
    (f : (I →₀ X) →+ (J →₀ Y))
    (hf : ∀ i j, Continuous (fun x ↦ f (Finsupp.single i x) j))
    (x : I →₀ X) : finiteFinsuppMap X Y I J f hf x = f x :=
  rfl

/-- Restrict the first boundary of a continuous three-term complex to the
closed kernel of the second boundary. -/
@[expose] noncomputable def boundaryToKernel
    {X₂ X₁ X₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) : X₂ ⟶ kernelGroup d₁ := by
  apply ConcreteCategory.ofHom
  exact
    { toAddMonoidHom :=
        { toFun := fun x ↦ ⟨d₂ x, hd x⟩
          map_zero' := by ext; simp
          map_add' := by intro x y; ext; simp }
      continuous_toFun := d₂.hom.continuous.subtype_mk _ }

@[simp]
lemma boundaryToKernel_apply
    {X₂ X₁ X₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) (x : X₂) :
    boundaryToKernel d₂ d₁ hd x = ⟨d₂ x, hd x⟩ :=
  rfl

/-- Compact Hausdorff homology of a continuous three-term complex. -/
@[expose] noncomputable def homology
    {X₂ X₁ X₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) : CompHausAddCommGrp.{u} :=
  quotientRange (boundaryToKernel d₂ d₁ hd)

/-- A commuting map of continuous three-term complexes induces a continuous
map on compact Hausdorff homology. -/
@[expose] noncomputable def homologyMap
    {X₂ X₁ X₀ Y₂ Y₁ Y₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (e₂ : Y₂ ⟶ Y₁) (e₁ : Y₁ ⟶ Y₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) (he : ∀ x, e₁ (e₂ x) = 0)
    (p₂ : X₂ ⟶ Y₂) (p₁ : X₁ ⟶ Y₁) (p₀ : X₀ ⟶ Y₀)
    (h₁ : ∀ x, e₁ (p₁ x) = p₀ (d₁ x))
    (h₂ : ∀ x, e₂ (p₂ x) = p₁ (d₂ x)) :
    homology d₂ d₁ hd ⟶ homology e₂ e₁ he := by
  let q : kernelGroup d₁ ⟶ kernelGroup e₁ :=
    kernelMap p₁ p₀ d₁ e₁ h₁
  exact quotientRangeMap p₂ q
    (boundaryToKernel d₂ d₁ hd) (boundaryToKernel e₂ e₁ he)
    (fun x ↦ by
      apply Subtype.ext
      change e₂ (p₂ x) = p₁ (d₂ x)
      exact h₂ x)

@[simp]
lemma homologyMap_mk
    {X₂ X₁ X₀ Y₂ Y₁ Y₀ : CompHausAddCommGrp.{u}}
    (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀)
    (e₂ : Y₂ ⟶ Y₁) (e₁ : Y₁ ⟶ Y₀)
    (hd : ∀ x, d₁ (d₂ x) = 0) (he : ∀ x, e₁ (e₂ x) = 0)
    (p₂ : X₂ ⟶ Y₂) (p₁ : X₁ ⟶ Y₁) (p₀ : X₀ ⟶ Y₀)
    (h₁ : ∀ x, e₁ (p₁ x) = p₀ (d₁ x))
    (h₂ : ∀ x, e₂ (p₂ x) = p₁ (d₂ x))
    (x : kernelGroup d₁) :
    homologyMap d₂ d₁ e₂ e₁ hd he p₂ p₁ p₀ h₁ h₂
        (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (kernelMap p₁ p₀ d₁ e₁ h₁ x) :=
  rfl

end CompHausAddCommGrp
