/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.GroupExtensionUlift

/-!
# Continuous group extensions

This file packages an abstract group extension together with mathlib's strong
topological short-exactness predicate.  Thus the inclusion is a closed
embedding and the projection is an open quotient map; merely asking that both
homomorphisms be continuous would lose essential quotient-topology data.

The groups may live in independent universes.  `ContinuousGroupExtension.ulift`
raises them independently, while `commonUniverseUlift` makes the canonical
choice that puts all three carriers in their common maximum universe.  The
pointwise formulas are exposed for later mixed-universe constructions.
-/

set_option warningAsError true

@[expose] public section

universe uN uE uQ uN' uE' uQ'

/-- A group extension whose inclusion and projection form a short exact
sequence of topological groups in the strong sense of
`TopologicalGroup.IsSES`. -/
structure ContinuousGroupExtension (N : Type uN) (E : Type uE) (Q : Type uQ)
    [Group N] [Group E] [Group Q]
    [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
    [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]
    extends GroupExtension N E Q where
  /-- The inclusion is a closed embedding, the projection is an open quotient
  map, and their underlying homomorphisms are exact. -/
  isSES : TopologicalGroup.IsSES toGroupExtension.inl toGroupExtension.rightHom

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- Construct a continuous group extension from an abstract extension and the
strong topological short-exactness witness. -/
def mk' (S : GroupExtension N E Q)
    (hS : TopologicalGroup.IsSES S.inl S.rightHom) :
    ContinuousGroupExtension N E Q where
  toGroupExtension := S
  isSES := hS

@[simp]
theorem mk'_toGroupExtension (S : GroupExtension N E Q)
    (hS : TopologicalGroup.IsSES S.inl S.rightHom) :
    (mk' S hS).toGroupExtension = S := rfl

/-- The inclusion, bundled as a continuous homomorphism. -/
def inlContinuous (S : ContinuousGroupExtension N E Q) : N →ₜ* E where
  toMonoidHom := S.inl
  continuous_toFun := S.isSES.isClosedEmbedding.continuous

@[simp]
theorem inlContinuous_apply (S : ContinuousGroupExtension N E Q) (n : N) :
    S.inlContinuous n = S.inl n := rfl

/-- The projection, bundled as a continuous homomorphism. -/
def rightHomContinuous (S : ContinuousGroupExtension N E Q) : E →ₜ* Q where
  toMonoidHom := S.rightHom
  continuous_toFun := S.isSES.isOpenQuotientMap.continuous

@[simp]
theorem rightHomContinuous_apply (S : ContinuousGroupExtension N E Q) (e : E) :
    S.rightHomContinuous e = S.rightHom e := rfl

/-- Raise the kernel, middle group, and quotient of a continuous extension
through independently chosen universes. -/
def ulift (S : ContinuousGroupExtension N E Q) :
    ContinuousGroupExtension
      (ULift.{uN'} N) (ULift.{uE'} E) (ULift.{uQ'} Q) where
  toGroupExtension := S.toGroupExtension.ulift
  isSES := S.toGroupExtension.isSES_ulift S.isSES

@[simp]
theorem ulift_toGroupExtension (S : ContinuousGroupExtension N E Q) :
    (S.ulift.{uN, uE, uQ, uN', uE', uQ'}).toGroupExtension =
      S.toGroupExtension.ulift := rfl

@[simp]
theorem ulift_inl_apply (S : ContinuousGroupExtension N E Q)
    (n : ULift.{uN'} N) :
    S.ulift.inl n = ULift.up (S.inl n.down) := rfl

@[simp]
theorem ulift_rightHom_apply (S : ContinuousGroupExtension N E Q)
    (e : ULift.{uE'} E) :
    S.ulift.rightHom e = ULift.up (S.rightHom e.down) := rfl

@[simp]
theorem ulift_inlContinuous_apply (S : ContinuousGroupExtension N E Q)
    (n : ULift.{uN'} N) :
    S.ulift.inlContinuous n = ULift.up (S.inl n.down) := rfl

@[simp]
theorem ulift_rightHomContinuous_apply (S : ContinuousGroupExtension N E Q)
    (e : ULift.{uE'} E) :
    S.ulift.rightHomContinuous e = ULift.up (S.rightHom e.down) := rfl

/-- The canonical common-universe lift of an independently universe-polymorphic
continuous extension. -/
def commonUniverseUlift (S : ContinuousGroupExtension N E Q) :
    ContinuousGroupExtension
      (ULift.{max uE uQ} N)
      (ULift.{max uN uQ} E)
      (ULift.{max uN uE} Q) :=
  S.ulift

@[simp]
theorem commonUniverseUlift_toGroupExtension
    (S : ContinuousGroupExtension N E Q) :
    S.commonUniverseUlift.toGroupExtension =
      S.toGroupExtension.ulift := rfl

@[simp]
theorem commonUniverseUlift_inl_apply (S : ContinuousGroupExtension N E Q)
    (n : ULift.{max uE uQ} N) :
    S.commonUniverseUlift.inl n = ULift.up (S.inl n.down) := rfl

@[simp]
theorem commonUniverseUlift_rightHom_apply (S : ContinuousGroupExtension N E Q)
    (e : ULift.{max uN uQ} E) :
    S.commonUniverseUlift.rightHom e = ULift.up (S.rightHom e.down) := rfl

/-- An equivalence of continuous extensions with fixed kernel and quotient.
The equivalence of middle groups is required to be a homeomorphism. -/
structure Equiv (S : ContinuousGroupExtension N E Q)
    {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E']
    (S' : ContinuousGroupExtension N E' Q) extends E ≃ₜ* E' where
  /-- Compatibility with the kernel inclusions. -/
  inl_comm : toContinuousMulEquiv ∘ S.inl = S'.inl
  /-- Compatibility with the quotient projections. -/
  rightHom_comm : S'.rightHom ∘ toContinuousMulEquiv = S.rightHom

namespace Equiv

variable {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E']
  {S : ContinuousGroupExtension N E Q}
  {S' : ContinuousGroupExtension N E' Q}

/-- Forget topology from an equivalence of continuous extensions. -/
def toGroupExtensionEquiv (equiv : S.Equiv S') :
    S.toGroupExtension.Equiv S'.toGroupExtension where
  toMulEquiv := equiv.toContinuousMulEquiv.toMulEquiv
  inl_comm := equiv.inl_comm
  rightHom_comm := equiv.rightHom_comm

instance : EquivLike (S.Equiv S') E E' where
  coe equiv := equiv.toContinuousMulEquiv
  inv equiv := equiv.toContinuousMulEquiv.symm
  left_inv equiv := equiv.toContinuousMulEquiv.left_inv
  right_inv equiv := equiv.toContinuousMulEquiv.right_inv
  coe_injective' := fun equiv equiv' h _ => by
    cases equiv
    cases equiv'
    congr
    exact ContinuousMulEquiv.ext (congrFun h)

instance : MulEquivClass (S.Equiv S') E E' where
  map_mul equiv := equiv.toContinuousMulEquiv.map_mul

instance : HomeomorphClass (S.Equiv S') E E' where
  map_continuous equiv := equiv.toContinuousMulEquiv.continuous
  inv_continuous equiv := equiv.toContinuousMulEquiv.symm.continuous

@[simp]
theorem map_inl (equiv : S.Equiv S') (n : N) :
    equiv (S.inl n) = S'.inl n := by
  exact congrFun equiv.inl_comm n

@[simp]
theorem rightHom_map (equiv : S.Equiv S') (e : E) :
    S'.rightHom (equiv e) = S.rightHom e := by
  exact congrFun equiv.rightHom_comm e

end Equiv

end ContinuousGroupExtension
