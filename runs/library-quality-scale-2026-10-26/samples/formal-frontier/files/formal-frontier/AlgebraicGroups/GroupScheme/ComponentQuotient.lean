/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupScheme.ComponentSchemeMap
public import AlgebraicGroups.GroupScheme.QuotientSheaf

/-!
# The fppf quotient by the identity component

For a quasi-compact group scheme locally of finite type over an algebraically
closed field, with the explicit connectedness hypotheses needed to construct
its component morphism, this file identifies the relative fppf quotient by the
identity component with the sheaf represented by the finite constant rational
component group.

## References

- J. S. Milne, *Algebraic Groups*, Proposition 2.37(b), for the exact
  identity-component sequence; Definition 5.20 and Propositions 5.24–5.25
  for quotient and relation-square conventions. The group-valued fppf
  quotient here is by the scheme-theoretic identity component, not by its
  reduction, and does not establish Theorem B.37.
- The local `GroupScheme.QuotientSheaf` supplies the relative group-valued
  fppf quotient and its representation from an fppf morphism with kernel;
  `GroupScheme.ComponentSchemeMap` supplies that morphism, its fpqc
  properties and its scheme-theoretic kernel. The mathlib community,
  *Mathlib*, supplies the relative sites and sheafification machinery in
  `AlgebraicGeometry.Sites.Fpqc` and
  `CategoryTheory.Sites.PreservesSheafification`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K] {G : Scheme.{u}}
variable (f : G ⟶ Spec (.of K)) [GrpObj (Over.mk f)] [LocallyConnectedSpace G]

local instance : LocallyConnectedSpace (Over.mk f).left :=
  inferInstanceAs (LocallyConnectedSpace G)

variable [ConnectedSpace ((Scheme.identityComponentOver (Over.mk f) ⊗
  Scheme.identityComponentOver (Over.mk f)).left)]
variable [GeometricallyConnected (Scheme.identityComponentOver (Over.mk f)).hom]
variable [LocallyOfFiniteType f] [QuasiCompact f]

noncomputable local instance : Fintype (rationalComponentGroup f) :=
  Fintype.ofFinite _

/-- The relative fppf quotient of a group scheme by its identity component is
represented by the finite constant group scheme on its rational component
group. This is the algebraically closed-field discrete quotient in Milne,
*Algebraic Groups*, Proposition 2.37(b), with the quotient conventions of
Definition 5.20 and Proposition 5.24. It does not construct the different
quotient by the reduced identity component. -/
noncomputable def identityComponentRelativeFppfQuotientIso :
    IsMonHom.Normal.relativeFppfQuotient
        (Scheme.identityComponentι (Over.mk f)) ≅
      Scheme.relativeFppfYoneda
        (finiteConstantGroupScheme K (rationalComponentGroup f)).X :=
  IsMonHom.Normal.relativeFppfQuotientIso
    (componentSchemeMap f)
    (isPullback_identityComponentι_componentSchemeMap f)

end AlgebraicGeometry
