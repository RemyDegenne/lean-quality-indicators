/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RingTheory.KrullDimension.GoingDown
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Stalk dimension bounds for flat morphisms

At a point where the stalk map of a scheme morphism is flat, the dimension of the target
stalk is at most the dimension of the source stalk. A flat morphism satisfies this condition
at every point.

## Main results

- `AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_le_of_flat_stalkMap` takes flatness of
  the stalk map at a single point.
- `AlgebraicGeometry.Flat.ringKrullDim_stalk_le` applies to every point of a flat morphism.

Both inequalities concern the full stalk rings, not fibers, residue fields, or selected
irreducible components. Dimensions take values in `WithBot ℕ∞`; no quasi-finiteness,
Noetherian, finite-type, or finite-dimensional hypothesis is imposed.

## References

- `SchemeProperties.RingTheory.KrullDimension.GoingDown`: dimension bounds for flat local
  ring maps.
- Mathlib, `AlgebraicGeometry.Scheme.Hom.stalkMap`: the canonical local map on stalks.
- Mathlib, `AlgebraicGeometry.Flat.stalkMap` and
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`: stalkwise flatness of scheme morphisms.
- Mathlib, `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`: the full stalk dimension
  convention.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If the canonical local map on stalks is flat at `x`, the full dimension of the target
stalk is at most the full dimension of the source stalk. This is the stalkwise form of
`RingHom.Flat.ringKrullDim_le`, using Mathlib's `Scheme.Hom.stalkMap`. -/
theorem Scheme.Hom.ringKrullDim_stalk_le_of_flat_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hx : (f.stalkMap x).hom.Flat) :
    ringKrullDim (Y.presheaf.stalk (f x)) ≤
      ringKrullDim (X.presheaf.stalk x) := by
  exact hx.ringKrullDim_le

/-- A flat scheme morphism bounds the full dimension of its target stalk at `f x` by
that of its source stalk at `x`. Mathlib's `Flat.stalkMap` supplies flatness of the
canonical local stalk map. -/
theorem Flat.ringKrullDim_stalk_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    ringKrullDim (Y.presheaf.stalk (f x)) ≤
      ringKrullDim (X.presheaf.stalk x) := by
  exact f.ringKrullDim_stalk_le_of_flat_stalkMap x (Flat.stalkMap f x)

end AlgebraicGeometry
