/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Geometric irreducibility implies geometric connectedness

Every geometrically irreducible morphism of schemes is geometrically connected. The proof
uses Mathlib's geometric pullback predicates and `IrreducibleSpace.connectedSpace` on each
field-valued pullback. The schemes share the universe required by Mathlib's geometric API.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Every geometrically irreducible morphism of schemes is geometrically connected. -/
instance (priority := 100) GeometricallyIrreducible.geometricallyConnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] :
    GeometricallyConnected f := by
  constructor
  intro K _ y Z fst snd h
  have : IrreducibleSpace Z :=
    GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h
  infer_instance

end AlgebraicGeometry
