/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Anchor
-/
module

public import CoherentModules.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Universally coherent rings

This file defines a commutative ring to be universally coherent when all of its finitely
presented commutative algebras are coherent. The target-algebra universe is a parameter of the
class: `IsUniversallyCoherent.{u, v} R` makes the assertion for algebras in `Type v`. This avoids
silently restricting the assertion to the universe containing `R`.

## Main declarations

* `IsUniversallyCoherent`: every finitely presented commutative algebra is coherent.
* `IsUniversallyCoherent.isCoherentRing_of_algEquiv`: transport along an algebra equivalence.
* `IsUniversallyCoherent.of_isNoetherian`: Noetherian commutative rings are universally coherent.
-/

@[expose] public section

universe u v w

/-- A commutative ring is universally coherent (for target algebras in `Type v`) if every
finitely presented commutative algebra in that universe is a coherent ring.

The target-algebra universe is deliberately independent of the universe containing the base
ring. Use `IsUniversallyCoherent.{u, v} R` when that universe is not inferred from an algebra. -/
class IsUniversallyCoherent (R : Type u) [CommRing R] : Prop where
  isCoherentRing (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] : IsCoherentRing A

namespace IsUniversallyCoherent

/-- A universally coherent commutative ring is coherent as a ring. -/
instance toIsCoherentRing (R : Type u) [CommRing R] [IsUniversallyCoherent.{u, u} R] :
    IsCoherentRing R :=
  IsUniversallyCoherent.isCoherentRing R R

/-- Universal coherence gives coherence after replacing a finitely presented algebra by an
equivalent algebra, including when the two carrier types live in different universes. -/
theorem isCoherentRing_of_algEquiv (R : Type u) {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.FinitePresentation R A] [IsUniversallyCoherent.{u, w} R]
    (e : A ≃ₐ[R] B) : IsCoherentRing B := by
  let _ : Algebra.FinitePresentation R B := Algebra.FinitePresentation.equiv e
  exact IsUniversallyCoherent.isCoherentRing R B

/-- Every Noetherian commutative ring is universally coherent. -/
instance (priority := 100) of_isNoetherian (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsUniversallyCoherent.{u, v} R where
  isCoherentRing A := by
    intros
    let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
    exact IsCoherentRing.of_isNoetherian A

end IsUniversallyCoherent
