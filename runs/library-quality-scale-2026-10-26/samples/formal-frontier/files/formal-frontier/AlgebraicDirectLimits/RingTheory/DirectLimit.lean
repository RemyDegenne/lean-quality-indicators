/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Order.DirectedSystem
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Constant ring-homomorphism systems

A constant family with identity ring homomorphisms satisfies `DirectedSystem`
over any preorder. The index and carrier universes are independent, and the
semiring need not be associative or commutative. The identity and composition
laws are available through `DirectedSystem.map_self` and `DirectedSystem.map_map`.
Directedness and nonemptiness are separate hypotheses of the colimit construction.

The law witness specializes `DirectedSystem.const` using `RingHom.coe_id`.
The constant integer colimit in this library's Krull-dimension examples uses
this instance with Mathlib's characteristic maps and universal ring lift.

## References

The construction reuses Junyan Xu's `DirectedSystem` and concrete `DirectLimit`
APIs in Mathlib, and Amelia Livingston and Jireh Loreaux's `RingHom` identity API.
The constant-integer colimit model is Keel's development in this library.
-/

@[expose] public section

universe u v

namespace DirectedSystem

/-- A constant family with identity ring homomorphisms is a directed system
over any preorder. -/
instance constRingHom {ι : Type u} [Preorder ι] (A : Type v) [NonAssocSemiring A] :
    DirectedSystem (fun _ : ι => A) (fun _ _ _ => (RingHom.id A : A → A)) := by
  simpa only [RingHom.coe_id] using (DirectedSystem.const (ι := ι) A)

end DirectedSystem
