/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.ArbitraryLocalProjectiveFree
public import Mathlib.RingTheory.LocalRing.Basic

import StableRange.Local

/-!
# Projective modules over local rings

Kaplansky's projective-module theorem in terms of Mathlib's `IsLocalRing`,
`Module.Projective` and `Module.Free` classes. The scalar ring need not be
commutative, and the module need not be finitely or countably generated.
The scalar and module universes are independent.

Mathlib modules use left scalar actions. A right module over `R` is a module
over `Rᵐᵒᵖ`; applying `Module.Projective.free_of_isLocalRing` to that scalar
ring gives right-module freeness, using the existing opposite local-ring
instance. No second scalar action or commuting-action hypothesis is needed.

## Implementation notes

The proper-two-sided-ideal formulation is
`Module.Projective.free_of_isUnit_compl_arbitraryRank`, from the existing
local-freeness formalization in
`ProjectiveModules.Module.ArbitraryLocalProjectiveFree`. It is the arbitrary-rank
right-module result. The canonical Jacobson radical of `Rᵐᵒᵖ` is proper by
`Ring.jacobson_lt_top`; its complement consists of units by
`IsLocalRing.mem_ringJacobson_iff` in `StableRange.Local`. Semilinear transport
along `RingEquiv.opOp` relates the right-module result over `Rᵐᵒᵖ` to the
left-module interface here. The finite residue-coordinate result remains
`Module.Projective.exists_rightFreeLinearEquiv_of_isUnit_compl`:
its coordinate size is the dimension over the residue division ring, not a
claim about `Module.finrank` over arbitrary local scalars.

## References

* I. Kaplansky, *Projective modules*, Annals of Mathematics **68** (1958),
  372–377.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  author-hosted complete-book build dated 2013-08-29, Remark I.2.2.1.
* Mathlib's projective-module, free-module and local-ring APIs, and the
  arbitrary-rank right-module local-freeness formalization in
  `ProjectiveModules.Module.ArbitraryLocalProjectiveFree`.
* `StableRange.Local`, for the characterization of the canonical Jacobson
  radical of a possibly noncommutative local ring as its nonunits.
-/

@[expose] public section

universe uR uP

namespace Module.Projective

/-- Every projective module over a possibly noncommutative local ring is free,
with no bound on its rank or number of generators.

This is Kaplansky's projective-module theorem (*Projective modules*, 1958),
also cited in Weibel's *The K-book*, Remark I.2.2.1. For right modules over
`R`, use the same theorem with scalar ring `Rᵐᵒᵖ`. -/
theorem free_of_isLocalRing
    {R : Type uR} [Ring R] [IsLocalRing R]
    {P : Type uP} [AddCommGroup P] [Module R P] [Module.Projective R P] :
    Module.Free R P := by
  classical
  let eR : R ≃+* Rᵐᵒᵖᵐᵒᵖ := RingEquiv.opOp R
  let _ : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eR
  let _ : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eR
  -- Regard the given left action as a right action of the opposite ring.
  let _ : Module Rᵐᵒᵖᵐᵒᵖ P := Module.compHom P eR.symm.toRingHom
  let e : P ≃ₛₗ[eR.symm.toRingHom] P :=
    { AddEquiv.refl P with map_smul' := fun _ _ ↦ rfl }
  let _ : Module.Projective Rᵐᵒᵖᵐᵒᵖ P := Module.Projective.of_equiv e.symm
  have hI : (Ring.jacobson Rᵐᵒᵖ).toTwoSided ≠ ⊤ := by
    intro h
    apply (Ring.jacobson_lt_top Rᵐᵒᵖ).ne
    simpa only [Ideal.asIdeal_toTwoSided, TwoSidedIdeal.top_asIdeal] using
      congrArg (fun I : TwoSidedIdeal Rᵐᵒᵖ ↦ I.asIdeal) h
  have hunit (r : Rᵐᵒᵖ) (hr : r ∉ (Ring.jacobson Rᵐᵒᵖ).toTwoSided) :
      IsUnit r := by
    by_contra h
    exact hr (Ideal.mem_toTwoSided.mpr ((IsLocalRing.mem_ringJacobson_iff r).mpr h))
  let _ : Module.Free Rᵐᵒᵖᵐᵒᵖ P :=
    free_of_isUnit_compl_arbitraryRank (R := Rᵐᵒᵖ)
      (Ring.jacobson Rᵐᵒᵖ).toTwoSided hI hunit
  exact Module.Free.of_equiv e

end Module.Projective
