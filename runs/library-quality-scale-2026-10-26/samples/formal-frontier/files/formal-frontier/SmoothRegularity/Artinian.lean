/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity of Artinian rings

For a commutative Artinian local ring, regularity is equivalent to being a field.
For a commutative Artinian ring, regularity is equivalent to reducedness. The
global criterion includes the zero ring; it does not assert that a regular
Artinian ring is a field.

The statements use Mathlib's `IsRegularLocalRing`, `IsRegularRing`, `IsField`,
`IsReduced` and `IsArtinianRing`. Artinianity supplies Noetherianity, so neither
criterion requires a separate Noetherian hypothesis. Mathlib's `IsLocalRing`
includes nontriviality, which excludes the zero ring from the local criterion
but not from the global one.

## Proofs

The local criterion uses the vanishing of the Krull dimension and the
span finrank of the maximal ideal. The global criterion applies the local
criterion to localizations and uses the locality of reducedness. Neither
argument requires a domain hypothesis or a smoothness theorem.

## References

The regularity definitions and cotangent-space criterion are from Mathlib's
`Mathlib.RingTheory.RegularLocalRing.Defs`. The Artinian theory, including
`IsArtinianRing.isField_of_isReduced_of_isLocalRing` and the finite product of
fields equivalence `IsArtinianRing.equivPi`, is from Mathlib's
`Mathlib.RingTheory.Artinian.Ring` and `Mathlib.RingTheory.Artinian.Module`.
Mathlib's `Mathlib.RingTheory.HopkinsLevitzki` supplies Artinian-to-Noetherian
instances and the dimension-zero characterization. The localization and descent
of reducedness are from `Mathlib.RingTheory.LocalProperties.Reduced`.
These imported results are reused, not redefined here.
-/

@[expose] public section

universe u

namespace IsArtinianRing

/-- A commutative Artinian local ring is regular if and only if it is a field.
The field condition is the proposition `IsField R`, not a choice of inverses. -/
theorem isRegularLocalRing_iff_isField (R : Type u) [CommRing R]
    [IsArtinianRing R] [IsLocalRing R] : IsRegularLocalRing R ↔ IsField R := by
  have hdim : ringKrullDim R = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
      (isArtinianRing_iff_krullDimLE_zero.mp inferInstance)
  rw [isRegularLocalRing_iff, hdim, Nat.cast_eq_zero,
    Submodule.spanFinrank_eq_zero_iff_eq_bot
      (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal R)),
    ← IsLocalRing.isField_iff_maximalIdeal_eq]

/-- A commutative Artinian ring is regular if and only if it is reduced.
This includes subsingleton rings and does not require the ring to be local. -/
theorem isRegularRing_iff_isReduced (R : Type u) [CommRing R]
    [IsArtinianRing R] : IsRegularRing R ↔ IsReduced R := by
  constructor
  · intro h
    letI : IsRegularRing R := h
    apply isReduced_ofLocalizationMaximal R
    intro m hm
    letI : m.IsMaximal := hm
    have hfield : IsField (Localization.AtPrime m) :=
      (isRegularLocalRing_iff_isField (Localization.AtPrime m)).mp inferInstance
    letI := hfield.toField
    infer_instance
  · intro h
    letI : IsReduced R := h
    rw [isRegularRing_iff]
    intro p hp
    exact (isRegularLocalRing_iff_isField (Localization.AtPrime p)).mpr
      (isField_of_isReduced_of_isLocalRing (Localization.AtPrime p))

end IsArtinianRing
