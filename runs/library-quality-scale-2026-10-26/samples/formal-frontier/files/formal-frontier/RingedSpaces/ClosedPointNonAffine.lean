/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.ClosedPointHom

/-!
# Non-affineness of constant-closed ringed morphisms

A ring homomorphism from a local ring that sends an element of its maximal ideal to a
unit induces a constant-closed ringed-space morphism that cannot arise from any
ring homomorphism between the corresponding affine spectra.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), Exercise 7.2.G (p. 206), in the context of Definition 7.2.1 (p. 204)
  and Exercise 7.2.F (pp. 205–206): motivation for a nonlocal full ringed-space
  morphism not induced by an affine map. The arbitrary-`beta`, nontrivial-target
  non-affineness theorem is a project generalization, not a printed proof or a
  statement about locally ringed or scheme morphisms.
-/

set_option warningAsError true

@[expose] public section

namespace AlgebraicGeometry.RingedSpace.ClosedPointHom

open CategoryTheory Opposite TopologicalSpace TopCat

universe u

/-- A nonlocal map to a nonzero ring yields a constant-closed ringed morphism
different from every affine-induced morphism, regardless of the inducing map.
Vakil's *The Rising Sea* (21 October 2025 draft), Exercise 7.2.G (p. 206),
motivates the contrast; the arbitrary inducing map and nontrivial target here
are project generalizations, not a locally ringed or scheme-map theorem. -/
theorem hom_ne_sheafedSpaceMap_of_isUnit
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (alpha : R →+* S) (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hu : IsUnit (alpha r)) (beta : R →+* S) :
    hom R (Spec.sheafedSpaceObj (CommRingCat.of S))
        (CommRingCat.ofHom alpha ≫
          (StructureSheaf.globalSectionsIso (CommRingCat.of S)).hom).hom ≠
      Spec.sheafedSpaceMap (CommRingCat.ofHom beta) := by
  intro heq
  let X := Spec.sheafedSpaceObj (CommRingCat.of S)
  let globalIso := StructureSheaf.globalSectionsIso (CommRingCat.of S)
  have hAffine : globalSectionsMap R X (Spec.sheafedSpaceMap (CommRingCat.ofHom beta)) =
      CommRingCat.ofHom beta ≫ globalIso.hom := by
    convert (StructureSheaf.toOpen_comp_comap beta ⊤) using 1; rfl
  have hClosed : globalSectionsMap R X
      (hom R X (CommRingCat.ofHom alpha ≫ globalIso.hom).hom) =
      CommRingCat.ofHom alpha ≫ globalIso.hom := by
    exact (hom_globalSectionsMap R X
      (CommRingCat.ofHom alpha ≫ globalIso.hom).hom).trans
        (CommRingCat.ofHom_hom _)
  have hGlobal : CommRingCat.ofHom alpha ≫ globalIso.hom =
      CommRingCat.ofHom beta ≫ globalIso.hom :=
    hClosed.symm.trans ((congrArg (globalSectionsMap R X) heq).trans hAffine)
  have hRing : alpha = beta := by
    have hCat : CommRingCat.ofHom alpha = CommRingCat.ofHom beta :=
      (CategoryTheory.Iso.cancel_iso_hom_right _ _ globalIso).mp hGlobal
    apply RingHom.ext
    intro x
    exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of S => f.hom x) hCat
  let p : PrimeSpectrum S := Classical.choice (inferInstance : Nonempty (PrimeSpectrum S))
  have hBase : IsLocalRing.closedPoint R = PrimeSpectrum.comap alpha p := by
    have hEq := congrArg (fun f : X ⟶ Spec.sheafedSpaceObj (CommRingCat.of R) =>
      f.hom.base p) heq
    change IsLocalRing.closedPoint R = PrimeSpectrum.comap beta p at hEq
    rw [← hRing] at hEq
    exact hEq
  have hMem : alpha r ∈ p.asIdeal := by
    have hp : r ∈ (PrimeSpectrum.comap alpha p).asIdeal := by
      rw [← hBase]
      exact hr
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using hp
  exact (Ideal.notMem_of_isUnit p.asIdeal hu) hMem

/-- No affine-induced map equals the nonlocal constant-closed ringed morphism. -/
theorem not_exists_sheafedSpaceMap_of_isUnit
    {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (alpha : R →+* S) (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R)
    (hu : IsUnit (alpha r)) :
    ¬ ∃ beta : R →+* S,
      hom R (Spec.sheafedSpaceObj (CommRingCat.of S))
          (CommRingCat.ofHom alpha ≫
            (StructureSheaf.globalSectionsIso (CommRingCat.of S)).hom).hom =
        Spec.sheafedSpaceMap (CommRingCat.ofHom beta) := by
  rintro ⟨beta, hbeta⟩
  exact (hom_ne_sheafedSpaceMap_of_isUnit alpha r hr hu beta) hbeta

end AlgebraicGeometry.RingedSpace.ClosedPointHom
