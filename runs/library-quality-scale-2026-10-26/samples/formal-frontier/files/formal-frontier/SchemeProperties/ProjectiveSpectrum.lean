/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Reducedness and integrality of projective spectra

For an `ℕ`-graded commutative ring `A`, the scheme `Proj 𝒜` is reduced if `A` is
reduced, and its underlying space is preirreducible if `A` is a domain. A nonempty
projective spectrum of a domain is integral. No finite generation or generation
in degree one is assumed.

Nonemptiness is essential for integrality: a domain with its grading concentrated
in degree zero has empty projective spectrum. Reducedness and preirreducibility
do not require nonemptiness.

## References

* Mathlib's projective spectra and standard affine cover, developed by Jujian Zhang,
  Johan Commelin and Andrew Yang: `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`.
* Mathlib's homogeneous localizations, developed by Jujian Zhang and Eric Wieser:
  `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.
* Mathlib's scheme reducedness and integrality criteria, developed by Andrew Yang:
  `Mathlib.AlgebraicGeometry.Properties`.
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective spectrum of a reduced graded commutative ring is reduced. -/
instance isReduced [_root_.IsReduced A] : AlgebraicGeometry.IsReduced (Proj 𝒜) := by
  letI (M : Submonoid A) : _root_.IsReduced (HomogeneousLocalization 𝒜 M) :=
    isReduced_of_injective
      (algebraMap (HomogeneousLocalization 𝒜 M) (Localization M))
      (HomogeneousLocalization.val_injective M)
  have h : ∀ i : (affineOpenCover 𝒜).openCover.I₀,
      AlgebraicGeometry.IsReduced ((affineOpenCover 𝒜).openCover.X i) := fun i =>
    inferInstanceAs
      (AlgebraicGeometry.IsReduced
        (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))))
  exact @AlgebraicGeometry.IsReduced.of_openCover (Proj 𝒜) (affineOpenCover 𝒜).openCover h

/-- The projective spectrum of a graded domain is preirreducible, including when
it is empty. -/
instance preirreducibleSpace [IsDomain A] : PreirreducibleSpace (Proj 𝒜) := by
  change PreirreducibleSpace (ProjectiveSpectrum 𝒜)
  refine PreirreducibleSpace.of_forall_nonempty_inter ?_
  rintro U V hU hV ⟨x, hx⟩ ⟨y, hy⟩
  -- A point of a nonempty open makes the zero homogeneous ideal relevant.
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by
        simpa only [HomogeneousIdeal.toIdeal_bot] using
          (Ideal.isPrime_bot : (⊥ : Ideal A).IsPrime)
      not_irrelevant_le := fun h => x.not_irrelevant_le (h.trans bot_le) }
  have hη : IsGenericPoint η Set.univ := by
    rw [isGenericPoint_def, Set.eq_univ_iff_forall]
    intro z
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η z).mp
      ((ProjectiveSpectrum.as_ideal_le_as_ideal 𝒜 η z).mp bot_le)
  exact ⟨η, (hη.mem_open_set_iff hU).2 ⟨x, Set.mem_univ x, hx⟩,
    (hη.mem_open_set_iff hV).2 ⟨y, Set.mem_univ y, hy⟩⟩

/-- A nonempty projective spectrum of a graded domain is integral. A grading
concentrated in degree zero shows why nonemptiness is a separate hypothesis. -/
theorem isIntegral [IsDomain A] [Nonempty (Proj 𝒜)] :
    AlgebraicGeometry.IsIntegral (Proj 𝒜) := by
  letI : IrreducibleSpace (Proj 𝒜) :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced (Proj 𝒜)

end AlgebraicGeometry.Proj
