/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.Algebra.Algebra.Tower

/-!
# Associated primes under restriction of scalars

The colon ideal of an arbitrary submodule and set contracts along a compatible
algebra map, without a surjectivity assumption. Consequently associated primes
contract under scalar restriction. The converse for surjective algebra maps
compares associated primes of the same module over the two scalar rings.

## References

* Mathlib's colon, ideal-comap, and associated-prime APIs.
-/

@[expose] public section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v} {M : Type w}
  [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Restricting scalars contracts the colon ideal of any submodule and set
along the algebra map. In particular, taking the bottom submodule and the
whole set recovers `Module.comap_annihilator`. -/
theorem colon_restrictScalars (N : Submodule S M) (T : Set M) :
    (N.restrictScalars R).colon T = (N.colon T).comap (algebraMap R S) := by
  ext scalar
  simp only [mem_colon, Ideal.mem_comap, restrictScalars_mem, algebraMap_smul]

end Submodule

namespace IsAssociatedPrime

variable {R : Type u} {S : Type v} {M : Type w}
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- An associated prime over the larger scalar ring contracts to an associated
prime over the smaller scalar ring, even if the algebra map is not surjective. -/
theorem comap_algebraMap {J : Ideal S} (hJ : IsAssociatedPrime J M) :
    IsAssociatedPrime (J.comap (algebraMap R S)) M := by
  obtain ⟨witness, hWitness⟩ := hJ.2
  have hPrime : (J.comap (algebraMap R S)).IsPrime :=
    Ideal.IsPrime.comap (f := algebraMap R S) (hK := hJ.isPrime)
  refine ⟨hPrime, ⟨witness, ?_⟩⟩
  calc
    J.comap (algebraMap R S) =
        (((⊥ : Submodule S M).colon {witness}).radical).comap (algebraMap R S) := by
          rw [hWitness]
    _ = (((⊥ : Submodule S M).colon {witness}).comap (algebraMap R S)).radical :=
      Ideal.comap_radical (algebraMap R S) _
    _ = ((⊥ : Submodule R M).colon {witness}).radical := by
      rw [← Submodule.colon_restrictScalars (R := R), Submodule.restrictScalars_bot]

/-- For a surjective algebra map, a prime ideal is associated to a module
over the target precisely when its contraction is associated over the source. -/
theorem comap_algebraMap_iff (J : Ideal S)
    (hSurj : Function.Surjective (algebraMap R S)) :
    IsAssociatedPrime (J.comap (algebraMap R S)) M ↔ IsAssociatedPrime J M := by
  constructor
  · intro hAssociated
    have hPrime : J.IsPrime := by
      refine ⟨?_, ?_⟩
      · intro hTop
        apply hAssociated.isPrime.ne_top
        simp only [hTop, Ideal.comap_top]
      · intro left right hProduct
        obtain ⟨sourceLeft, rfl⟩ := hSurj left
        obtain ⟨sourceRight, rfl⟩ := hSurj right
        have hSourceProduct : sourceLeft * sourceRight ∈
            J.comap (algebraMap R S) := by
          change algebraMap R S (sourceLeft * sourceRight) ∈ J
          simpa only [map_mul] using hProduct
        exact hAssociated.isPrime.mem_or_mem hSourceProduct
    obtain ⟨witness, hWitness⟩ := hAssociated.2
    refine ⟨hPrime, witness, ?_⟩
    apply Ideal.comap_injective_of_surjective (algebraMap R S) hSurj
    calc
      J.comap (algebraMap R S) =
          ((⊥ : Submodule R M).colon {witness}).radical := hWitness
      _ = (((⊥ : Submodule S M).colon {witness}).radical).comap
          (algebraMap R S) := by
            rw [Ideal.comap_radical, ← Submodule.colon_restrictScalars,
              Submodule.restrictScalars_bot]
  · exact comap_algebraMap

end IsAssociatedPrime
