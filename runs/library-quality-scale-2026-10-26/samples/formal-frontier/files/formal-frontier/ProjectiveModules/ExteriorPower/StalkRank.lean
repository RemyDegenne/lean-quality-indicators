/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Localization
import ProjectiveModules.ExteriorPower.BaseChange

/-!
# Exterior powers above all stalk ranks

An exterior power of a finite flat module vanishes when its degree is strictly
larger than the rank at every prime. The scalar ring and module have independent
universes; the result includes the zero ring and degree zero.

The proof localizes at maximal ideals, where a finite flat module is free.
Scalar extension identifies the localized exterior power with the exterior
power of the localized module. A finite basis then gives vanishing above its
cardinality. No global projectivity or finite presentation is required.

## References

- [The Stacks Project, Tag 00NZ](https://stacks.math.columbia.edu/tag/00NZ),
  finite flat modules over local rings are free, as formalized in Mathlib by
  `Module.free_of_flat_of_isLocalRing`.
- Mathlib's `exteriorPower.subsingleton_of_span_eq_top_of_card_lt` and
  `Module.subsingleton_of_localization_maximal` supply finite-span vanishing
  and localization detection. The scalar-extension construction uses
  `ExteriorAlgebra.equivBaseChange` and its homogeneous-submodule compatibility.
-/

@[expose] public section

universe uR uM

open scoped TensorProduct

namespace exteriorPower

variable {R : Type uR} [CommRing R]
variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The `k`th exterior power of a finite flat module is subsingleton if every
stalk has rank strictly less than `k`. There is no nontrivial-ring assumption,
and the degree may be zero. The proof uses finite-flat freeness over local
rings (Stacks Project, Tag 00NZ, as formalized in Mathlib) and vanishing above
the cardinality of a finite spanning family. -/
theorem subsingleton_of_rankAtStalk_lt
    [Module.Finite R M] [Module.Flat R M] (k : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) M p < k) :
    Subsingleton (⋀[R]^k M) := by
  classical
  apply Module.subsingleton_of_localization_maximal (R := R)
    (fun p ↦ LocalizedModule p.primeCompl (⋀[R]^k M))
    (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl (⋀[R]^k M))
  intro p hp
  let A := Localization.AtPrime p
  haveI : Module.Flat R A := IsLocalization.flat A p.primeCompl
  haveI : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  let e := (ExteriorAlgebra.equivBaseChange (R := R) (S := A) (M := M)).toLinearEquiv
  -- The image equality first identifies the two homogeneous submodules.
  let ep : (⋀[A]^k (A ⊗[R] M)) ≃ₗ[A] (⋀[R]^k M).baseChange A :=
    (Submodule.equivMapOfInjective e.toLinearMap e.injective _).trans
      (LinearEquiv.ofEq _ _
        (ExteriorAlgebra.equivBaseChange_map_exteriorPower (R := R) (S := A) (M := M) k))
  -- Flatness turns the tensor-to-image map into a carrier equivalence.
  let eE : (A ⊗[R] (⋀[R]^k M)) ≃ₗ[A] (⋀[A]^k (A ⊗[R] M)) :=
    (Submodule.toBaseChange.toLinearEquiv A (⋀[R]^k M)).trans ep.symm
  have hr : Module.finrank A (A ⊗[R] M) < k := by
    rw [← (LocalizedModule.equivTensorProduct p.primeCompl M).finrank_eq]
    exact h ⟨p, hp.isPrime⟩
  let b := Module.Free.chooseBasis A (A ⊗[R] M)
  haveI : Subsingleton (⋀[A]^k (A ⊗[R] M)) :=
    subsingleton_of_span_eq_top_of_card_lt b b.span_eq k (by
      rw [← Module.finrank_eq_nat_card_basis b]
      exact hr)
  exact ((LocalizedModule.equivTensorProduct p.primeCompl (⋀[R]^k M)).trans eE).injective.subsingleton

end exteriorPower
