/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Universal injectivity and algebraically closed field-valued points

For an arbitrary scheme morphism `f : X ⟶ Y`, universal injectivity is equivalent to
injectivity of postcomposition by `f` on `Spec K`-valued points for every algebraically
closed field `K`. The fields and schemes share an arbitrary universe, as in Mathlib's
all-field characterization. There are no finiteness, reducedness, separation or flatness
assumptions on `f`.

The statement uses Mathlib's existing `UniversallyInjective` and scheme spectrum, not a
new notion of geometric point. The distinction from injectivity of the underlying map
of topological spaces, and from being a monomorphism, is explained in the
[mathematical guide](../docs/UniversallyInjectiveGeometricPoints.md).

## Relationship with the all-field criterion

Mathlib's `AlgebraicGeometry.tfae_universallyInjective` gives the corresponding
criterion with all fields as tests. The equivalence below restricts that quantifier
to algebraically closed fields without changing the hypotheses on the morphism.
For any field `K`, precompose two `K`-valued points with the canonical map from the
spectrum of `AlgebraicClosure K`. This map is flat and surjective, hence an epimorphism.
Injectivity over the algebraic closure and epimorphism cancellation recover injectivity
over `K`.

## References

* Mathlib's `AlgebraicGeometry.tfae_universallyInjective`, by Andrew Yang and
  Justus Springer, formalizes the all-field criterion and its relationship with
  purely inseparable residue-field extensions (Stacks Project, Tag 01S4).
* Mathlib's `AlgebraicGeometry.Flat.epi_of_flat_of_surjective`, in the flat-morphism
  development by Christian Merten and Andrew Yang, supplies the epimorphism API for
  field extensions (Stacks Project, Tag 02VW).
* Mathlib's algebraic closure construction is due to Kenny Lau.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme morphism is universally injective if and only if it is injective on
`Spec K`-valued points for every algebraically closed field `K`.

This restricts the test fields in Mathlib's `tfae_universallyInjective` without imposing
any additional hypothesis on the morphism or its source and target. -/
theorem universallyInjective_iff_injective_geometricPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UniversallyInjective f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K],
        Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f) := by
  constructor
  · intro hf K _ _
    have hFields : ∀ (L : Type u) [Field L],
        Function.Injective (fun g : Spec (.of L) ⟶ X ↦ g ≫ f) :=
      ((tfae_universallyInjective f).out 1 2).mp hf
    exact hFields K
  · intro hf
    apply ((tfae_universallyInjective f).out 1 2).mpr
    intro K _ g₁ g₂ h
    let π : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    haveI : Flat π := inferInstance
    haveI : Surjective π := inferInstance
    haveI : Epi π := Flat.epi_of_flat_of_surjective π
    apply (cancel_epi π).mp
    apply hf (AlgebraicClosure K)
    simpa only [Category.assoc] using congrArg (fun g ↦ π ≫ g) h

end AlgebraicGeometry
