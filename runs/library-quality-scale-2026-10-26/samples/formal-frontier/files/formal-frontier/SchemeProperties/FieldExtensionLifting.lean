/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Lifting field-valued points after field extension

A morphism of schemes is surjective precisely when every supplied field-valued point of its
target lifts after some extension of its field of definition. A field extension is expressed
as a morphism from `CommRingCat.of K` to a commutative ring `L` satisfying `IsField L`.
Thus the statements do not require a choice of field structure on the existential target.

## Main results

- `AlgebraicGeometry.Scheme.Hom.exists_lift_after_field_extension`: a supplied field-valued
  point lifts along a surjective morphism after extending its field.
- `AlgebraicGeometry.Scheme.Hom.surjective_of_lifts_after_field_extension`: lifting all
  field-valued points after field extension implies surjectivity.
- `AlgebraicGeometry.Scheme.Hom.surjective_iff_lifts_after_field_extension`: the resulting
  characterization of surjectivity.

## Limitations

There are no local finite type, quasi-compactness or algebraic closedness hypotheses.
The extension may be transcendental: `Spec K(t) ⟶ Spec K` illustrates why an algebraic
extension, or a lift over `K` itself, cannot generally be required. Lifting over the same
field requires additional hypotheses.

## References

The residue-field maps and base-change method are supplied by Mathlib:

- `Mathlib.AlgebraicGeometry.ResidueField`, for residue fields and their canonical maps.
- `Mathlib.AlgebraicGeometry.PullbackCarrier`, for surjectivity after base change.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, for recovering ring maps from morphisms
  between affine spectra.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every supplied field-valued point of the target of a surjective scheme morphism lifts
along that morphism after some field extension. The extension is not required to be algebraic. -/
theorem exists_lift_after_field_extension [Surjective f] {K : Type u} [Field K]
    (g : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ L : CommRingCat.{u}, IsField L ∧
      ∃ (ι : CommRingCat.of K ⟶ L) (q : Spec L ⟶ X),
        q ≫ f = Spec.map ι ≫ g := by
  classical
  obtain ⟨z, _⟩ :=
    (Limits.pullback.snd f g).surjective (default : Spec (CommRingCat.of K))
  let L := (Limits.pullback f g).residueField z
  let r : Spec L ⟶ Limits.pullback f g :=
    (Limits.pullback f g).fromSpecResidueField z
  refine ⟨L, Field.toIsField L, Spec.preimage (r ≫ Limits.pullback.snd f g),
    r ≫ Limits.pullback.fst f g, ?_⟩
  simp only [Spec.map_preimage, Category.assoc, Limits.pullback.condition]

/-- A scheme morphism is surjective if every field-valued point of its target lifts after
some extension of its field of definition. All fields and all supplied points are tested. -/
theorem surjective_of_lifts_after_field_extension
    (h : ∀ (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ Y),
      ∃ L : CommRingCat.{u}, IsField L ∧
        ∃ (ι : CommRingCat.of K ⟶ L) (q : Spec L ⟶ X),
          q ≫ f = Spec.map ι ≫ g) : Surjective f := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨L, hL, ι, q, hq⟩ := h (Y.residueField y) (Y.fromSpecResidueField y)
  let : Nontrivial L := hL.nontrivial
  obtain ⟨s⟩ := (inferInstance : Nonempty (Spec L))
  refine ⟨q s, ?_⟩
  calc
    f (q s) = Y.fromSpecResidueField y (Spec.map ι s) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun r : Spec L ⟶ Y ↦ r s) hq
    _ = y := Scheme.fromSpecResidueField_apply y (Spec.map ι s)

/-- Surjectivity of a scheme morphism is equivalent to lifting every field-valued point
of its target after some field extension, with no finiteness hypotheses on the morphism. -/
theorem surjective_iff_lifts_after_field_extension :
    Surjective f ↔
      ∀ (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ Y),
        ∃ L : CommRingCat.{u}, IsField L ∧
          ∃ (ι : CommRingCat.of K ⟶ L) (q : Spec L ⟶ X),
            q ≫ f = Spec.map ι ≫ g := by
  constructor
  · intro hf K _ g
    let : Surjective f := hf
    exact f.exists_lift_after_field_extension g
  · exact f.surjective_of_lifts_after_field_extension

end AlgebraicGeometry.Scheme.Hom
