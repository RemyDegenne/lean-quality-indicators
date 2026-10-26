/-
SPDX-License-Identifier: Apache-2.0
Authors: Lintel
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Field-valued fibers of locally quasi-finite morphisms

A locally quasi-finite, quasi-compact morphism has finitely many lifts of every
field-valued point of its base, with values in the same field. The field need not
be algebraically closed, and the morphism need not be locally of finite type.

Conversely, a locally-of-finite-type morphism is locally quasi-finite if these
sets of lifts are finite for every algebraically closed field and every point of
the base valued in that field. This implication does not require quasi-compactness.
For locally-of-finite-type, quasi-compact morphisms, the two directions give an
equivalence.

Mathlib's `LocallyQuasiFinite` is a fiberwise condition; it does not itself require
local finite type or quasi-compactness. Local finite type is required only for the
converse here, while quasi-compactness is required only for the forward direction.
An infinite disjoint union of copies of a field spectrum illustrates why
quasi-compactness cannot simply be omitted from the forward statement.

## References

* Mathlib's `IsFinite.of_locallyQuasiFinite`, `Scheme.isoSpec`,
  `Spec.homEquivAlgHom` and `Finite.algHom` supply the finite-morphism and
  algebra-homomorphism approach to the forward implication.
* Mathlib's `pointEquivClosedPoint`, `LocallyOfFiniteType.jacobsonSpace`,
  `JacobsonSpace.discreteTopology`, `Scheme.Pullback.range_fst` and
  `LocallyQuasiFinite.of_finite_preimage_singleton` supply the closed-point and
  finite-fiber approach to the converse.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A locally quasi-finite, quasi-compact morphism has finitely many lifts of each
field-valued point of its base. The field is arbitrary: neither algebraic
closedness of the field nor local finite type of the morphism is assumed. -/
theorem finite_field_valued_fiber [LocallyQuasiFinite f] [QuasiCompact f]
    {K : Type u} [Field K] (g : Spec (CommRingCat.of K) ⟶ Y) :
    Set.Finite {q : Spec (CommRingCat.of K) ⟶ X | q ≫ f = g} := by
  classical
  let P : Scheme.{u} := Limits.pullback f g
  let h : P ⟶ Spec (CommRingCat.of K) := Limits.pullback.snd f g
  have : IsFinite h := IsFinite.of_locallyQuasiFinite h
  have : IsAffine P := isAffine_of_isAffineHom h
  let e := P.isoSpec
  let φ : CommRingCat.of K ⟶ Γ(P, ⊤) := Spec.preimage (e.inv ≫ h)
  let : Algebra K Γ(P, ⊤) := φ.hom.toAlgebra
  have hφ : Spec.algebraMap K Γ(P, ⊤) = e.inv ≫ h := by
    change Spec.map φ = _
    exact Spec.map_preimage _
  have : Module.Finite K Γ(P, ⊤) := by
    apply RingHom.finite_algebraMap.mp
    apply (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap K Γ(P, ⊤)))).mp
    change IsFinite (Spec.algebraMap K Γ(P, ⊤))
    rw [hφ]
    infer_instance
  let lift (q : {q : Spec (CommRingCat.of K) ⟶ X // q ≫ f = g}) :
      Spec (CommRingCat.of K) ⟶ P :=
    Limits.pullback.lift q.1 (𝟙 _) (by simpa only [Category.id_comp] using q.2)
  let E := Spec.homEquivAlgHom (R := K) (A := Γ(P, ⊤)) (B := K)
  change Finite {q : Spec (CommRingCat.of K) ⟶ X // q ≫ f = g}
  refine Finite.of_injective (fun q => E ⟨lift q ≫ e.hom, ?_⟩) ?_
  · rw [hφ]
    simp [Category.assoc, lift, h, Limits.pullback.lift_snd, Spec.algebraMap]
  · intro q r hqr
    have hqr' : lift q ≫ e.hom = lift r ≫ e.hom :=
      congrArg Subtype.val (E.injective hqr)
    have hqr'' : lift q = lift r := (cancel_mono e.hom).mp hqr'
    apply Subtype.ext
    simpa only [lift, Limits.pullback.lift_fst] using
      congrArg (fun p : Spec (CommRingCat.of K) ⟶ P =>
        p ≫ Limits.pullback.fst f g) hqr''

/-- A locally-of-finite-type morphism is locally quasi-finite if the set of lifts
of every point valued in every algebraically closed field is finite.
No quasi-compactness hypothesis is imposed on the morphism. -/
theorem locallyQuasiFinite_of_finite_geometric_point_fibers [LocallyOfFiniteType f]
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (g : Spec (CommRingCat.of K) ⟶ Y),
      Set.Finite {q : Spec (CommRingCat.of K) ⟶ X | q ≫ f = g}) :
    LocallyQuasiFinite f := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton f
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  let g : Spec (CommRingCat.of K) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
      Y.fromSpecResidueField y
  let P : Scheme.{u} := Limits.pullback f g
  have : Finite {q : Spec (CommRingCat.of K) ⟶ X // q ≫ f = g} := h K g
  -- A section of the geometric fiber is determined by its first projection.
  have : Finite {q : Spec (CommRingCat.of K) ⟶ P //
      q ≫ Limits.pullback.snd f g = 𝟙 _} := by
    refine Finite.of_injective
      (fun q ↦ (⟨q.1 ≫ Limits.pullback.fst f g, ?_⟩ :
        {q : Spec (CommRingCat.of K) ⟶ X // q ≫ f = g})) ?_
    · rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
        q.2, Category.id_comp]
    · intro q₁ q₂ e
      apply Subtype.ext
      apply Limits.pullback.hom_ext
      · exact congrArg Subtype.val e
      · exact q₁.2.trans q₂.2.symm
  have hclosed : (closedPoints P).Finite :=
    Finite.of_surjective (pointEquivClosedPoint (Limits.pullback.snd f g))
      (pointEquivClosedPoint (Limits.pullback.snd f g)).surjective
  let : JacobsonSpace P :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd f g)
  let : DiscreteTopology P := JacobsonSpace.discreteTopology hclosed
  let : Finite P := Set.finite_univ_iff.mp (by
    simpa only [closedPoints_eq_univ] using hclosed)
  have hg : Set.range g = {y} := Set.range_eq_singleton fun x ↦ by
    simp only [g, Scheme.Hom.comp_apply]
    exact Y.fromSpecResidueField_apply y _
  simpa only [Set.image_univ, Scheme.Pullback.range_fst, hg] using
    (Set.finite_univ (α := P)).image (Limits.pullback.fst f g)

/-- A locally-of-finite-type, quasi-compact morphism is locally quasi-finite
exactly when the set of lifts of every point valued in every algebraically
closed field is finite. Local finite type is used for the reverse implication,
and quasi-compactness for the forward implication. -/
theorem locallyQuasiFinite_iff_finite_geometric_point_fibers
    [LocallyOfFiniteType f] [QuasiCompact f] :
    LocallyQuasiFinite f ↔ ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (g : Spec (CommRingCat.of K) ⟶ Y),
      Set.Finite {q : Spec (CommRingCat.of K) ⟶ X | q ≫ f = g} := by
  constructor
  · intro hf K _ _ g
    let : LocallyQuasiFinite f := hf
    exact finite_field_valued_fiber f g
  · exact locallyQuasiFinite_of_finite_geometric_point_fibers f

end AlgebraicGeometry.Scheme.Hom
