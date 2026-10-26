/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.RationalFunctionFieldReconstruction
public import SchemeProperties.IntegralDominantRationalCategoryOver

public section

/-!
# Inverses of integral dominant rational maps over a chosen base

If the field map induced by a given dominant rational arrow is an isomorphism,
it induces an inverse over independently chosen structure morphisms, provided
the structure morphism of the original source is locally of finite type. The
reverse implication needs no finiteness hypothesis. These are isomorphisms of
dominant quotient rational arrows, not isomorphisms of total schemes. The
construction adapts an earlier Formal Frontier proof of this criterion.

## References

* Formal Frontier, earlier formalization of the chosen-base dominant rational
  inverse criterion: inverse field homomorphism, compatibility triangle and
  reconstruction with target the original source; the proof expression here
  is adapted from that contribution.
* Scheme Properties, `RationalFunctionFieldReconstruction`,
  `RationalFunctionFieldPullback` and `RationalFunctionFieldFaithfulness`:
  reconstruction, composition and identity readback, and equality reflection.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.IntegralDominantRationalSchemeOver

variable {S : Scheme.{u}} {X Y : IntegralDominantRationalSchemeOver S}

private theorem inverse_compatible (f : X ⟶ Y)
    [IsIso f.toRationalMap.functionFieldMap] :
    (Spec.map (inv f.toRationalMap.functionFieldMap) ≫
      X.toScheme.fromSpecStalk (genericPoint X.toScheme)) ≫ X.toBase =
      Y.toScheme.fromSpecStalk (genericPoint Y.toScheme) ≫ Y.toBase := by
  have hbase := Scheme.RationalMap.functionFieldMap_compatible
    X.toBase Y.toBase f.toRationalMap (isOver_iff_compHom.mp f.isOver)
  have hinv : Spec.map (inv f.toRationalMap.functionFieldMap) ≫
      Spec.map f.toRationalMap.functionFieldMap = 𝟙 _ := by
    rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]
  calc
    (Spec.map (inv f.toRationalMap.functionFieldMap) ≫
        X.toScheme.fromSpecStalk (genericPoint X.toScheme)) ≫ X.toBase =
      Spec.map (inv f.toRationalMap.functionFieldMap) ≫
        ((Spec.map f.toRationalMap.functionFieldMap ≫
          Y.toScheme.fromSpecStalk (genericPoint Y.toScheme)) ≫ Y.toBase) := by
            simp only [Category.assoc, hbase]
    _ = Y.toScheme.fromSpecStalk (genericPoint Y.toScheme) ≫ Y.toBase := by
      simp only [← Category.assoc, hinv, Category.id_comp]

private def inverse (f : X ⟶ Y) [LocallyOfFiniteType X.toBase]
    [IsIso f.toRationalMap.functionFieldMap] : Y ⟶ X := by
  let q := Scheme.RationalMap.ofFunctionFieldMap Y.toBase X.toBase
    (inv f.toRationalMap.functionFieldMap) (inverse_compatible f)
  exact hom q inferInstance ((isOver_iff_compHom).2
    (Scheme.RationalMap.ofFunctionFieldMap_compHom Y.toBase X.toBase
      (inv f.toRationalMap.functionFieldMap) (inverse_compatible f)))

private theorem inverse_functionFieldMap (f : X ⟶ Y) [LocallyOfFiniteType X.toBase]
    [IsIso f.toRationalMap.functionFieldMap] :
    (inverse f).toRationalMap.functionFieldMap = inv f.toRationalMap.functionFieldMap := by
  exact Scheme.RationalMap.functionFieldMap_ofFunctionFieldMap Y.toBase X.toBase
    (inv f.toRationalMap.functionFieldMap) (inverse_compatible f)

/-- The function-field map of an invertible chosen-base rational arrow is
invertible by contravariant composition and identity readback, with no local
finite type hypothesis. -/
theorem isIso_functionFieldMap (f : X ⟶ Y) [IsIso f] :
    IsIso f.toRationalMap.functionFieldMap := by
  let g := inv f
  have h₁ : f.toRationalMap.comp g.toRationalMap = Scheme.RationalMap.id X.toScheme := by
    have h := congrArg (fun h : X ⟶ X => h.toRationalMap) (IsIso.hom_inv_id f)
    simpa only [toRationalMap_comp, toRationalMap_id] using h
  have h₂ : g.toRationalMap.comp f.toRationalMap = Scheme.RationalMap.id Y.toScheme := by
    have h := congrArg (fun h : Y ⟶ Y => h.toRationalMap) (IsIso.inv_hom_id f)
    simpa only [toRationalMap_comp, toRationalMap_id] using h
  have hφψ : g.toRationalMap.functionFieldMap ≫ f.toRationalMap.functionFieldMap =
      𝟙 X.toScheme.functionField := by
    calc
      _ = (f.toRationalMap.comp g.toRationalMap).functionFieldMap :=
        (Scheme.RationalMap.functionFieldMap_comp _ _).symm
      _ = 𝟙 X.toScheme.functionField := by
        simp only [h₁, Scheme.RationalMap.functionFieldMap_id]
  have hψφ : f.toRationalMap.functionFieldMap ≫ g.toRationalMap.functionFieldMap =
      𝟙 Y.toScheme.functionField := by
    calc
      _ = (g.toRationalMap.comp f.toRationalMap).functionFieldMap :=
        (Scheme.RationalMap.functionFieldMap_comp _ _).symm
      _ = 𝟙 Y.toScheme.functionField := by
        simp only [h₂, Scheme.RationalMap.functionFieldMap_id]
  exact ⟨⟨g.toRationalMap.functionFieldMap, hψφ, hφψ⟩⟩

/-- For an arrow over independently chosen maps to `S`, local finite type of
the original source map suffices to reflect a function-field isomorphism to
an isomorphism of the given dominant rational arrow. The construction adapts
the earlier Formal Frontier inverse-field-map argument via reconstruction and
faithfulness; the converse requires no finite-type hypothesis. -/
theorem isIso_iff_isIso_functionFieldMap (f : X ⟶ Y)
    [LocallyOfFiniteType X.toBase] :
    IsIso f ↔ IsIso f.toRationalMap.functionFieldMap := by
  constructor
  · intro hf
    exact @isIso_functionFieldMap _ _ _ f hf
  · intro hφ
    let g := @inverse _ _ _ f _ hφ
    have h₁ : f.toRationalMap.comp g.toRationalMap = Scheme.RationalMap.id X.toScheme := by
      apply Scheme.RationalMap.eq_of_functionFieldMap_eq
      calc
        _ = g.toRationalMap.functionFieldMap ≫ f.toRationalMap.functionFieldMap :=
          Scheme.RationalMap.functionFieldMap_comp _ _
        _ = inv f.toRationalMap.functionFieldMap ≫ f.toRationalMap.functionFieldMap := by
          rw [@inverse_functionFieldMap _ _ _ f _ hφ]
        _ = 𝟙 X.toScheme.functionField :=
          @IsIso.inv_hom_id _ _ _ _ f.toRationalMap.functionFieldMap hφ
        _ = (Scheme.RationalMap.id X.toScheme).functionFieldMap :=
          Scheme.RationalMap.functionFieldMap_id.symm
    have h₂ : g.toRationalMap.comp f.toRationalMap = Scheme.RationalMap.id Y.toScheme := by
      apply Scheme.RationalMap.eq_of_functionFieldMap_eq
      calc
        _ = f.toRationalMap.functionFieldMap ≫ g.toRationalMap.functionFieldMap :=
          Scheme.RationalMap.functionFieldMap_comp _ _
        _ = f.toRationalMap.functionFieldMap ≫ inv f.toRationalMap.functionFieldMap := by
          rw [@inverse_functionFieldMap _ _ _ f _ hφ]
        _ = 𝟙 Y.toScheme.functionField :=
          @IsIso.hom_inv_id _ _ _ _ f.toRationalMap.functionFieldMap hφ
        _ = (Scheme.RationalMap.id Y.toScheme).functionFieldMap :=
          Scheme.RationalMap.functionFieldMap_id.symm
    have hg₁ : f ≫ g = 𝟙 X := by
      apply hom_ext
      simpa only [toRationalMap_comp, toRationalMap_id] using h₁
    have hg₂ : g ≫ f = 𝟙 Y := by
      apply hom_ext
      simpa only [toRationalMap_comp, toRationalMap_id] using h₂
    exact ⟨⟨g, hg₁, hg₂⟩⟩

end AlgebraicGeometry.IntegralDominantRationalSchemeOver
