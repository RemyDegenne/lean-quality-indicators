/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Partial-map extension at valuation stalks

The local valuative ingredient of normal-source extension to a proper relative target,
expressed with the existing partial-map carrier and explicit equations over the base.

## Limitations

Only the local extension at a valuation-stalk point is constructed here.
No normal-source codimension corollary, maximal-domain construction, or union gluing is supplied.

## References

* J. S. Milne, *Abelian Varieties*, I.3.1: the codimension-one valuative extension argument.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.PartialMap

private theorem exists_extension_of_valuationRing_stalk_aux {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY] (p : X.PartialMap Y)
    (hp : p.hom ≫ sY = p.domain.ι ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ q : X.PartialMap Y,
      x ∈ q.domain ∧
      q.hom ≫ sY = q.domain.ι ≫ sX ∧
      q.toRationalMap = p.toRationalMap ∧
      X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
        X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
  classical
  -- The function field is canonically the fraction field of the actual stalk at `x`.
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap (X.presheaf.stalk x) X.functionField))
  have hj : j ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
    change Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ _ = _
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  have hpK : p.fromFunctionField ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX := by
    dsimp only [fromFunctionField, fromSpecStalkOfMem]
    rw [Category.assoc, hp, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  let square : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x
      commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
      domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
      valuationRing := inferInstanceAs (ValuationRing (X.presheaf.stalk x))
      K := X.functionField
      field := inferInstanceAs (Field X.functionField)
      algebra := inferInstanceAs (Algebra (X.presheaf.stalk x) X.functionField)
      isFractionRing := inferInstanceAs
        (IsFractionRing (X.presheaf.stalk x) X.functionField)
      i₁ := p.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ sX
      commSq := ⟨by
        change p.fromFunctionField ≫ sY = j ≫ (X.fromSpecStalk x ≫ sX)
        rw [← Category.assoc, hj]
        exact hpK⟩ }
  have hvaluative : ValuativeCriterion.Existence sY := by
    have hclosed : UniversallyClosed sY := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hclosed
    exact hclosed.1
  obtain ⟨τ, hτK, hτS⟩ := (hvaluative square).exists_lift
  change j ≫ τ = p.fromFunctionField at hτK
  change τ ≫ sY = X.fromSpecStalk x ≫ sX at hτS
  -- Finite type and germ injectivity spread the lift to a genuine native partial map.
  let q := ofFromSpecStalk sX sY τ hτS
  have hxq : x ∈ q.domain := mem_domain_ofFromSpecStalk sX sY τ hτS
  have hqS : q.hom ≫ sY = q.domain.ι ≫ sX := ofFromSpecStalk_comp sX sY τ hτS
  have hqK : q.fromFunctionField = p.fromFunctionField := by
    calc
      q.fromFunctionField = j ≫ q.fromSpecStalkOfMem hxq := by
        dsimp only [fromFunctionField, fromSpecStalkOfMem]
        rw [← Category.assoc]
        congr 1
        apply (cancel_mono q.domain.ι).mp
        simpa only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι] using hj.symm
      _ = j ≫ τ := by
        rw [fromSpecStalkOfMem_ofFromSpecStalk]
      _ = p.fromFunctionField := hτK
  have hqrat : q.toRationalMap = p.toRationalMap :=
    RationalMap.eq_of_fromFunctionField_eq _ _ hqK
  -- Relative separatedness upgrades generic agreement to the entire intersection.
  let : X.Over S := .ofHom sX
  let : Y.Over S := .ofHom sY
  let : IsSeparated (Y ↘ S) := (inferInstance : IsSeparated sY)
  let : p.IsOver S := (isOver_iff (S := S) (f := p)).mpr hp
  let : q.IsOver S := (isOver_iff (S := S) (f := q)).mpr hqS
  refine ⟨q, hxq, hqS, hqrat, ?_⟩
  have hfull := (equiv_iff_of_isSeparated (S := S) (f := p) (g := q)).mp
    (toRationalMap_eq_iff.mp hqrat.symm)
  dsimp only [restrict] at hfull
  exact hfull

variable {X Y S : Scheme.{u}} [IsIntegral X]
variable (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY] (p : X.PartialMap Y)
variable (hp : p.hom ≫ sY = p.domain.ι ≫ sX)
variable (x : X) [ValuationRing (X.presheaf.stalk x)]

/-- A noncanonically chosen representative of `p` defined at `x` and over the given base.
Only agreement on the common domain is asserted: the chosen neighborhood need not contain
all of `p.domain`, and no uniqueness of the partial map or its domain is claimed. -/
noncomputable def extensionOfValuationRingStalk : X.PartialMap Y :=
  (exists_extension_of_valuationRing_stalk_aux sX sY p hp x).choose

/-- The chosen representative is defined at the valuation-stalk point. -/
theorem mem_domain_extensionOfValuationRingStalk :
    x ∈ (extensionOfValuationRingStalk sX sY p hp x).domain :=
  (exists_extension_of_valuationRing_stalk_aux sX sY p hp x).choose_spec.1

/-- The chosen representative respects the specified base maps. -/
theorem extensionOfValuationRingStalk_comp :
    (extensionOfValuationRingStalk sX sY p hp x).hom ≫ sY =
      (extensionOfValuationRingStalk sX sY p hp x).domain.ι ≫ sX :=
  (exists_extension_of_valuationRing_stalk_aux sX sY p hp x).choose_spec.2.1

/-- The chosen representative determines the original rational map. -/
theorem extensionOfValuationRingStalk_toRationalMap :
    (extensionOfValuationRingStalk sX sY p hp x).toRationalMap = p.toRationalMap :=
  (exists_extension_of_valuationRing_stalk_aux sX sY p hp x).choose_spec.2.2.1

/-- The original and chosen representatives agree on their entire intersection. -/
theorem extensionOfValuationRingStalk_inter :
    X.homOfLE (inf_le_left :
        p.domain ⊓ (extensionOfValuationRingStalk sX sY p hp x).domain ≤ p.domain) ≫ p.hom =
      X.homOfLE (inf_le_right :
          p.domain ⊓ (extensionOfValuationRingStalk sX sY p hp x).domain ≤
            (extensionOfValuationRingStalk sX sY p hp x).domain) ≫
        (extensionOfValuationRingStalk sX sY p hp x).hom :=
  (exists_extension_of_valuationRing_stalk_aux sX sY p hp x).choose_spec.2.2.2

/-- A partial map over a base to a proper target has an equivalent representative defined at
any point whose stalk is a valuation ring. The two morphisms agree on their entire common
domain. This is the valuation-stalk form of the local argument underlying Milne,
*Abelian Varieties*, I.3.1. -/
theorem exists_extension_of_valuationRing_stalk {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY] (p : X.PartialMap Y)
    (hp : p.hom ≫ sY = p.domain.ι ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ q : X.PartialMap Y,
      x ∈ q.domain ∧
      q.hom ≫ sY = q.domain.ι ≫ sX ∧
      q.toRationalMap = p.toRationalMap ∧
      X.homOfLE (inf_le_left : p.domain ⊓ q.domain ≤ p.domain) ≫ p.hom =
        X.homOfLE (inf_le_right : p.domain ⊓ q.domain ≤ q.domain) ≫ q.hom := by
  exact ⟨extensionOfValuationRingStalk sX sY p hp x,
    mem_domain_extensionOfValuationRingStalk sX sY p hp x,
    extensionOfValuationRingStalk_comp sX sY p hp x,
    extensionOfValuationRingStalk_toRationalMap sX sY p hp x,
    extensionOfValuationRingStalk_inter sX sY p hp x⟩

end AlgebraicGeometry.Scheme.PartialMap
