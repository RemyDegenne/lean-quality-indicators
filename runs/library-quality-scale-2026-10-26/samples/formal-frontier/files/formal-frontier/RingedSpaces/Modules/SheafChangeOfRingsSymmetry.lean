/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import RingedSpaces.Modules.PresheafChangeOfRingsSymmetry
public import RingedSpaces.Modules.SheafChangeOfRings

/-!
# Right-factor scalar extension of module sheaves

Sheafifying the genuine right-factor tensor presheaf is naturally isomorphic
to the ordinary sheafified scalar extension. This does not identify sections
of a sheafification on an arbitrary open with raw tensor products.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (21 October 2025
  draft), §2.6.4 and Exercise 2.6.K(a) (p. 92): forming a tensor presheaf
  and then sheafifying motivates the right-factor comparison. The natural
  symmetry is a project prerequisite for Exercise 7.2.D(b,c,e) (p. 205),
  not a separate claim in that exercise.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Apply right-factor scalar extension before sheafifying. -/
noncomputable def rightSheafFunctor (theta : A ⟶ B) : Sheaves A ⥤ Sheaves B :=
  (SheafOfModules.forget (ringSheaf A)) ⋙
    rightPresheafFunctor A.obj B.obj theta.hom ⋙ moduleSheafification B

/-- Sheafification of the right-factor presheaf agrees with scalar extension. -/
noncomputable def rightSheafNatIso (theta : A ⟶ B) :
    rightSheafFunctor A B theta ≅ tensorSheafFunctor A B theta :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (SheafOfModules.forget (ringSheaf A))
      (rightPresheafNatIso A.obj B.obj theta.hom)) (moduleSheafification B)

/-- Tensor symmetry commutes with the actual module-sheafification unit. -/
theorem rightSheafificationUnit_naturality (theta : A ⟶ B) (M : Sheaves A) :
    (rightPresheafIso A.obj B.obj theta.hom M.val).hom ≫
        (moduleSheafificationAdjunction B).unit.app
          (tensorPresheaf A.obj B.obj theta.hom M.val) =
      (moduleSheafificationAdjunction B).unit.app
          (rightPresheaf A.obj B.obj theta.hom M.val) ≫
        (SheafOfModules.forget (ringSheaf B) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj)).map
          ((rightSheafNatIso A B theta).hom.app M) := by
  exact (moduleSheafificationAdjunction B).unit.naturality
    (rightPresheafIso A.obj B.obj theta.hom M.val).hom

/-- The diagonal open site has the existing weak-sheafification witnesses. -/
noncomputable def opensRightSheafNatIso {X : TopCat.{u}}
    (A B : TopCat.Sheaf CommRingCat.{u} X) (theta : A ⟶ B) :
    rightSheafFunctor A B theta ≅ tensorSheafFunctor A B theta := by
  letI := opensWeakSheafify X
  letI := opensWEqualsLocallyBijective X
  exact rightSheafNatIso A B theta

end RingedSpaces.Modules

#lint-
