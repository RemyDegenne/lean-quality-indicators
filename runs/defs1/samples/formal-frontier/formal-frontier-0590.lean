@[expose] public section

open CategoryTheory TopologicalSpace

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The natural Hom equivalence for the sheafified tensor presheaf. -/
noncomputable def tensorSheafHomEquiv (theta : A ⟶ B) (M : Sheaves A) (N : Sheaves B) :
    ((tensorSheafFunctor A B theta).obj M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N) :=
  ((moduleSheafificationAdjunction B).homEquiv
      (tensorPresheaf A.obj B.obj theta.hom M.val) N).trans
    ((tensorPresheafHomEquiv A.obj B.obj theta.hom M.val N.val).trans
      ((SheafOfModules.fullyFaithfulForget (ringSheaf A)).homEquiv
        (X := M) (Y := (SheafOfModules.restrictScalars (ringSheafMap A B theta)).obj N)).symm)

end RingedSpaces.Modules
end
