public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SheafCohomology.HigherDirectImageFilteredColimit

variable {X : TopCat.{u}} (U : Opens X)

open CategoryTheory.Sheaf.OpenCohomology

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

variable [HasSheafify
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  AddCommGrpCat.{u}]

variable [(Opens.grothendieckTopology X).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [((Opens.grothendieckTopology X).over U).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u})]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

variable [HasExt.{u} (CategoryTheory.Sheaf
  ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})]

variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u})]

/-- Cohomology on an open over-site agrees additively with cohomology after
transport to the corresponding topological subspace. -/
@[expose] noncomputable def HOverEquivHSubspace
    (G : CategoryTheory.Sheaf
      ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})
    (n : ℕ) :
    CategoryTheory.Sheaf.H G n ≃+
      CategoryTheory.Sheaf.H
        ((U.sheafEquivOver (A := AddCommGrpCat.{u})).functor.obj G) n := by
  let E := U.sheafEquivOver (A := AddCommGrpCat.{u})
  let : E.functor.Additive :=
    E.functor.additive_of_preserves_binary_products
  let : E.inverse.Additive :=
    E.inverse.additive_of_preserves_binary_products
  let A := (constantSheaf ((Opens.grothendieckTopology X).over U)
    AddCommGrpCat.{u}).obj ↧(ULift ℤ)
  let B := (constantSheaf (Opens.grothendieckTopology (TopCat.of U))
    AddCommGrpCat.{u}).obj ↧(ULift ℤ)
  let e₁ : Abelian.Ext A G n ≃+
      Abelian.Ext A (E.inverse.obj (E.functor.obj G)) n :=
    (((Abelian.extFunctor n).obj (.op A)).mapIso
      (E.unitIso.app G)).addCommGroupIsoToAddEquiv
  let e₂ : Abelian.Ext A (E.inverse.obj (E.functor.obj G)) n ≃+
      Abelian.Ext (E.functor.obj A) (E.functor.obj G) n :=
    E.toAdjunction.extEquiv.symm
  let e₃ : Abelian.Ext (E.functor.obj A) (E.functor.obj G) n ≃+
      Abelian.Ext B (E.functor.obj G) n :=
    (((Abelian.extFunctor n).mapIso (overConstantIso U).symm.op).app
      (E.functor.obj G)).addCommGroupIsoToAddEquiv
  exact e₁.trans (e₂.trans e₃)

end SheafCohomology.HigherDirectImageFilteredColimit
end
end
