@[expose] public section

open CategoryTheory TopologicalSpace

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheafification of the right-factor presheaf agrees with scalar extension. -/
noncomputable def rightSheafNatIso (theta : A ⟶ B) :
    rightSheafFunctor A B theta ≅ tensorSheafFunctor A B theta :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (SheafOfModules.forget (ringSheaf A))
      (rightPresheafNatIso A.obj B.obj theta.hom)) (moduleSheafification B)

end RingedSpaces.Modules
end
