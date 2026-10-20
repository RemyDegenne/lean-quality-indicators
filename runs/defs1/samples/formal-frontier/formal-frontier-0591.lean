@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- Compare sheafification of the chosen commutative and ordinary ring pullbacks. -/
noncomputable def constructedComparison (S : Y.Sheaf CommRingCat.{v}) :
    (sheafForget X).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{v}).obj
        ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj S.obj)) ≅
    (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).obj
      ((TopCat.Presheaf.pullback RingCat.{v} f).obj
        ((sheafForget Y).obj S).obj) :=
  ((sheafComposeNatIso (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{v} RingCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) RingCat.{v})).app
      ((TopCat.Presheaf.pullback CommRingCat.{v} f).obj S.obj)).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso
      (PresheafInverseImage.commRingPullbackComparison f S.obj)

end RingedSpaces.Modules.SheafInverseImage
end
