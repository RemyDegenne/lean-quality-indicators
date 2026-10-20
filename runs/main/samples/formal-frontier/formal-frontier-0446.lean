@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

set_option maxHeartbeats 1000000 in
theorem ringUnit_full (S : Y.Sheaf CommRingCat.{v})
    (V : (Opens Y)ᵒᵖ) (r : (sourceRing S).obj.obj V) :
    (ringIso f S).hom.hom.app ((Opens.map f).op.obj V)
      ((actualUnit f S).hom.app V r) =
    (toSheafify (Opens.grothendieckTopology X) (pointwiseRing f S)).app
      ((Opens.map f).op.obj V)
      (((Opens.map f).op.pointwiseLeftKanExtensionUnit (sourceRing S).obj).app V r) := by
  have hc := RingedSpaces.Modules.SheafInverseImage.comparison_unit_app f S V
  have hd := RingedSpaces.Modules.SheafInverseImage.ringUnit_pointwise f (sourceRing S) V r
  change (RingedSpaces.Modules.PresheafInverseImage.inverseImageSheafRingComparison f (sourceRing S)).inv.hom.app
      ((Opens.map f).op.obj V)
      ((RingedSpaces.Modules.SheafInverseImage.comparison f S).hom.hom.app
        ((Opens.map f).op.obj V) ((actualUnit f S).hom.app V r)) = _
  have hc' : (RingedSpaces.Modules.SheafInverseImage.comparison f S).hom.hom.app
      ((Opens.map f).op.obj V) ((actualUnit f S).hom.app V r) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{v} f).unit.app
        (sourceRing S)).hom.app V r := by
    convert congrArg (fun t => t r) hc using 1; rfl
  rw [hc']
  exact hd

end RingedSpaces.Modules.SheafInverseImage
end
