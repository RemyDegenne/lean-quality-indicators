namespace OAI

noncomputable section

namespace PiExponentSeshadri.IdealModule

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

variable {X Y : Scheme.{u}}

lemma closed_image (I : X.IdealSheafData) (U : X.affineOpens) :
    ((closedInclusion I).val.app (op U.1)).hom.range = I.ideal U := by
  exact (image_eq_ideal I.subschemeι U).trans (congrArg (fun J => J.ideal U) I.ker_subschemeι)

end
end PiExponentSeshadri.IdealModule
end
end OAI
