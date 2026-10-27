@[expose] public section

namespace Connes

namespace PaperDualCoordinates

open Construction

open Construction.PaperKernel

noncomputable section

/--
The `partialToDual` construction used in the Connes rigidity formalization.
-/
def partialToDual : (VStar →ₗ[k] Module.Dual k A) →ₗ[k]
    Module.Dual k AVStar where
  toFun g := TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun φ => g φ a
          map_add' := by intro φ ψ; simp
          map_smul' := by intro r φ; simp }
      map_add' := by intro a b; ext φ; simp
      map_smul' := by intro r a; ext φ; simp }
  map_add' := by intro f g; apply TensorProduct.ext'; intro a φ; simp
  map_smul' := by intro r g; apply TensorProduct.ext'; intro a φ; simp

end
end PaperDualCoordinates
end Connes
end
