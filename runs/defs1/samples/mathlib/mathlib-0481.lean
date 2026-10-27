@[expose] public section

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

open ConcreteCategory

section

variable {C : Type*} [Category* C]

variable {ι : Type*} [HasProductsOfShape ι C]

variable (C) in
/-- A category `C` has the `w`-IPC property it satisfies the IPC-property for every `ι : Type w`. -/
class IsIPC [HasProducts.{w} C] [HasFilteredColimitsOfSize.{w} C] : Prop where
  isIPCOfShape (ι : Type w) : IsIPCOfShape.{w} ι C := by infer_instance

end
end CategoryTheory.Limits
end
