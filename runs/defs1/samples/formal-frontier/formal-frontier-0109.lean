public section

set_option warningAsError true

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)

/-- Tensor restriction from `V` to `U` is semilinear along the actual
structure-sheaf map `Γ(Spec R, V) → Γ(Spec R, U)`. -/
@[expose]
noncomputable def sectionTensorRes {U V : (Spec R).Opens} (i : U ⟶ V) :
    TensorProduct Γ(Spec R, V) Γ(tilde M, V) Γ(tilde N, V) →ₛₗ[
      ((Spec R).presheaf.map i.op).hom]
      TensorProduct Γ(Spec R, U) Γ(tilde M, U) Γ(tilde N, U) :=
  (PresheafOfModulesOfCommRing.Monoidal.tensorObj (tilde M).val
    (tilde N).val).restrictₛₗ i.op

end AlgebraicGeometry.Scheme.Modules
end
end
