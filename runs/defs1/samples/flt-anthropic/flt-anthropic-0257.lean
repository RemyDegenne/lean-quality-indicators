set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.OModulePresheaf

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

variable (F G : OModulePresheaf π)

def tensor : OModulePresheaf π where
  obj U := F.obj U ⊗[Γ(V, U)] G.obj U
  addCommGroup _ := inferInstance
  module U := F.tensorObjModule G U
  moduleSections _ := inferInstance
  isScalarTower U :=

    @IsScalarTower.mk R Γ(V, U) _ (_) (_) (_)
      fun r a t => mul_smul ((Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r) a t
  res h := F.tensorRes G h
  res_smul h a t := (F.tensorResₛₗ G h).map_smulₛₗ a t
  res_refl U := by
    letI := F.tensorObjModule G U
    refine LinearMap.ext fun t => ?_
    show F.tensorResₛₗ G (le_refl U) t = t
    induction t using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul x y => rw [tensorResₛₗ_tmul, res_refl_apply, res_refl_apply]
    | add s t hs ht => rw [map_add, hs, ht]
  res_comp {U U' U''} h h' := by
    letI := F.tensorObjModule G U; letI := F.tensorObjModule G U''
    refine LinearMap.ext fun t => ?_
    show F.tensorResₛₗ G (h.trans h') t = F.tensorResₛₗ G h (F.tensorResₛₗ G h' t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => rw [tensorResₛₗ_tmul, tensorResₛₗ_tmul, tensorResₛₗ_tmul, res_res, res_res]
    | add s t hs ht => rw [map_add, hs, ht, map_add, map_add]

end AlgebraicGeometry.OModulePresheaf
end
