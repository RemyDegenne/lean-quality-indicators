@[expose] public section

namespace ContinuousAffineMap

variable {R V W W₂ P Q Q₂ : Type*} [NormedField R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [AddTorsor V P] [TopologicalSpace P]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [AddTorsor W Q] [TopologicalSpace Q]
  [AddCommGroup W₂] [Module R W₂] [TopologicalSpace W₂] [AddTorsor W₂ Q₂] [TopologicalSpace Q₂]

section Affine

variable [IsTopologicalAddTorsor P] [IsTopologicalAddTorsor Q] [IsTopologicalAddTorsor Q₂]

variable {α : Type*} [TopologicalSpace α]

section postcompA

variable
  [IsTopologicalAddGroup W] [ContinuousConstSMul R W]
  [IsTopologicalAddGroup W₂] [ContinuousConstSMul R W₂]

variable (P) in
/-- Post-composition of continuous affine maps by a fixed continuous linear map, as a continuous
linear map. -/
@[simps]
def _root_.ContinuousLinearMap.postcompContinuousAffineMap (f : W →L[R] W₂) :
    (P →ᴬ[R] W) →L[R] (P →ᴬ[R] W₂) where
  toFun g := f.toContinuousAffineMap.comp g
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

end postcompA
end Affine
end ContinuousAffineMap
end
