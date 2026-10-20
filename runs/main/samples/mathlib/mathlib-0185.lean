@[expose] public section

notation:25 P " →ᴬ[" R "] " Q => ContinuousAffineMap R P Q

namespace ContinuousLinearMap

variable {R V W : Type*} [Ring R]

variable [AddCommGroup V] [Module R V] [TopologicalSpace V]

variable [AddCommGroup W] [Module R W] [TopologicalSpace W]

@[simp]
theorem toContinuousAffineMap_map_zero (f : V →L[R] W) : f.toContinuousAffineMap 0 = 0 := by simp

end ContinuousLinearMap
end
