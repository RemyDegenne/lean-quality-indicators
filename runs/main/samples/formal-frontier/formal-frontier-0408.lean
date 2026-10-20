set_option warningAsError true

@[expose] public section

universe u v w

namespace ContinuousMap

variable {X : Type u} [TopologicalSpace X]

variable {ι : Type v}

@[simp] theorem cauchyKernel_zero (a : ι → C(X, ℂ)) (i : ι) :
    cauchyKernel a i 0 = 1 := by
  change Ring.inverse (1 - (0 : ℂ) • a i) = 1
  rw [zero_smul ℂ (a i), sub_zero, Ring.inverse_one]

end ContinuousMap
end
