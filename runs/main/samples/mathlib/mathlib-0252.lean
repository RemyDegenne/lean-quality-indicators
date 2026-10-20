@[expose] public section

noncomputable section

open Filter Set

open scoped Topology

namespace Complex

open Real

theorem tanh_periodic : Function.Periodic tanh (π * I) := by
  simp [tanh_eq_sinh_div_cosh]

end Complex
end
end
