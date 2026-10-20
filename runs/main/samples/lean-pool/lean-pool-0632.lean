@[expose] public section

noncomputable section

notation ρ "[" idx " ↦ " x "]" => updateVar ρ idx x

section

@[expose] public section

namespace LeanCert.Core

namespace IntervalDyadic

theorem mem_of_mem_bisect_left {x : ℝ} {I : IntervalDyadic}
    (hx : x ∈ (I.bisect).1) : x ∈ I := by
  refine ⟨hx.1, hx.2.trans ?_⟩
  exact_mod_cast I.midpoint_le_hi

end IntervalDyadic
end LeanCert.Core
end
end
end
end
