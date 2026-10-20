public noncomputable section

namespace Convexity.StdSimplex

open Set unitInterval

variable {ι : Type*}

attribute [local instance] Classical.decEq

variable [Fintype ι] [Nontrivial ι]

theorem hornDeformation_one_mem (a : ι) (x : StdSimplex ℝ ι) :
    hornDeformation a 1 x ∈ horn a := by
  classical
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_mem_eq_inf' (Finset.univ_nontrivial.erase_nonempty (a := a))
      (fun i => x.weights i)
  refine ⟨i, (Finset.mem_erase.mp hi).1, ?_⟩
  simp [hornDeformation_weights, (Finset.mem_erase.mp hi).1, hornDepth_def, ← hmin]

end Convexity.StdSimplex
end
