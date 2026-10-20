public section

noncomputable section

open scoped NNReal Topology

open Filter NormedSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace IsMDissipative

variable {A : X →ₗ.[ℝ] X}

theorem yosidaLimit_time_add (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x) :=
  yosidaLimit_time_add_of_tendsto_of_norm_le x
    (hA.tendsto_yosidaLimit hdense ht x)
    (hA.tendsto_yosidaLimit hdense hs (yosidaLimit A t x))
    (hA.tendsto_yosidaLimit hdense (add_nonneg hs ht) x)
    (hA.eventually_norm_exp_smul_yosidaApproximation_le hs)

end IsMDissipative
end TauCeti.Semigroups
end
end
