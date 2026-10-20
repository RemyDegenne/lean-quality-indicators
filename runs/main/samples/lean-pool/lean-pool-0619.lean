section

@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

namespace NavierStokes.LoopMoments

open scoped BigOperators

noncomputable section

variable {ι : Type*}

theorem variance_identity (s : Finset ι) (w t : ι → ℝ) (m : ℝ)
    (hmass : ∑ i ∈ s, w i = 1) (hmean : avg s w t = m) :
    avg s w (fun i => (t i - m) ^ 2) = avg s w (fun i => t i ^ 2) - m ^ 2 := by
  calc
    avg s w (fun i => (t i - m) ^ 2) =
        avg s w (fun i => t i ^ 2 - (2 * m) * t i + m ^ 2) := by
          congr 1
          funext i
          ring
    _ = avg s w (fun i => t i ^ 2) - (2 * m) * avg s w t + m ^ 2 := by
          rw [avg_add, avg_sub, avg_const_mul, avg_const s w (m ^ 2) hmass]
    _ = avg s w (fun i => t i ^ 2) - m ^ 2 := by rw [hmean]; ring

end
end NavierStokes.LoopMoments
end
end
