public section

open Filter GenContFract

open GenContFract (of)

namespace Real

variable {ξ : ℝ}

theorem tendsto_den_convergent (hξ : Irrational ξ) :
    Tendsto (fun n ↦ (ξ.convergent n).den) atTop atTop :=
  tendsto_atTop_mono' atTop ((eventually_ge_atTop 4).mono fun n hn ↦
    (Nat.le_succ n).trans ((Nat.le_fib_self (by omega)).trans (fib_succ_le_den_convergent hξ n)))
    tendsto_id

end Real
end
