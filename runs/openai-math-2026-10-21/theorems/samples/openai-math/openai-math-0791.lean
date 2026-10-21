namespace OAI

namespace LowSpaceSubsetSum

namespace SamplerAttempts

variable {Ω : Type*}

theorem runCostAcc_value (test : Ω → Bool × ℕ)
    (N : ℕ) (f : Fin N → Ω) (reads work : ℕ) :
    (runCostAcc test N f reads work).1 = firstAccept (fun a => (test a).1 = true) N f := by
  induction N generalizing reads work with
  | zero => rfl
  | succ N ih =>
    simp only [runCostAcc, firstAccept]
    split
    · rfl
    · exact ih _ _ _

end SamplerAttempts
end LowSpaceSubsetSum
end OAI
