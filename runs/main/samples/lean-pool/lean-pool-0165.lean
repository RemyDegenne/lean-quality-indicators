@[expose] public section

open CategoryTheory AlgebraicTopology

namespace SphereOddDegree

namespace GradedCupPullback

variable {A : ℕ → Type*}

theorem pull_pow_fixed (G : GradedCupPullback A) {x : A 1} (hx : G.pull x = x) (n : ℕ) :
    G.pull (G.pow x n) = G.pow x n := by rw [pull_pow, hx]

end GradedCupPullback
end SphereOddDegree
end
