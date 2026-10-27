public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5

open CFSG.Sporadic.Co2Rank

variable {G : Type*} [Group G]

section

variable {n : ℕ} {v : ℕ → G} {adj : ℕ → ℕ → Bool} {pr : ℕ → ℕ → ℕ}

theorem pr_not_mem (hs : Setting n v adj pr) {S : List ℕ} (hS : SInv n v S) {m : ℕ} (hm : m < n)
    (hmS : m ∉ S) (hadj : ∀ s ∈ S, adj m s = true) : ∀ s ∈ S, pr m s ∉ S := by
  have hvm := not_mem_Sset hs hS hm hmS
  intro s hsS hin
  apply hvm
  have h1 : v m * v s ∈ Sset v S := by
    rw [← (hs.pr_spec m s (hadj s hsS)).2]
    exact Or.inr ⟨pr m s, hin, rfl⟩
  have h2 := (hS.closed _ h1 (v s) (Or.inr ⟨s, hsS, rfl⟩)).1
  have h3 : v m * v s * v s = v m := by rw [mul_assoc, (hs.sq s (hS.lt s hsS)).1, mul_one]
  rwa [h3] at h2

end
end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D5
end
