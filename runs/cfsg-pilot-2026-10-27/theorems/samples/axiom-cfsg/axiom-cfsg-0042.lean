public section

namespace CFSG.Quasithin

open CFSG.Sporadic.Bridge

namespace F6

namespace G22Perm

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

include hk2 in
theorem exists_rep
    (g : G2Group k) : ∃ (x : U33G) (ε : Bool), g = g2HomC h2 x * rhoPow h2 ε := by
  have D := g2IndexTwoData h2 hk2
  rcases D.cover g with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨x, false, by rw [hx]; simp [rhoPow]⟩
  · refine ⟨x, true, ?_⟩
    simp only [rhoPow, ite_true]
    rw [hx, mul_assoc, D.sq, mul_one]

end G22Perm
end F6
end CFSG.Quasithin
end
