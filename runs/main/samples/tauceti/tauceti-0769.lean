public section

open Complex Set UpperHalfPlane

namespace TauCeti

namespace ModularForm

theorem im_lt_of_mem_arcSingularSet_union_verticalSingularSet {S : Finset ℍ} {s : ℂ} {H : ℝ}
    (hH : 1 < H) (hHgt : ∀ p ∈ S, (p : ℂ).im < H)
    (hs : s ∈ arcSingularSet S ∪ verticalSingularSet S) : s.im < H := by
  rcases Finset.mem_union.mp hs with h | h
  · exact im_lt_of_mem_arcSingularSet h hH
  · exact im_lt_of_mem_verticalSingularSet h hHgt

end ModularForm
end TauCeti
end
