public section

namespace TauCeti

open List

variable {α : Type*} [LinearOrder α]

@[simp]
theorem robinsonSchenstedEquiv_apply_coe (w : List α) :
    (robinsonSchenstedEquiv w : List (List α) × List ℕ) = robinsonSchensted w := (rfl)

end TauCeti
end
