public section

universe u v

namespace groupCohomology

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

open HomologicalComplex.HomologySequence

open Limits

theorem isIso_δ_of_isZero (n : ℕ) (h : IsZero (groupCohomology X.X₂ n))
    (hs : IsZero (groupCohomology X.X₂ (n + 1))) :
    IsIso (δ hX n (n + 1) rfl) := SnakeInput.isIso_δ _ h hs

end groupCohomology
end
