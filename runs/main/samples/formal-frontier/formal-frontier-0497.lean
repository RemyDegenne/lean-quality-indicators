@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace TopCat

theorem openSingularSet_sup {X : TopCat.{u}} (U V : Opens X) :
    openSingularSet U ⊔ openSingularSet V = smallSingularSet (twoOpenCover U V) := by
  ext n x
  change (x ∈ (openSingularSet U).obj n ∨ x ∈ (openSingularSet V).obj n) ↔
    x ∈ (smallSingularSet (twoOpenCover U V)).obj n
  rw [mem_openSingularSet_iff, mem_openSingularSet_iff,
    mem_smallSingularSet_iff]
  constructor
  · rintro (hx | hx)
    · exact ⟨false, by simpa [twoOpenCover] using hx⟩
    · exact ⟨true, by simpa [twoOpenCover] using hx⟩
  · rintro ⟨i, hi⟩
    cases i with
    | false => exact Or.inl (by simpa [twoOpenCover] using hi)
    | true => exact Or.inr (by simpa [twoOpenCover] using hi)

end TopCat
end
end
