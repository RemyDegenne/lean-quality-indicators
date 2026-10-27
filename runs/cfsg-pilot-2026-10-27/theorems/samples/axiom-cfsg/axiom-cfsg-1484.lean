public noncomputable section

namespace CFSG.Fischer

open Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X}

section Star

theorem Pair.starImage_injective_of_one_notMem (hP : Pair X E) {e : X}
    (h : (1 : LocalQuotient E e) ∉ LocalImages E e) : Function.Injective (starImage E e) := by
  refine Pair.starImage_injective hP fun f hf => ?_
  by_contra! hall
  exact h (range_starImage (E := E) e ▸ ⟨⟨f, hf⟩, (starImage_eq_one_iff _).2 hall⟩)

end Star
end CFSG.Fischer
end
