@[expose] public section

open Set Pointwise

namespace SemigroupIdeal

variable {M : Type*}

@[to_additive ]
theorem coe_closure' [Monoid M] {s : Set M} :
    (closure s : Set M) = univ * s := by
  rw [coe_closure, union_eq_right]
  exact fun x hx => ⟨1, mem_univ 1, x, hx, by simp⟩

end SemigroupIdeal
end
