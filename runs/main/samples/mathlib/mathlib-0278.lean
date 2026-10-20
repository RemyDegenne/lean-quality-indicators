@[expose] public section

namespace PNat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

variable {n m : ℕ+}

theorem find_comp_succ (h : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬p 1) :
    PNat.find h = PNat.find h₂ + 1 := by
  refine (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n ↦ ?_⟩
  induction n with
  | one => simp [h1]
  | succ m _ =>
    intro hm
    simp only [add_lt_add_iff_right, lt_find_iff] at hm
    exact hm _ le_rfl

end PNat
end
