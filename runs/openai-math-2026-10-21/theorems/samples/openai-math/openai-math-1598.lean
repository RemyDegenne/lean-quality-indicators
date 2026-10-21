namespace OAI

noncomputable section

open scoped InnerProductSpace

noncomputable section

theorem commute_all_of_unitary {A : Type*} [CStarAlgebra A] (a : A)
    (ha : ∀ u : unitary A, Commute a (u : A)) : ∀ b, Commute a b := by
  intro b
  have hb : b ∈ Submodule.span ℂ (unitary A : Set A) := by
    rw [CStarAlgebra.span_unitary]; trivial
  induction hb using Submodule.span_induction with
  | mem y hy => exact ha ⟨y,hy⟩
  | zero => exact Commute.zero_right _
  | add x y hx hy hx' hy' => exact hx'.add_right hy'
  | smul c x hx hx' => exact hx'.smul_right c

end
end
end OAI
