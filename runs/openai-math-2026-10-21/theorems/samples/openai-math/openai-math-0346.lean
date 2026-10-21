namespace OAI

namespace ThorpNine.Casimir

namespace Thorp.FiniteConvolution

open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G]

lemma power_list_pos {p : G → ℝ} (hp : ∀ g, 0 ≤ p g) (l : List G)
    (hl : ∀ g ∈ l, 0 < p g) : 0 < power p l.length l.prod := by
  induction l with
  | nil => simp [power]
  | cons a l ih =>
    simpa only [List.length_cons,List.prod_cons,power] using
      conv_pos_of hp (power_nonneg hp l.length) (hl a (by simp))
        (ih (fun g hg => hl g (by simp [hg])))

end Thorp.FiniteConvolution
end ThorpNine.Casimir
end OAI
