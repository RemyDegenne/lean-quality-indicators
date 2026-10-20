@[expose] public section

open Homogenization

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4

theorem sc_list_abs_sum_le {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ L, |f a| ≤ c) : |(L.map f).sum| ≤ (L.length : ℝ) * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    calc _ ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
      _ ≤ c + (L.length : ℝ) * c := add_le_add h1 h2
      _ = ((L.length : ℝ) + 1) * c := by ring

end AVenhance.Infra.Section5.Contracts
end
end
