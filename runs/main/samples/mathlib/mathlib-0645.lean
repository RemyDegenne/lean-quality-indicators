public section

open Finset

open Multiset

open Polynomial

universe u w

variable {R : Type u} {ι : Type w}

namespace Polynomial

variable (s : Finset ι)

section Semiring

variable {S : Type*} [Semiring S]

theorem degree_list_sum_le_of_forall_degree_le (l : List S[X])
    (n : WithBot ℕ) (hl : ∀ p ∈ l, degree p ≤ n) :
    degree l.sum ≤ n := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    rcases hl with ⟨hhd, htl⟩
    rw [List.sum_cons]
    exact le_trans (degree_add_le hd tl.sum) (max_le hhd (ih htl))

end Semiring
end Polynomial
end
