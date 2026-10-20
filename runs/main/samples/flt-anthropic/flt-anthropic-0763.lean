namespace P2MW.S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

namespace P2mKuroshSpan

section FreeProduct

variable {ι : Type*} {M : ι → Type*} [∀ i, Group (M i)]

variable {Ω : Type*} [MulAction (Monoid.CoprodI M) Ω] {A B : Type*} [AddCommGroup A] [AddCommGroup B]

open Monoid.CoprodI

theorem IsCrossed.ext_of {c c' : Monoid.CoprodI M → Ω → A} (hc : IsCrossed c) (hc' : IsCrossed c')
    (h : ∀ (i : ι) (m : M i), c (of m) = c' (of m)) : c = c' := by
  funext g
  induction g using Monoid.CoprodI.induction_on with
  | one => rw [hc.map_one, hc'.map_one]
  | of i m => exact h i m
  | mul x y hx hy => rw [hc, hc', hx, hy]

end FreeProduct
end P2mKuroshSpan
end P2MW.S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero
