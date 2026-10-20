public section

open Function

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

namespace Finset

section CancelCommMonoid

variable [DecidableEq ι] [CancelCommMonoid M] {s t : Finset ι} {f : ι → M}

@[to_additive]
lemma prod_sdiff_eq_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i = ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i = ∏ i ∈ t, f i :=
  eq_comm.trans <| eq_iff_eq_of_mul_eq_mul <| by
    rw [← prod_union disjoint_sdiff_self_left, ← prod_union disjoint_sdiff_self_left,
      sdiff_union_self_eq_union, sdiff_union_self_eq_union, union_comm]

end CancelCommMonoid
end Finset
end
