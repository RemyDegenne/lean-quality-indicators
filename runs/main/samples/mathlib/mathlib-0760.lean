@[expose] public section

open DirectSum

variable {ι : Type*} {σ S R : Type*}

section DirectSum

variable [DecidableEq ι]

namespace DirectSum

section CanonicallyOrderedAddCommMonoid

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]

theorem coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i ≤ n) :
    ((r * of (fun i => A i) i r') n : R) = r (n - i) * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm

end CanonicallyOrderedAddCommMonoid
end DirectSum
end DirectSum
end
