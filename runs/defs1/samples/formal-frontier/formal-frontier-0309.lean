@[expose] public section

universe u v

namespace MonoidAlgebra

variable {K : Type u} [Semiring K] {α : Type v}

/-- The zero-generator augmentation of the free-word monoid algebra.

It fixes constant coefficients and sends every letter monomial to zero. No
commutativity assumption on the coefficient semiring is needed: the word map sends
the empty word to one and every nonempty word to zero, which commute with all
coefficients. -/
noncomputable def freeMonoidAugmentation (K : Type u) (α : Type v) [Semiring K] :
    MonoidAlgebra K (FreeMonoid α) →+* K := by
  have commute_freeMonoid_lift_zero (k : K) (w : FreeMonoid α) :
      Commute k (FreeMonoid.lift (fun _ : α ↦ (0 : K)) w) := by
    change k * FreeMonoid.lift (fun _ : α ↦ (0 : K)) w =
      FreeMonoid.lift (fun _ : α ↦ (0 : K)) w * k
    induction w using FreeMonoid.inductionOn' with
    | one => simp only [map_one, mul_one, one_mul]
    | of_mul a w _ =>
      simp only [map_mul, FreeMonoid.lift_eval_of, zero_mul, mul_zero]
  exact liftNCRingHom (RingHom.id K) (FreeMonoid.lift (fun _ : α ↦ (0 : K)))
    (fun k w ↦ commute_freeMonoid_lift_zero k w)

end MonoidAlgebra
end
