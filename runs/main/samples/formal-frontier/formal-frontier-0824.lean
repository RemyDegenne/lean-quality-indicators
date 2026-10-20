@[expose] public section

noncomputable section

universe u v

namespace MonoidAlgebra

variable {K : Type u} [Semiring K] {ι : Type v}

theorem linearCombination_freeMonoid_of_eq_iff
    (f : ι →₀ MonoidAlgebra K (FreeMonoid ι)) (x : MonoidAlgebra K (FreeMonoid ι)) :
    Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid ι))
      (fun a : ι ↦ single (FreeMonoid.of a) (1 : K)) f = x ↔
      x.coeff 1 = 0 ∧ ∀ (a : ι) (w : FreeMonoid ι),
        x.coeff (w * FreeMonoid.of a) = (f a).coeff w := by
  constructor
  · rintro rfl
    exact ⟨coeff_linearCombination_freeMonoid_of_one f,
      coeff_linearCombination_freeMonoid_of f⟩
  · rintro ⟨h1, ht⟩
    apply coeff_injective
    apply Finsupp.ext
    intro w
    have h (z : FreeMonoid ι) :
        (Finsupp.linearCombination (MonoidAlgebra K (FreeMonoid ι))
          (fun a : ι ↦ single (FreeMonoid.of a) (1 : K)) f).coeff z.reverse =
            x.coeff z.reverse := by
      cases z using FreeMonoid.casesOn with
      | one =>
        have hreverse : FreeMonoid.reverse (1 : FreeMonoid ι) = 1 := rfl
        simpa only [hreverse, coeff_linearCombination_freeMonoid_of_one] using h1.symm
      | of_mul a z =>
        simpa only [FreeMonoid.reverse_mul, FreeMonoid.reverse_of,
          coeff_linearCombination_freeMonoid_of] using (ht a z.reverse).symm
    simpa only [FreeMonoid.reverse_reverse] using h w.reverse

end MonoidAlgebra
end
end
