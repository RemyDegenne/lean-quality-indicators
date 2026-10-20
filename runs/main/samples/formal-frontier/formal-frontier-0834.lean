@[expose] public section

open Function

namespace Module.Basis

variable {ι A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

lemma repr_update_of_ne [DecidableEq ι] (b : Basis ι A M) (i : ι) (x y : M)
    (hx : IsUnit (b.repr x i)) (j : ι) (hji : j ≠ i) :
    (b.update i x hx).repr y j =
      b.repr y j - b.repr y i * (↑(hx.unit⁻¹) : A) * b.repr x j := by
  have hmul : (↑(hx.unit⁻¹) : A) * b.repr x i = 1 := by
    simpa only [hx.unit_spec] using (Units.inv_mul hx.unit)
  have hcoord : (b.update i x hx).coord j =
      b.coord j - ((↑(hx.unit⁻¹) : A) * b.repr x j) • b.coord i := by
    apply (b.update i x hx).ext
    intro k
    simp only [coord_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, repr_self]
    by_cases hki : k = i
    · subst k
      simp only [update_same, Finsupp.single_apply, if_neg (Ne.symm hji)]
      rw [mul_right_comm _ (b.repr x j), hmul, one_mul, sub_self]
    · simp only [update_apply, Function.update_of_ne hki, repr_self,
        Finsupp.single_apply, if_neg hki, mul_zero, sub_zero]
  calc
    (b.update i x hx).repr y j =
        b.repr y j - ((↑(hx.unit⁻¹) : A) * b.repr x j) * b.repr y i := by
      simpa only [coord_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul] using congrArg (fun f : M →ₗ[A] A ↦ f y) hcoord
    _ = b.repr y j - b.repr y i * (↑(hx.unit⁻¹) : A) * b.repr x j := by
      rw [mul_comm _ (b.repr y i), ← mul_assoc]

end Module.Basis
end
