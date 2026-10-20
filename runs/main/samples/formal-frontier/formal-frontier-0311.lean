public section

set_option warningAsError true

namespace IsFractionRing

variable {A K : Type*} [CommRing A] [IsDomain A]
  [UniqueFactorizationMonoid A] [Field K] [Algebra A K]
  [IsFractionRing A K]

theorem isInteger_of_sq_mul_squarefree
    {f : A} (hf : Squarefree f) {x : K}
    (hx : IsLocalization.IsInteger A (x ^ 2 * algebraMap A K f)) :
    IsLocalization.IsInteger A x := by
  obtain ⟨v, hv⟩ := hx
  have hden : x * algebraMap A K (den A x) = algebraMap A K (num A x) :=
    (num_mul_den_eq_num_iff_eq (x := x) (y := x)).2 rfl
  have hdiv : (den A x : A) * den A x ∣ num A x * num A x * f := by
    refine ⟨v, (FaithfulSMul.algebraMap_injective A K) ?_⟩
    simp only [map_mul]
    rw [← hden, hv]
    ring
  have hden_dvd : (den A x : A) ∣ num A x * num A x := by
    apply hf.dvd_of_squarefree_of_mul_dvd_mul_right
    simpa only [mul_comm] using hdiv
  have hden_unit : IsUnit (den A x : A) :=
    ((num_den_reduced A x).mul_left
      (num_den_reduced A x)).symm.isUnit_of_dvd hden_dvd
  exact isInteger_of_isUnit_den hden_unit

end IsFractionRing
end
