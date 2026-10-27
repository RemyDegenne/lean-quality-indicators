namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial

set_option autoImplicit false

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace E2SOL

section Sat

variable {n : ℕ} {k : Type} [Field k]
    {Zk : Scheme.{0}} (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

noncomputable def satIdeal : Ideal (MvPolynomial (Fin (n + 1)) k) where
  carrier := {p | ∀ d : ℕ, Van ιk d (comp d p)}
  zero_mem' := by
    intro d; rw [comp_zero]; exact Van_zero ιk d
  add_mem' := by
    intro p q hp hq d
    rw [comp_add]; exact Van_add ιk (hp d) (hq d)
  smul_mem' := by
    intro c p hp d
    rw [smul_eq_mul, ← sum_homogeneousComponent c, Finset.sum_mul]
    apply Van_comp_sum
    intro e _
    rcases Nat.lt_or_ge d e with hde | hed
    · have hc0 : comp d (homogeneousComponent e c * p) = 0 := by
        apply Subtype.ext
        simp only [comp, homogeneousComponent_mul_of_mem_left (homogeneousComponent_mem e c) p d,
          if_neg (not_le.mpr hde), Submodule.coe_zero]
      rw [hc0]; exact Van_zero ιk d
    · obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hed
      have hceq : comp (e + d') (homogeneousComponent e c * p) =
          ⟨(comp e c : MvPolynomial (Fin (n + 1)) k) * (comp d' p : MvPolynomial (Fin (n + 1)) k),
            SetLike.mul_mem_graded (comp e c).2 (comp d' p).2⟩ := by
        apply Subtype.ext
        simp only [comp, homogeneousComponent_mul_of_mem_left (homogeneousComponent_mem e c) p (e + d'),
          if_pos (Nat.le_add_right e d'), Nat.add_sub_cancel_left]
      rw [hceq]
      exact Van_mul_left ιk e (comp e c) (hp d')

end Sat
end E2SOL
end
end P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
