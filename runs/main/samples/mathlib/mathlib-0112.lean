public section

open Function Set Subalgebra MvPolynomial Algebra

universe u v

variable {ι ι' R : Type*} {S : Type u} {A : Type v} {x : ι → A}

variable [CommRing R] [CommRing S] [CommRing A]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

theorem trdeg_eq_zero_iff : trdeg R A = 0 ↔ Algebra.IsAlgebraic R A := by
  by_cases h : Algebra.IsAlgebraic R A
  · exact iff_of_true trdeg_eq_zero h
  rw [← not_iff_not]
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at h ⊢
  exact iff_of_true (trdeg_pos R A).ne' h

end
