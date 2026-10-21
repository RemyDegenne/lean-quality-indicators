namespace OAI

namespace StableCoordinate.FilteredRees

open AddMonoidAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

variable (F : ℤ → Submodule k A) [SetLike.GradedMonoid F]

variable (D : Derivation k A A) (m : ℤ)

variable (hshift : ∀ d (a : A), a ∈ F d → D a ∈ F (d + m))

theorem reesDerivation_iterate_coe (p : rees F) (n : ℕ) :
    (((reesDerivation F D m hshift : rees F → rees F)^[n]) p : LaurentPolynomial A) =
      ((shiftedDerivation D m : LaurentPolynomial A → LaurentPolynomial A)^[n]) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', reesDerivation_coe, ih,
        Function.iterate_succ_apply']

end StableCoordinate.FilteredRees
end OAI
