@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

theorem laurentUnit_not_mem_powerImage (n : ℕ) (hn : 2 ≤ n) :
    laurentUnit K ∉ (powerImage K n).obj (op (op (laurentTest K))) := by
  intro h
  obtain ⟨b, hb⟩ := (mem_powerImage_iff K n (laurentTest K) (laurentUnit K)).1 h
  change (LaurentPolynomial K)ˣ at b
  have hpow : (b : LaurentPolynomial K) ^ n = LaurentPolynomial.T 1 := by
    have hval := congrArg Units.val hb
    change (b : LaurentPolynomial K) ^ n = (laurentUnit K).val at hval
    simpa only [laurentUnit, IsUnit.unit_spec] using hval
  obtain ⟨shift, polynomial, hshift⟩ := LaurentPolynomial.exists_T_pow (b : LaurentPolynomial K)
  have hpolynomial : Polynomial.toLaurent (polynomial ^ n) =
      LaurentPolynomial.T (n * shift + 1 : ℕ) := by
    rw [map_pow, hshift, mul_pow, hpow, LaurentPolynomial.T_pow,
      ← LaurentPolynomial.T_add]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_comm]
  have hp : polynomial ^ n = (Polynomial.X : Polynomial K) ^ (n * shift + 1) :=
    Polynomial.toLaurent_injective (by simpa [Polynomial.toLaurent_X_pow] using hpolynomial)
  have hdegree := congrArg Polynomial.natDegree hp
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_pow] at hdegree
  have hdiv : n ∣ 1 := by
    have hnshift : n ∣ n * shift := ⟨shift, rfl⟩
    have hndegree : n ∣ n * shift + 1 := ⟨polynomial.natDegree, hdegree.symm⟩
    simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hndegree hnshift
  have hn1 : n = 1 := Nat.dvd_one.mp hdiv
  omega

end AlgebraicGeometry
end
