@[expose] public section

namespace AlgebraicAnalysis

noncomputable section

namespace OreDivision

variable {B : Type*} [Ring B] (D : OreDivisionDerivation B)

namespace OreAmbient

variable {B A : Type*} [Ring B] [Ring A]
  (D : OreDivisionDerivation B) (O : OreAmbient B A D)

theorem commutator_iterate_pow (p x : A)
    (hpx : p * x - x * p = 1) (j n : ℕ) :
    (((commutatorDerivation p)^[j]) (x ^ n)) =
      if j ≤ n then n.descFactorial j • x ^ (n - j) else 0 := by
  by_cases hjn : j ≤ n
  · simp [hjn, commutator_iterate_pow_of_le p x hpx j n hjn]
  · have hnj : n < j := Nat.lt_of_not_ge hjn
    simp [hjn, commutator_iterate_pow_of_lt p x hpx j n hnj]

end OreAmbient
end OreDivision
end
end AlgebraicAnalysis
end
