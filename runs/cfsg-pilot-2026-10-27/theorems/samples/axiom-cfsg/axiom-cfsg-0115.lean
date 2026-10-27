public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.CompatibleFamily

open CFSG.Wreathed.LinearLocalTwistMoment CFSG.Semidihedral.Principal

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
  (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

theorem theta_involution_moment (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ((multiplicityColumn basis (fS (r n) : G) (modulus n) 0 χ -
          multiplicityColumn basis (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) χ : ℤ) :
          ℂ) *
        ((basis.representation χ).character t ^ 2 / (basis.representation χ).character 1) =
      0 := by
  obtain ⟨hM4, -, -, hhalf⟩ := modulus_eq_four_mul hn
  have h := principal_Fourier_involution_square_sum hn fS basis ideal B
  have hfun : (fun x : Subgroup.zpowers (fS (r n) : G) =>
      1 - cyclicLinearCharacter (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) x) =
      (fun x => cyclicLinearCharacter (fS (r n) : G) (modulus n) 0 x -
        cyclicLinearCharacter (fS (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) x) :=
    funext fun x => by rw [cyclicLinearCharacter_zero]
  rw [hfun] at h
  simp only [characterPairing_linear_difference hn fS basis] at h
  have htr : (fS (r n) : G) ^ (modulus n / 2) = t := by
    rw [ht, show modulus n / 2 = 2 ^ (n - 2) by omega]
  rw [htr] at h
  rw [← h]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [sq]

end CFSG.Semidihedral.FieldFactorOne
end
