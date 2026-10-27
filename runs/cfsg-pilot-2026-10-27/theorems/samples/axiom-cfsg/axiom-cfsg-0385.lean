public section

namespace CFSG.RankThree.PartOne.K133

open CFSG.Assembly.LowTwoRank Matrix Module

open scoped commutatorElement

theorem exists_unip_normalization {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (a : GL n K) (c : Kˣ)
    (hac : a ^ p = Matrix.GeneralLinearGroup.scalar n c) :
    ∃ μ : Kˣ, (μ : K) ^ p = (c : K) ∧
      (((μ⁻¹ : Kˣ) : K) • ((a : GL n K) : Matrix n n K) - 1) ^ p = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ p = (c : K) := by
    have hsurj : Function.Surjective (frobenius K p) :=
      Finite.surjective_of_injective (frobenius_inj K p)
    obtain ⟨μ, hμ⟩ := hsurj (c : K)
    exact ⟨μ, by simpa [frobenius_def] using hμ⟩
  have hμ0 : μ ≠ 0 := by
    intro h0
    have : (c : K) = 0 := by rw [← hμ, h0, zero_pow (Fact.out : p.Prime).ne_zero]
    exact c.ne_zero this
  refine ⟨Units.mk0 μ hμ0, hμ, ?_⟩
  set A : Matrix n n K := ((a : GL n K) : Matrix n n K) with hA
  have hAp : A ^ p = (c : K) • (1 : Matrix n n K) := by
    have := congrArg (fun g : GL n K => (g : Matrix n n K)) hac
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [scalar_eq_smul_one'] at this
    exact this
  have hc : Commute ((((Units.mk0 μ hμ0)⁻¹ : Kˣ) : K) • A : Matrix n n K) 1 := Commute.one_right _
  have := sub_pow_char_of_commute p hc
  rw [this, smul_pow, hAp, one_pow, smul_smul]
  have : (((Units.mk0 μ hμ0)⁻¹ : Kˣ) : K) ^ p * (c : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, Units.val_mk0, hμ]
    simp [c.ne_zero]
  simp only [this]
  simp

end CFSG.RankThree.PartOne.K133
end
