public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux

open Matrix CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.SeitzGeneration.Centers
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag

section Choice

variable {ℓ f n p : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_pth_word (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hn : 0 < n) {G : Type*}
    [Group G] (π : SUid σ₀ n →* G)
    (hker : ∀ g ∈ π.ker, ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1)
    {E : Subgroup G} (hE : IsElemAbelian p E) {x s : SUid σ₀ n} (hxs : x * s = s * x) {α : K}
    (hα0 : α ≠ 0) (hxp : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = α • 1)
    (hα : ¬ ∃ c : K, c ^ p = α) (hsE : π s ∈ E) :
    ∃ a b : ℕ, ¬ p ∣ b ∧ ∃ ν : K, ν ≠ 0 ∧
      (((x ^ a * s ^ b : SUid σ₀ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p =
        (ν ^ p) • 1 := by
  have hsp : π (s ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hsE
  obtain ⟨β, hβ⟩ := hker (s ^ p) hsp
  have hβ' : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p = β • 1 := by
    rw [← hβ, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hβ0 : β ≠ 0 := scalar_ne_zero_of_matPow hn hβ'
  obtain ⟨a, b, hab, ν, hν⟩ := exists_pth_power_word hp hpK hα0 hβ0
  have hb : ¬ p ∣ b := by
    rintro ⟨t, rfl⟩
    have hpa : ¬ p ∣ a := fun hpa => hab ⟨hpa, dvd_mul_right p t⟩
    apply hα
    refine pth_power_of_pow_coprime hp hα0 hpa (s := ν * (β ^ t)⁻¹) ?_
    rw [mul_pow, inv_pow, ← pow_mul, hν, mul_comm t p, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hβ0), mul_one]
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hν
    exact mul_ne_zero (pow_ne_zero _ hα0) (pow_ne_zero _ hβ0) hν.symm
  exact ⟨a, b, hb, ν, hν0, by rw [pow_word_of_comm hxs hxp hβ' a b, ← hν]⟩

end Choice
end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzCubeUnitaryAux
end
