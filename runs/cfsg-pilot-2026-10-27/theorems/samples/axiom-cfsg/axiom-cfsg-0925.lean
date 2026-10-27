public section

namespace CFSG.ComponentClassification.HSFLit.AutL2

open CFSG Subgroup Equiv CFSG.GH74.KGroups

open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.HSFLit.AutBeta

variable {G : Type} [Group G] {J : Subgroup G} {n : ℕ} (M : AutModel (Jhat J) (Perm (Fin n)))

variable [Finite G]

theorem l2UnbalancingOuter :
    ∀ (G : Type) [Group G] [Finite G] (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J →
      (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J)) →
      ∀ j ∈ J, j⁻¹ * x ∉ coreActionKernel J := by
  intro G _ _ a x J htri hL j hj hjx
  obtain ⟨-, hxo, -, -, -, hxJ, hDJ⟩ := htri
  have hx2 : x * x = 1 := by rw [← pow_two, ← hxo, pow_orderOf_eq_one]
  have hset : {y | ∃ i ∈ J, ∃ d ∈ ({x} : Set G), y = i⁻¹ * d⁻¹ * i * d} =
      {y | ∃ i ∈ J, y = i⁻¹ * x⁻¹ * i * x} := by
    ext y
    simp
  have hxJ' : closure {y | ∃ i ∈ J, ∃ d ∈ ({x} : Set G), y = i⁻¹ * d⁻¹ * i * d} = J := by
    rw [hset]
    exact hxJ
  have hxN : x ∈ normalizer (J : Set G) := mem_normalizer_of_closure hxJ' (Set.mem_singleton x)
  obtain ⟨n, M, hF, -⟩ := exists_l2Model' hL
  obtain ⟨-, -, hρP⟩ := rhoM_outer M hF hxN hx2 hxJ' hDJ fun d hd => (mem_inf.mp hd).1
  have hjN : j⁻¹ ∈ normalizer (J : Set G) := le_normalizer (J.inv_mem hj)
  have h1 : rhoM M (mul_mem hjN hxN) = 1 := by
    have := (rhoHom_eq_one_iff M ⟨j⁻¹ * x, mul_mem hjN hxN⟩).2 hjx
    rwa [rhoHom_apply, inv_eq_one] at this
  rw [rhoM_mul M hjN hxN] at h1
  have h2 : rhoM M hxN = (rhoM M hjN)⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact hρP (h2 ▸ M.P.inv_mem (rhoM_mem_P M hF.le (J.inv_mem hj)))

end CFSG.ComponentClassification.HSFLit.AutL2
end
