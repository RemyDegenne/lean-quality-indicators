public section

namespace CFSG.StandardType.ZS

open Subgroup QuadraticMap

theorem owD3_refl_form {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : A = closure (ClassRefl p Q c))
    {r : U ≃ₗ[ZMod p] U} (hrA : r ∈ A) (hr : IsRefl p r) :
    ∃ (a : U) (ha : Q a ≠ 0), Q a = c ∧
      ∀ v, Q a • r v = Q a • v - polarBilin Q v a • a := by
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have h2K : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    exact hp2 (le_antisymm hle hp.two_le)
  have hclass : r ∈ ClassRefl p Q c :=
    wit_classRefl_of_mem_closure hp hp2 Q hQ c hc hr (hA ▸ hrA)
  obtain ⟨hr2, hrk⟩ := hr
  obtain ⟨_, hisom, a, haQ, hra⟩ := hclass
  have ha : Q a ≠ 0 := by rw [haQ]; exact hc
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  obtain ⟨a', ha', hr_eq⟩ := owCr_refl_form Q hQ h2K hr2 hrk hisom
  have hrefl : owCr_orthRefl Q a' ha' a = -a := by rw [← hr_eq]; exact hra
  have hcoe : ((polarBilin Q a a') / Q a') • a' = (2 : ZMod p) • a := by
    have h := hrefl
    rw [owCr_orthRefl_apply] at h
    have h1 : a = -a + ((polarBilin Q a a') / Q a') • a' := (sub_eq_iff_eq_add.mp h)
    have h2'' : a + a = ((polarBilin Q a a') / Q a') • a' := by
      have := congrArg (fun t => t - (-a)) h1
      rwa [add_sub_cancel_left, sub_neg_eq_add] at this
    rw [two_smul]
    exact h2''.symm
  have hBa' : polarBilin Q a a' ≠ 0 := by
    intro h0
    have hzero : (2 : ZMod p) • a = 0 := by rw [← hcoe, h0]; simp
    rcases smul_eq_zero.mp hzero with h2a | haa
    · exact h2K h2a
    · exact ha_ne haa
  have ha'_eq : a' = ((polarBilin Q a a' / Q a')⁻¹ * 2) • a := by
    have h := congrArg (fun w => ((polarBilin Q a a' / Q a')⁻¹) • w) hcoe
    rw [smul_smul, inv_mul_cancel₀ (div_ne_zero hBa' ha'), one_smul] at h
    exact h.trans (by rw [smul_smul])
  have hl : ((polarBilin Q a a' / Q a')⁻¹ * 2) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (div_ne_zero hBa' ha')) h2K
  have ha'' : Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ≠ 0 := by
    rw [← ha'_eq]; exact ha'
  have hcongr : owCr_orthRefl Q a' ha'
      = owCr_orthRefl Q (((polarBilin Q a a' / Q a')⁻¹ * 2) • a) ha'' := by
    congr 1
  have hr_a : r = owCr_orthRefl Q a ha := by
    rw [hr_eq, hcongr]
    exact owCc_orthRefl_smul Q a hl ha ha''
  refine ⟨a, ha, haQ, ?_⟩
  intro v
  rw [hr_a, owCr_orthRefl_apply, smul_sub, smul_smul]
  congr 1
  field_simp [ha]

end CFSG.StandardType.ZS
end
