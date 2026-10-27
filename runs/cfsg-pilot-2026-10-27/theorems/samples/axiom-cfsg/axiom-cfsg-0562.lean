public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace OctFrame

variable {T : TitsSystem G 8} (F : OctFrame T)

theorem comm_X0_X3 (t u : F.K) : ⁅F.X 0 t, F.X 3 u⁆ = F.X' 2 (t * u) := by
  by_cases ht : t = 0
  · subst ht
    simp [F.X_zero, F.X'_zero]
  by_cases hu : u = 0
  · subst hu
    simp [F.X_zero, F.X'_zero]
  have hst : F.sigma t ≠ 0 := (map_ne_zero F.sigma).2 ht
  set c : F.K := (F.sigma t * t)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero hst ht)
  have hsc : F.sigma c = (t ^ 2 * F.sigma t)⁻¹ := by
    rw [hc, map_inv₀, map_mul, F.sigma_sigma]
  have hct : c / F.sigma c = t := by
    rw [hsc, hc]
    field_simp
  have hv : F.X' 8 c ∈ T.Uprime 8 := F.X'_mem (by decide) c
  have hv1 : F.X' 8 c ≠ 1 := F.X'_ne_one (by decide) hc0
  have h := T.lemma34_i F.hT (F.X_mem 3 u) (F.X_ne_one 3 hu) hv hv1
  rw [F.nu_X' (by decide) hc0, show (8 : ℤ) + 8 = 0 + 16 by norm_num, F.X_add_sixteen, hct,
    F.X_inv_odd (j := 3) (by decide)] at h
  have hm3 : (T.mu 3 (F.X 3 u))⁻¹ = T.mu 3 (F.X 3 u) :=
    inv_eq_of_mul_eq_one_right (F.mu_X_mul_self 3 hu)
  have h1 : (T.mu 3 (F.X 3 u))⁻¹ * F.X' 8 c * T.mu 3 (F.X 3 u) = F.X' 6 (u * c) := by
    have := F.mu_X_odd_conj_X' (i := 3) (by decide) hu (j := 8) (by decide) c
    norm_num [wtX'] at this
    rw [hm3] at this ⊢
    exact this
  have hsc0 : F.sigma c ≠ 0 := (map_ne_zero F.sigma).2 hc0
  have h2 : T.mu 8 (F.X' 8 c) * F.X' 6 (u * c) * (T.mu 8 (F.X' 8 c))⁻¹ = F.X' 2 (t * u) := by
    have := F.mu_X'_conj_X' (i := 8) (by decide) hc0 (j := 6) (by decide) (u * c)
    norm_num [wtX'] at this
    rw [this, show (18 : ℤ) = 2 + 16 by norm_num, F.X'_add_sixteen]
    congr 1
    rw [← hct]
    field_simp
  rw [h1, h2] at h
  have hg : F.X 0 t * F.X 0 t ∈ T.Uprime 0 := T.lemma316_iii F.hT (by decide) (F.X_mem 0 t)
  have hgc : F.X 0 t * F.X 0 t * F.X 3 u = F.X 3 u * (F.X 0 t * F.X 0 t) :=
    T.Uprime_comm (j := 0) (k := 3) (by norm_num) (by norm_num) hg (F.X_mem 3 u)
  have key : ⁅F.X 0 t, F.X 3 u⁆ = ⁅(F.X 0 t)⁻¹, F.X 3 u⁆ := by
    have e : F.X 0 t = (F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t) := by group
    conv_lhs => rw [e]
    simp only [commutatorElement_def]
    calc (F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t) * F.X 3 u * ((F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t))⁻¹ *
          (F.X 3 u)⁻¹
        = (F.X 0 t)⁻¹ * (F.X 0 t * F.X 0 t * F.X 3 u) * (F.X 0 t * F.X 0 t)⁻¹ * (F.X 0 t)⁻¹⁻¹ *
          (F.X 3 u)⁻¹ := by group
      _ = (F.X 0 t)⁻¹ * F.X 3 u * (F.X 0 t)⁻¹⁻¹ * (F.X 3 u)⁻¹ := by rw [hgc]; group
  rw [key, h]

end OctFrame
end CFSG.GH74.Tits83
end
