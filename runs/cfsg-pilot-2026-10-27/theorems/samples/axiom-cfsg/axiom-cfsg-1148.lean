public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem mem_Zs_of_comm_z {n : G} (hn : n ∈ c.N1) (hnz : n * z = z * n)
    (hρ : c.rho ⟨n, hn⟩ = 1) : n ∈ c.Zs := by
  have hcz : n ∈ (L ⊓ centralizer ({t} : Set G)) ⊔ zpowers z :=
    (c.h.normalizer_Q_cent_z_iff c.hα c.hF c.hWr c.hBD).1 ⟨c.mem_Nc.1 (c.N1_le_Nc hn), hnz⟩
  have hAB : zpowers z ≤ centralizer ((L ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun a ha => c.h.conf.cfg.z_comm_of_mem_A ha.1
  obtain ⟨ℓ, hℓ, w, hw, hnℓ⟩ := exists_mul_of_mem_sup_of_le_centralizer hAB hcz
  rcases mem_zpowers_sq_eq_one c.h.z_sq hw with hw1 | hw1
  · rw [hw1, mul_one] at hnℓ
    subst hnℓ
    have hconv := c.rho_conv ⟨n, hn⟩ hnz (c.W_le_normE hℓ)
    rw [hρ] at hconv
    have h1 : convN (⟨n, c.W_le_normE hℓ⟩ : normalizer (E : Set G)) = 1 :=
      (Prod.ext_iff.1 hconv.symm).1
    have hcomm : ∀ e ∈ E, n * e = e * n := by
      intro e he
      have := congrArg (fun φ : MulAut ↥E => ((φ ⟨e, he⟩ : ↥E) : G)) h1
      simp only [convN_coe] at this
      calc n * e = (n * e * n⁻¹) * n := by group
        _ = e * n := by rw [this]; rfl
    rcases c.h.wf.cent n hℓ.1 hcomm with h2 | h2
    · rw [h2]; exact c.Zs.one_mem
    · rw [h2]; exact c.t_mem_Zs
  · exfalso
    rw [hw1] at hnℓ
    obtain ⟨e, he, b, hb, hℓeb⟩ := c.exists_eq_mul_of_mem_W hℓ
    have hℓα : ℓ * α = α * ℓ := by
      rw [hℓeb]
      have h1 : e * α = α * e := (c.mem_Qs.1 (c.E_le_Qs he)).2
      have h2 : b * α = α * b := c.h.BS b hb α c.hα.mem
      calc e * b * α = e * (α * b) := by rw [mul_assoc, h2]
        _ = α * (e * b) := by rw [← mul_assoc, h1, mul_assoc]
    have hℓt : ℓ * t = t * ℓ := mem_centralizer_singleton_iff.1 hℓ.2
    have hn2 := (c.mem_N1.1 hn).2
    have : n * α * n⁻¹ = α * t := by
      rw [hnℓ]
      calc ℓ * z * α * (ℓ * z)⁻¹ = ℓ * (z * α * z⁻¹) * ℓ⁻¹ := by group
        _ = ℓ * (α * t) * ℓ⁻¹ := by rw [c.h.z_conj_alpha c.hα]
        _ = (ℓ * α * ℓ⁻¹) * (ℓ * t * ℓ⁻¹) := by group
        _ = α * t := by
          rw [hℓα, hℓt]; group
    rw [hn2] at this
    exact c.h.t_ne (by simpa using this.symm)

end I13Ctx
end CFSG.EvenSporadicStandard.Fin76b
end
