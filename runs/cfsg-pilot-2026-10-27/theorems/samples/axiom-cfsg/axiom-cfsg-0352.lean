public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint

open CFSG.LocalAnalysis.EvenBN.Common

open CFSG.ABGLocalTools (IsSylowOf)

open scoped MatrixGroups Pointwise commutatorElement

namespace ProductN1Aux

section Diagonal

variable {G : Type*} [Group G]

theorem diag_surj {t : G} (htt : t * t = 1) {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ Aᵍ[t], a * b = b * a) (hinf : A ⊓ Aᵍ[t] = ⊥) {g : G}
    (hg : g ∈ (A : Set G) * (Aᵍ[t] : Set G)) (hgt : g * t = t * g) :
    ∃ a ∈ A, g = a * (t * a * t⁻¹) := by
  obtain ⟨e, he, e', he', rfl⟩ := Set.mem_mul.1 hg
  have hfix : t * (e * e') * t⁻¹ = e * e' := by
    rw [← hgt]
    group
  have h1 : t * e * t⁻¹ ∈ Aᵍ[t] := conj_mem_conjg htt he
  have h2 : t * e' * t⁻¹ ∈ A := conj_mem_of_mem_conjg he'
  have h3 : t * (e * e') * t⁻¹ = (t * e * t⁻¹) * (t * e' * t⁻¹) := by group
  rw [hfix] at h3
  have hc := hcomm (t * e' * t⁻¹) h2 (t * e * t⁻¹) h1
  have h4 : e⁻¹ * (t * e' * t⁻¹) = e' * (t * e * t⁻¹)⁻¹ := by
    calc e⁻¹ * (t * e' * t⁻¹)
        = e⁻¹ * ((t * e' * t⁻¹) * (t * e * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by group
      _ = e⁻¹ * ((t * e * t⁻¹) * (t * e' * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by rw [← hc]
      _ = e⁻¹ * (e * e') * (t * e * t⁻¹)⁻¹ := by rw [h3]
      _ = e' * (t * e * t⁻¹)⁻¹ := by group
  have h5 : e⁻¹ * (t * e' * t⁻¹) ∈ A ⊓ Aᵍ[t] :=
    mem_inf.2 ⟨mul_mem (inv_mem he) h2, by rw [h4]; exact mul_mem he' (inv_mem h1)⟩
  rw [hinf, Subgroup.mem_bot] at h5
  have h6 : e = t * e' * t⁻¹ := inv_mul_eq_one.1 h5
  have h7 : e' = t * e * t⁻¹ := by
    rw [h6, conj_conj_of_mul_self htt]
  refine ⟨e, he, ?_⟩
  rw [← h7]

end Diagonal
end ProductN1Aux
end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
end
