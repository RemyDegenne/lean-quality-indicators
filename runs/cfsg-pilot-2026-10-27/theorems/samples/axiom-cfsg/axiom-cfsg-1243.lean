public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD

open scoped commutatorElement

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem exists_W_crossed_eq
    (h : d.Hyp) :
    ∃ w ∈ d.W, w⁻¹ * d.t * w * d.t = d.ι (x₄SU 0 1 zero_one_rel) := by
  have hYE := h.Y_eq_E₂
  obtain ⟨x, hx, hxt⟩ := h.exists_E₂_crossed_eq
    (d.ι_mem_pull_iff.2 (genFSU_mem 0) : d.ι (x₁SU 0 1 zero_one_rel) ∈ d.F)
  have hxY : x ∈ d.Y := hYE ▸ hx
  have hsq : ∀ c : F4, d.ι (x₂SU c) * d.ι (x₂SU c) = 1 := fun c => by
    rw [← map_mul, x₂SU_mul, CharTwo.add_self_eq_zero,
      show x₂SU 0 = 1 from ext_mat (by rw [mat_x₂SU, x₂Mat_zero, mat_one]), map_one]
  have hX : ∀ c : F4, d.ι (x₂SU c) ∈ d.Lev := fun c => X₂_le_Lev ⟨x₂SU c, x₂SU_mem c, rfl⟩
  have hconjY : ∀ c : F4, ∀ y ∈ d.Y, d.ι (x₂SU c) * y * (d.ι (x₂SU c))⁻¹ ∈ d.Y :=
    fun c y hy => hYE ▸ (mem_normalizer_iff.1 ((h.le_normalizer_E₂).1 (hX c)) y).1 (hYE ▸ hy)
  obtain ⟨hwY, hwa, hwb⟩ := klein_norm_comm (c := d.ι (x₂SU (F4.ω + 1)))
    (fun y hy z hz => h.Y_comm hy hz) hxY (hconjY 1) (hconjY F4.ω) (hsq 1) (hsq F4.ω)
    (by rw [← map_mul, x₂SU_mul, add_comm]) (by rw [← map_mul, x₂SU_mul])
  refine ⟨_, h.mem_W_of_comm hwY hwa.symm hwb.symm, ?_⟩
  have hU : ∀ {y}, y ∈ d.Y → y ∈ d.U := fun hy => h.E₂_le_U (hYE ▸ hy)
  have hcm : ∀ {y z}, y ∈ d.Y → z ∈ d.Y →
      (y * z)⁻¹ * d.t * (y * z) * d.t = (y⁻¹ * d.t * y * d.t) * (z⁻¹ * d.t * z * d.t) :=
    fun hy hz => crossed_mul h.t_mul_t (h.U_comm_F (hU hz) (h.U_crossed_mem_F (hU hy))).symm
  have hct : ∀ c : F4, (d.ι (x₂SU c) * x * (d.ι (x₂SU c))⁻¹)⁻¹ * d.t *
      (d.ι (x₂SU c) * x * (d.ι (x₂SU c))⁻¹) * d.t = d.ι (conjX₁ c) := fun c => by
    rw [crossed_conj (h.Lev_comm_t (hX c)), hxt, conjX₁, map_mul, map_mul, map_inv]
  rw [hcm (mul_mem (mul_mem hxY (hconjY 1 x hxY)) (hconjY F4.ω x hxY))
      (hconjY (F4.ω + 1) x hxY), hcm (mul_mem hxY (hconjY 1 x hxY)) (hconjY F4.ω x hxY),
    hcm hxY (hconjY 1 x hxY), hxt, hct 1, hct F4.ω, hct (F4.ω + 1), ← norm_conjX₁, map_mul,
    map_mul, map_mul, ← x₁_eq_conjX₁]

end Data.Hyp
end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
end
