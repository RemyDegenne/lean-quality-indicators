public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem c13_cmap_mul (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho,
      (a * b) * (t * (a * b) * t⁻¹) = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by
  intro a ha b hb
  have ht := c13_t_data hc.toCtx13A
  have hta : t * a * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hc.normal_Y.2 t ht.1 a ha
  have htb : t * b * t⁻¹ ∈ ctxYq t tau x₁ x₂ rho := hc.normal_Y.2 t ht.1 b hb
  have hcomm : b * (t * a * t⁻¹) = (t * a * t⁻¹) * b :=
    hc.Q_comm b (ctxYq_le_ctxQ hb) (t * a * t⁻¹) (ctxYq_le_ctxQ hta)
  calc (a * b) * (t * (a * b) * t⁻¹)
      = a * b * (t * a * t⁻¹) * (t * b * t⁻¹) := by
        rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group]
        group
    _ = a * (t * a * t⁻¹) * b * (t * b * t⁻¹) := by
        rw [show a * b * (t * a * t⁻¹) * (t * b * t⁻¹) =
          a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) by group, hcomm]
        group
    _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
end
