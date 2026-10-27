public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem inv_mul_mul_mem_J_of_commutator_mem_J {x g : G} (hxH : x ∈ H z) (hgH : g ∈ H z)
    (hg : ⁅x, g⁆ ∈ J z) : x⁻¹ * (g⁻¹ * x * g) ∈ J z := by
  have hgx : g * x ∈ H z := (H z).mul_mem hgH hxH
  have h1 := inv_conj_mem_J hgx hg
  have e : (g * x)⁻¹ * ⁅x, g⁆ * (g * x) = x⁻¹ * (g⁻¹ * x * g) := by
    rw [commutatorElement_def]; group
  rwa [e] at h1

end CFSG.RankThree.GF2n.Parrott
end
