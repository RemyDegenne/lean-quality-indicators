public section

open CFSG.Open

open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Thm53A

variable {G : Type u} [Group G]

theorem le_normalizer_sectionCentralizer {B X Y : Subgroup G}
    (hX : B ≤ Subgroup.normalizer (X : Set G)) (hY : B ≤ Subgroup.normalizer (Y : Set G)) :
    B ≤ Subgroup.normalizer ((sectionCentralizer X Y : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb x hx
  obtain ⟨hxX, hxY, hxc⟩ := mem_sectionCentralizer_iff.mp hx
  refine mem_sectionCentralizer_iff.mpr ⟨?_, ?_, fun y hy => ?_⟩
  · exact mul_mem (mul_mem (hX hb) hxX) (inv_mem (hX hb))
  · exact mul_mem (mul_mem (hY hb) hxY) (inv_mem (hY hb))
  · have hy' : b⁻¹ * y * b ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hY (inv_mem hb)) y).mp hy
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.mp (hX hb) _).mp (hxc _ hy')
    have e : ⁅b * x * b⁻¹, y⁆ = b * ⁅x, b⁻¹ * y * b⁆ * b⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact h1

end Thm53A
end CFSG.SignalizerFunctorTheorem.McBride.Near
end
