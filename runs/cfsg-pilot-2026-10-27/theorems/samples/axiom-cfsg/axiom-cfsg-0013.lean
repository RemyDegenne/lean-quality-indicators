public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

open scoped commutatorElement

section Pi

variable {G : Type} [Group G] [Finite G]

theorem pi27_ne_one_of_not_mem {W : Subgroup G} {t : G} (ht : t ∈ normalizer (W : Set G))
    (ht2 : t * t = 1) (htW : t ∉ W) : pi27 W ⟨t, ht⟩ ≠ 1 := by
  intro h
  have hker : (⟨t, ht⟩ : ↥(normalizer (W : Set G))) ∈
      (qPi (W.subgroupOf (normalizer (W : Set G)))).ker := h
  obtain ⟨m, hm, hmem⟩ := exists_odd_pow_mem_of_mem_ker_qPi _ hker
  obtain ⟨a, rfl⟩ := hm
  have hpow : (⟨t, ht⟩ : ↥(normalizer (W : Set G))) ^ (2 * a + 1) = ⟨t, ht⟩ := by
    have h2 : (⟨t, ht⟩ : ↥(normalizer (W : Set G))) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
    rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul]
  rw [hpow] at hmem
  exact htW (mem_subgroupOf.mp hmem)

end Pi
end CFSG.OddStandard.Seitz77
end
