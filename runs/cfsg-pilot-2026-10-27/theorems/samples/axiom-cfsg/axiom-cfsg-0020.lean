public section

namespace CFSG.AGLEmbedding.MonsterThree

open CFSG.Sporadic.Bridge.Y443 CFSG.Blueprint.NativeSporadic

open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

theorem x_eq_of_path {a b c : Fin 12} (hab : adjB a b = true) (hbc : adjB b c = true)
    (h : x a = x b) : x b = x c := by
  by_cases hac : a = c
  · rw [← hac]
    exact h.symm
  · have hna : ¬ y443Adjacent a c := by
      rw [adjacent_iff_adjB, adjB_false_of_path a b c hab hbc hac]
      exact Bool.false_ne_true
    have h2 : (x a * x c) ^ 2 = 1 := x_nadj hac hna
    have h3 : (x b * x c) ^ 3 = 1 := x_adj (ne_of_adjB b c hbc) (adj_of_adjB hbc)
    rw [h] at h2
    have h1 : x b * x c = 1 := by
      calc x b * x c = (x b * x c) ^ 3 * ((x b * x c) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    exact (mul_eq_one_iff_eq_inv.1 h1).trans (x_inv c)

end CFSG.AGLEmbedding.MonsterThree
end
