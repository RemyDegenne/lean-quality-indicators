public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open CFSG CFSG.OddSolvableUnitary CFSG.RankThree.GroupTheory

open scoped commutatorElement

universe u v

section Seed

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

variable {R : Subgroup (Module.End k V)ˣ} {u s : (Module.End k V)ˣ}

section Squares

variable {G : Type*} [Group G] [HasDistribNeg G]

theorem sq2_anti (a b : G) (ha : a * a = 1) (hb : b * b = 1) (hab : b * a = -(a * b)) :
    (a * b) * (a * b) = -1 := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (-(a * b)) * b := by rw [hab]
    _ = -((a * a) * (b * b)) := by rw [mul_neg, neg_mul]; group
    _ = -1 := by rw [ha, hb, one_mul]

end Squares
end Seed
end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
end
