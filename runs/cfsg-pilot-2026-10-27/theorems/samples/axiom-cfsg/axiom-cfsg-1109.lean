public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Alternating CFSG.Open

open Matrix

namespace LspNorm

section Basic

variable {m : ℕ} {K : Type} [Field K]

theorem spForm_zero_symm {u w : Fin m ⊕ Fin m → K} (h : spForm m K u w = 0) :
    spForm m K w u = 0 := by
  rw [← spForm_isAlt.neg_eq u w, h, neg_zero]

end Basic
end LspNorm
end CFSG.RankThree.GF2n.Stroth80
end
