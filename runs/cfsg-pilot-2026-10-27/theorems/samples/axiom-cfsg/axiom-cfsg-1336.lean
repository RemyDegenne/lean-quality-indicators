public section

namespace CFSG.RankThree.PartOne.KFU.OrthChar2

open Matrix

variable {K : Type} [Field K] (b c : K)

section Centralizer

theorem coe_Cu (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ((Cu b c hirr : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Cm b c := rfl

end Centralizer
end CFSG.RankThree.PartOne.KFU.OrthChar2
end
