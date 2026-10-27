public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof166Res6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {K : Type*} [Field K]

local notation "SL3" => Matrix.SpecialLinearGroup (Fin 3) K

variable [Finite K]

omit [Finite K] in
theorem coe_diagFirst (d : Kˣ) :
    ((diagFirst d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![(d : K), 1, 1] := rfl

end Linear
end CFSG.RankThree.PartTwo.Sec16.Proof166Res6
end
