public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1132

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA.I113

variable {Q : Type} [Group Q] [Finite Q]

section Cases

variable {B M : Subgroup Q} {c : Q}

theorem centralizer_le_normalizer_of_le {T : Subgroup Q} (hTM : T ≤ M) :
    Subgroup.centralizer (M : Set Q) ≤ Subgroup.normalizer (T : Set Q) :=
  (Subgroup.centralizer_le (s := (T : Set Q)) (t := (M : Set Q)) hTM).trans
    (Subgroup.centralizer_le_normalizer _)

end Cases
end CFSG.LocalAnalysis.GLTheoremA.I1132
end
