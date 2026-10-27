public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out

open Matrix

open scoped MatrixGroups

theorem coe_diagGL {K : Type*} [Field K] {n : ℕ} (d : Fin n → Kˣ) :
    ((diagGL d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun j => ((d j : Kˣ) : K)) :=
  rfl

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
end
