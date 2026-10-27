public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix

section Cls

variable {K : Type} [Field K]

variable {n : ℕ} [NeZero n]

theorem rhoEnt_comm_aa (σ : K ≃+* K) (A : Matrix (Fin 2) (Fin 2) K) (a : Kˣ) (c c' : Fin 5) :
    rhoEnt σ A c c' * (d8EvU c' a a : K) = (d8EvU c a a : K) * rhoEnt σ A c c' := by
  fin_cases c <;> fin_cases c' <;> simp [rhoEnt, d8EvU, mul_comm]

end Cls
end CFSG.RankThree.PartOne.KFOUT3
end
