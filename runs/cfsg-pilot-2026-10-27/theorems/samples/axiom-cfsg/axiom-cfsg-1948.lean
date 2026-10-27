public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

include S

section Abelian

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))

include hNS h13315 h1356two hH hab

theorem exists_conjSub_rho_45_F4
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    ∃ h ∈ H, ∃ w ∈ conjSub h V, ∃ hwN : w ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨w, hwN⟩ = swap 4 5 := by
  by_contra hcon
  push Not at hcon
  apply hna
  refine HypF91.isElemAbelian_conjClosure_of_forall S.elemAbelian_V fun k hk v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨hwN, hρ⟩ := S.rho_conjSub_V_F4 hNS h13315 h1356two hH hab hk hw
  rcases hρ with h1 | h45
  · exact (Subgroup.mem_centralizer_iff.mp ((S.rho_eq_one_iff ⟨w, hwN⟩).1 h1) v hv).symm
  · exact absurd h45 (hcon k hk w hw hwN)

end Abelian
end Setting4
end CFSG.Quasithin.H13.A6
end
