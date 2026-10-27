public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace CtxB

variable {K : Subgroup G} {t₀ : G} (C : CtxB T L V H K t₀)

include C

theorem comm (hSzB : SzAutBorelThree) (hA37 : A37ForSQTK)
    (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {e : ℕ} (hSz : IsSz e (cStar K)) {y : G} (hy : y ∈ l1 T L V) (hy3 : y ^ 3 = 1) {k : G}
    (hk : k ∈ K) : y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H :=
  mem_O2H_of_commute ⟨y, Setting147.l1H' C.S hy⟩ ⟨k, C.hKH hk⟩ (comm_of_conj_eq
    (C.centralizes hSzB hA37 h29 h1222 h1332 h1334 hSz hy hy3
      (mem_modO2Image'.mpr ⟨⟨k, C.hKH hk⟩, hk, rfl⟩)))

end CtxB
end CFSG.Quasithin.H13.L32A.C
end
