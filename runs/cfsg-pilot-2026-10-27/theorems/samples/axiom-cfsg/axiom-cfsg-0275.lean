public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

open CFSG.QuasithinUnique.Bridge

open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))

include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)

include hhat

include C in
theorem exists_c1_mem [IsMulCommutative ↥(conjClosure S.V3 H)]
    (h13314 : Stmt13_3_14) :
    ∃ (c₁ : G) (hc₁ : c₁ ∈ H), c₁ ^ 3 = 1 ∧ c₁ ∈ Subgroup.normalizer (S.V3 : Set G) ∧
      ∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H))),
        A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H))
          ⟨c₁, hc₁⟩ w = w → w = 1 := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  obtain ⟨c₁, hc₁L, hc₁3, hρ, -⟩ := C.exists_c1 hNS h13315 h1356two hH hab hhat
  have hc₁H : (c₁ : G) ∈ H := S.L1_le_of_mem_Hz hNS h13315 h1356two hH hc₁L
  have hcV3 : (c₁ : G) ∈ Subgroup.normalizer (S.V3 : Set G) :=
    S.L1T_le_NV3 (le_sup_left (a := S.L1) hc₁L)
  refine ⟨c₁, hc₁H, hc₁3, hcV3, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ hfix
  rw [A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
    A6Mod.secMk_eq_one_iff] at hfix
  rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at hfix
  have hu' : (u : G) ∈ S.V3 := hu
  have hcu : (c₁ : G) * u * (c₁ : G)⁻¹ ∈ S.V3 :=
    (Subgroup.mem_normalizer_iff.mp hcV3 (u : G)).mp hu'
  have h1 : (c₁ : G) * u * (c₁ : G)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
    rw [← S.V3_inf_U0 hNS h13315 h1356two hH h13314]
    refine ⟨S.V3.mul_mem hcu (S.V3.inv_mem hu'), ?_, hfix⟩
    exact (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (hHU hc₁H) (u : G)).mp u.2) ((conjClosure S.V3 H).inv_mem u.2)
  have h2 := S.mem_V1_of_c012 hρ hu' h1
  exact (A6Mod.secMk_eq_one_iff _).2 (S.V1_le_centralizer_QH hNS h13315 h1356two hH h2)

end Hat
end Conf
end NonAb
end Setting4
end CFSG.Quasithin.H13.A6
end
