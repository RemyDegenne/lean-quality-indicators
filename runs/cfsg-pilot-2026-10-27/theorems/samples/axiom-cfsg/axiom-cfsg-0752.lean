public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

open scoped commutatorElement Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))

include hNS h13315 h1356two hH hab

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)

include hhat

theorem comm_DH_UHg_F4 (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    {d u : G} (hd : d ∈ conjClosure S.V3 H ⊓ conjSub (C.g : G)⁻¹ (pCoreOf 2 H))
    (hu : u ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) : d * u = u * d := by
  have hF := S.hypF91_F4 hNS h13315 h1356two hH
  have hne : conjSub (C.g : G)⁻¹ (fsuV1 T V) ≠ fsuV1 T V := by
    intro h
    apply C.V1g_not_le_UH hab hna
    rw [h]
    exact S.V1_le_UH
  have h1 : ⁅d, u⁆ ∈ conjSub (C.g : G)⁻¹ (fsuV1 T V) :=
    (hF.F96_3 hne).1 (Subgroup.commutator_mem_commutator
      ⟨conjClosure_mono S.V3_le_V le_rfl hd.1, hd.2⟩ hu)
  have h2 : ⁅d, u⁆ ∈ conjClosure S.V3 H := by
    rw [commutatorElement_def]
    have h3 : u * d⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (C.UHg_le_normalizer_UH_F4 hNS h13315 h1356two hH hab hhat
        hu) _).mp ((conjClosure S.V3 H).inv_mem hd.1)
    have e : d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) := by group
    rw [e]
    exact (conjClosure S.V3 H).mul_mem hd.1 h3
  have h4 := C.V1g_inf_UH hab hna h1 h2
  rw [commutatorElement_def] at h4
  calc d * u = d * u * d⁻¹ * u⁻¹ * (u * d) := by group
    _ = u * d := by rw [h4, one_mul]

end Hat
end Conf
end NonAb
end Setting4
end CFSG.Quasithin.H13.A6
end
