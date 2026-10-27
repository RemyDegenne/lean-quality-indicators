public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank

open CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Universal.Unitary (SU)

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)

open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem commute_permSp_swap_zero_one_of_mem (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (e : L ≃* StatedSp 4 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin 4, NsKindSp e t k .unitaryEven) {z : G}
    (hz : z ∈ centralizerPerfectCore (modelToG e (nsTorusSp K (0 : Fin 4) ⊔ nsTorusSp K 1))) :
    ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) * z =
      z * ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) := by
  obtain ⟨F, _, _, _, hF, ι, hι, hpar⟩ :=
    exists_nsUniParam_even_of_three_le hset 3 hK le_rfl e ht hKt hroot
  obtain ⟨x, hx, rfl⟩ := (hpar 0).some.exists_eq_of_mem_overlap hF (by decide) hz
  exact commute_permSp_swap_zero_one hset hK hF (hpar 0).some (hpar 2).some ht hKt x hx

end Swap
end CFSG.SeitzReduction.SymplecticPilot
end
