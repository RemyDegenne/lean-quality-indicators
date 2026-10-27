public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot trivialOnQuot_conjSub)

open scoped commutatorElement

section EC

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem inf_S₁_eq (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W
    S₁ R₁ R₂ t t₁ u₁ u₂) :
    tightCore R ⊓ (S₁ : Subgroup Y) = R₁ ∧ K' ⊓ (S₁ : Subgroup Y) = R₂ := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hK'Ω : K' ∈ CoreAssembly.conjClass (tightCore R) := hs.hK'.1
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR₂ : IsSylow2In R₂ K' :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hyp.hR'.1 hyp.hR'.2.1
  exact ⟨hR₁.2.2 _ inf_le_left (S₁.isPGroup'.to_le inf_le_right) (le_inf hR₁.1 hyp.hR.2.2),
    hR₂.2.2 _ inf_le_left (S₁.isPGroup'.to_le inf_le_right) (le_inf hR₂.1 hyp.hR'.2.2)⟩

end EC
end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
end
