public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46

open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable {I : Inst S} {H : Hyp S R}

namespace Data6

variable (D : I.Data6 H)

variable (Rl : D.Rel)

include Rl in
theorem q0_holds : S.Q0Holds I.yi I.ki D.v D.w₁ D.w₂ (q0Of D.ε Rl.s1 Rl.s4) := by
  have hγ := Rl.h0
  rcases q0Of_cases D.ε Rl.s1 Rl.s4 with ⟨hq, hε, h1, h4⟩ | ⟨hq, hε, h1, h4⟩ | ⟨hq, hε, h1, h4⟩ |
      ⟨hq, hε, h1, h4⟩ | ⟨hq, hε⟩ <;> rw [hq]
  · rw [h4] at hγ
    exact ⟨Rl.rel.comm_one hε hγ, Rl.rel.sq_one hε hγ h1 h4, Rl.rel.card_Q0⟩
  · rw [h4] at hγ
    refine ⟨?_, ?_, Rl.rel.comm_one hε hγ, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_z]
    · rw [Rl.rel.sq2, h1, h4, I.wV_yi]; rfl
  · rw [h4] at hγ
    refine ⟨?_, ?_, Rl.rel.center_one hε hγ, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_ki]
    · rw [Rl.rel.sq2, h1, h4, I.wV_ki]; rfl
  · rw [h4] at hγ
    refine ⟨?_, ?_, ?_, Rl.rel.center_one hε hγ, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_z, I.wV_ki, ← I.wV_add]; rfl
    · rw [Rl.rel.sq2, h1, h4, I.wV_yi, I.wV_ki, ← I.wV_add]; rfl
    · rw [Rl.rel.comm, hγ, I.wV_ki]
  · obtain ⟨h1, h4⟩ := Rl.h1 hε
    have hact := D.act_holds
    rw [hε] at hact
    refine ⟨?_, ?_, hact, Rl.rel.center_two hε, Rl.rel.card_Q0⟩
    · rw [Rl.rel.sq1, h1, h4, I.wV_zero]
    · rw [Rl.rel.sq2, h1, h4, show lin dCols (0, 0, 0, 0) = (0, 0, 0, 0) by decide, I.wV_zero]

end Data6
end Inst
end CFSG.OddStandard.SmallF3.L33.KD.KD46
end
