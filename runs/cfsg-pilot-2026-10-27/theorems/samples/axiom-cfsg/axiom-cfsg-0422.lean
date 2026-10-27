public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD

open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

namespace T2Data

variable (D : B.T2Data)

theorem exists_E0_of_actsAs {g h : X} (hg : g ∈ D.P) (hh : h ∈ D.P) (hgh : ActsAs B.Q1 g h) :
    ∃ e : MB, MB.inE0 e = true ∧ g = h * B.ι e := by
  obtain ⟨e, he, hee⟩ := B.mem_E0_of_mem_centralizer_Q1 D.isPGroup
    (mul_mem (inv_mem hh) hg) (mem_centralizer_Q1_of_actsAs hgh)
  exact ⟨e, he, by rw [hee, mul_inv_cancel_left]⟩

end T2Data
end BData
end KD8abB
end CFSG.OddStandard.SmallF3.L33.KD
end
