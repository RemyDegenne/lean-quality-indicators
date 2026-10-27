public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem elem_E {yi : X} (hyi : yi ∈ A.R) (hyi2 : yi ^ 2 = 1) : ElemAbelianTwo (S.E yi) :=
  ⟨fun _ ha _ hb => E_comm S hyi ha hb, fun _ ha => E_sq S hyi hyi2 ha⟩

end CFSG.ComponentClassification.HSFLit.KD46
end
