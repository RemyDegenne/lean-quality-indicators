public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace CPair

variable (P : CPair S T₁)

theorem exists_n_eq : ∃ b ∈ S.B, P.W.D.v = P.V.D.w₁ * (S.x * P.V.yi) * b :=
  ⟨_, P.tau_mem, by group⟩

end CPair
end KD8c
end CFSG.ComponentClassification.HSFLit
end
