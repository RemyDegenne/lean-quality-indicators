public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

section Radical

theorem parabolicRadical_le_adjointGroup (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ≤ adjointGroup τ K :=
  (parabolicRadical_le_posUnipotent J).trans
    ((posUnipotent_le_parabolicSubgroup J).trans (parabolicSubgroup_le_adjointGroup τ K J))

end Radical
end CFSG.LieType.SeitzGeneration
end
