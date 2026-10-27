public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster CFSG.Monster.B
  CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.Griess
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.LocalAnalysis.ComponentInitial

open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem not_isComponent_of_mulEquiv (e : A ≃* B) (h : ∀ K : Subgroup A, ¬ CFSG.IsComponent K) :
    ∀ K : Subgroup B, ¬ CFSG.IsComponent K := fun K hK =>
  h (K.map e.symm.toMonoidHom) (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hK)

end Transport
end CFSG.Monster.B.CTIB
end
