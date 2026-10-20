public section

namespace TauCeti.DynkinType

open Set

theorem exists_e6MinusculeWeight_apply_eq_neg_one (i : Fin 6) :
    ∃ a : Fin 27, e6MinusculeWeight a i = -1 := by
  fin_cases i <;> decide +kernel

end TauCeti.DynkinType
end
