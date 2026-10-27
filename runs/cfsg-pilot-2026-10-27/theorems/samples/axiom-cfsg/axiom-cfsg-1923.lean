public section

namespace CFSG.Monster.Existence.Compat

open CFSG.Monster.Code CFSG.Open

theorem permLin_B : ∀ i : Fin 12, permLin (B i) = ∑ k, coefB i k • monsterGolayGen k := by
  decide +kernel

end CFSG.Monster.Existence.Compat
end
