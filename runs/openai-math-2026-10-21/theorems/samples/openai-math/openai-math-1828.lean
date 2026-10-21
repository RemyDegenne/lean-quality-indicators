namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.PCP.Expanders

open scoped BigOperators

open MaxCutGames.Foundations.Hastad

open CayleySpectral

theorem card_baseVertex : Fintype.card BaseVertex = baseDegree ^ 4 := by
  simpa only [BaseVertex, Cube, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, baseDegree] using base_arithmetic.2.2.1

end MaxCutGames.Foundations.PCP.Expanders
end
end OAI
