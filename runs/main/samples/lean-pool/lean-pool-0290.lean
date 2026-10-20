@[expose] public section

namespace UnrestrictedBooleanMul

namespace N4

noncomputable section

theorem anfFourProjection_eq_zero_of_degreeLE_three
    {p : ANF 8} (hp : DegreeLE 3 p) : anfFourProjection p = 0 := by
  funext i j k l
  by_cases hcard : ({i, j, k, l} : Finset (Fin 8)).card = 4
  · change (if ({i, j, k, l} : Finset (Fin 8)).card = 4 then
      p.coeff ⟨{i, j, k, l}⟩ else 0) = 0
    rw [ite_eq_left hcard]
    exact hp _ (by simp [hcard])
  · simp [anfFourProjection, hcard]

end
end N4
end UnrestrictedBooleanMul
end
