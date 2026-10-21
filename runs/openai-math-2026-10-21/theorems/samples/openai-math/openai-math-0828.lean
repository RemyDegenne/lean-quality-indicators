namespace OAI

section

noncomputable section

open Matrix Polynomial

namespace DimensionTen.Border

lemma shift_5 : B1 *ᵥ (Pi.single 1 1 : Fin 20 → ℤ) = d • Pi.single 5 1 := by decide +kernel

end DimensionTen.Border
end
end
end OAI
