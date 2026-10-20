@[expose] public section

noncomputable section

open Homogenization MeasureTheory Set

namespace AVenhance.Infra.Section4

/-- Actual primitive amplitudes in the source derivative calculus. -/
def amnrNormalFieldAmplitude (F Cb H : ℝ) : Option (Fin 2 × Fin 2) → ℝ
  | none => F
  | some _ => Cb * H

end AVenhance.Infra.Section4
end
end
