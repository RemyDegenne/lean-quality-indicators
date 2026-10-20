public section

open MeasureTheory

open scoped ENNReal

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The regularized transport tensor in space-time coordinates, used by
`def:riesz-pressure`. -/
@[expose]
def regPressureSpaceTimeTensor (J U : Vec3 × ℝ → Vec3) :
    Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z => J z i * U z j

end CKN.Leray
end
end
