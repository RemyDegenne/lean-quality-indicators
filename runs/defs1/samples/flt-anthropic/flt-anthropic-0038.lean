namespace P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul

attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

p2m_open

open scoped NNReal

noncomputable section

namespace NumberField

namespace AdelicFourier

namespace RowModule

p2m_open

section RowMul

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

variable [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]

def rowModulus : GL (Fin 2) A →* ℝ≥0 where
  toFun g := addEquivAddHaarChar (rowMul g)
  map_one' := by rw [rowMul_one]; exact addEquivAddHaarChar_refl
  map_mul' g h := by rw [rowMul_mul, addEquivAddHaarChar_trans]

end RowMul
end RowModule
end AdelicFourier
end NumberField
end
end P2MW.S_NumberField_AdelicFourier_addHaar_image_vecMul_eq_ideleNorm_det_mul_and_fourierTransform2_comp_vecMul
