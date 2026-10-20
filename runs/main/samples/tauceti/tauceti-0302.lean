public section

namespace TauCeti.BinaryGolay

open Matrix

@[simp]
theorem generator_castAdd (i j : Fin 12) :
    generator i (j.castAdd 12) = if i = j then 1 else 0 := by
  simp [generator, Matrix.one_apply]

end TauCeti.BinaryGolay
end
