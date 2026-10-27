public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Matrix

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

local notation "M₂" => Matrix (Fin 2) (Fin 2) (ZMod 2)

theorem card_GL_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  norm_num

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
end
