public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.B45Mat CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier Matrix

open scoped Kronecker

theorem length_pGen (z : ℤ) : (pGen z).length = 6 := by
  unfold pGen
  split_ifs
  · exact length_n2P
  · rw [n2iP, PM.length_mul, PM.length_mul]; exact length_n2P
  · exact PM.length_ofMat _

end CFSG.Quasithin.HM22
end
