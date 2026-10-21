namespace OAI

namespace PermanentBorder.FrobeniusDVR

open IsDiscreteValuationRing

variable {K B : Type*} [CommRing K] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra K B]

local notation "v" => addVal B

variable [CharP B 2]

omit [IsDomain B] [IsDiscreteValuationRing B] in
lemma derivation_square (D : Derivation K B B) (a : B) : D (a^2) = 0 := by
  have htwo : (2 : B) = 0 := CharP.cast_eq_zero _ 2
  simp [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, htwo]

end PermanentBorder.FrobeniusDVR
end OAI
