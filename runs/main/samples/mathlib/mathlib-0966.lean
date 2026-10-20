@[expose] public section

universe u v

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp]
theorem commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S :=
  SetLike.coe_injective <| by simp

end VonNeumannAlgebra
end
