public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm Pointwise TauCeti.ExactDivisor

namespace TauCeti

variable {N Q : ℕ} {M M' : Matrix (Fin 2) (Fin 2) ℤ} {k : ℤ}

@[simp]
theorem coe_atkinLehnerOperatorCusp (hQ : 0 < Q) (hQN : Q ∣ N) (h : IsAtkinLehnerMatrix N Q M)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (⇑(atkinLehnerOperatorCusp hQ hQN h k f) : ℍ → ℂ) = ⇑f ∣[k] atkinLehnerGL hQ h := (rfl)

end TauCeti
end
