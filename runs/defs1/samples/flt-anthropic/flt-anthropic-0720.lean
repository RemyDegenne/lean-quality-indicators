set_option autoImplicit false

noncomputable section

namespace PadicAlgCl

variable (p : ℕ) [Fact p.Prime]

def ringOfIntegers (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Subalgebra ℤ_[p] (PadicAlgCl p) :=
  integralClosure ℤ_[p] (PadicAlgCl p) ⊓ K.toSubalgebra.restrictScalars ℤ_[p]

end PadicAlgCl
end
