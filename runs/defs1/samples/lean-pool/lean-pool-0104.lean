@[expose] public section

open MvPolynomial Finset

open scoped symmDiff

namespace Nikodym.MultiQuad

noncomputable section

variable {m : ℕ}

/-- Blueprint K02: the multiquadratic order `𝒪_r`. -/
abbrev Order (r : Fin m → ℕ) := MvPolynomial (Fin m) ℤ ⧸ relIdeal r

end
end Nikodym.MultiQuad
end
