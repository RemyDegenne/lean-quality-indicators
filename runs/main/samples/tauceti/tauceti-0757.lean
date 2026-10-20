public section

namespace TauCeti

namespace IntegralLattice

variable (n : ℕ)

variable {n}

variable (n)

variable {n}

variable (n)

variable {n}

variable (n)

@[simp]
theorem checkerboardCyclicQuadraticIsometry_apply (hn : Odd n) (x : ZMod 4) :
    checkerboardCyclicQuadraticIsometry n hn x =
      zmodFourAddEquivCheckerboardDiscriminantGroup n hn x :=
  FiniteQuadraticModule.cyclicIsometryOfGenerator_apply 4 _ _ _ _ x

end IntegralLattice
end TauCeti
end
