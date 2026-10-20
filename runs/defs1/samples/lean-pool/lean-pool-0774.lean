@[expose] public section

namespace TauCeti

namespace DavisKahan1970

namespace Section9

/-- Upper-Ritz-vector version of the combined individual-angle envelope. -/
noncomputable def upperIndividualAngleExactBound (ε : ℝ) : ℝ :=
  ((Real.sqrt 7 / 10) / 500 * ε) /
    (1 - (ritzHighCoefficient / 500) * ε)

end Section9
end DavisKahan1970
end TauCeti
end
