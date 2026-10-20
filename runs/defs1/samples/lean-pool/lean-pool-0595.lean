@[expose] public section

namespace BGS.Markoff

/-- At `p`, there is an orbit whose complement has at most `p ^ epsilon` points. -/
def HasGiantOrbitAt (p : ℕ) (epsilon : ℝ) : Prop :=
  ∃ x : PuncturedMarkoffSurface (ZMod p),
    (orbitComplementCard x : ℝ) ≤ Real.rpow p epsilon

end BGS.Markoff
end
