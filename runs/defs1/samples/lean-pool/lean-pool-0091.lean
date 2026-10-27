@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- Permute the first incidence point so that its outer coordinate is first
and its bridge coordinate is third. -/
def cageFirstPointCanonicalEquiv (R : Type*)
    (axis other : NormalizedCoordinateAxis) :
    NormalizedPoint R ≃ NormalizedPoint R :=
  match axis, other with
  | .first, .first => normalizedSwap23Equiv R
  | .first, .second => Equiv.refl _
  | .first, .third => normalizedSwap23Equiv R
  | .second, .first => normalizedSwap12Equiv R
  | .second, .second =>
      (normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)
  | .second, .third =>
      (normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)
  | .third, .first =>
      (normalizedSwap23Equiv R).trans (normalizedSwap12Equiv R)
  | .third, .second =>
      ((normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)).trans
        (normalizedSwap12Equiv R)
  | .third, .third =>
      ((normalizedSwap12Equiv R).trans (normalizedSwap23Equiv R)).trans
        (normalizedSwap12Equiv R)

end
end BGS.Markoff
end
