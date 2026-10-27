@[expose] public section

namespace BGS.Markoff

universe u

/-- The intrinsic normalized-coordinate condition for a parabolic trace. -/
def IsNormalizedParabolicCoordinate {R : Type u} [OfNat R 4] [Pow R ℕ]
    (a : R) : Prop :=
  a ^ 2 = 4

end BGS.Markoff
end
