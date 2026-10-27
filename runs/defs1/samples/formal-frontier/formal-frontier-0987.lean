@[expose] public section

open Function

universe u v

/-- Equality of ideals identifies their quotient topological additive groups. -/
def Ideal.quotientContinuousAddEquivOfEq
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {I J : Ideal R} (h : I = J) : (R ⧸ I) ≃ₜ+ (R ⧸ J) := by
  subst J
  exact ContinuousAddEquiv.refl _

end
