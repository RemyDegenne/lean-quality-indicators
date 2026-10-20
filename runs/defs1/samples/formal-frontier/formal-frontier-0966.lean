@[expose] public section

noncomputable section

universe u v

namespace ValuationRing

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ]

/-- The literal image of `(a ^ n)` from the base ring in a localization.  Unlike `Ideal.map`,
this remembers only base-ring multiples. -/
def localizedPowerImage (a : V) (n : ℕ) : Submodule V Vₛ :=
  Submodule.map (Algebra.linearMap V Vₛ) ((Ideal.span {a}) ^ n)

end ValuationRing
end
end
