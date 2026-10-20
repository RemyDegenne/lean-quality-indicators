@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory.K0

section LocalIntegerEquivalence

variable (R : Type u) [Ring R] [IsLocalRing R]

/-- K₀ of a possibly noncommutative local ring is additively equivalent to the
integers by dimension over its canonical Jacobson residue division ring.
See Weibel, *The K-book*, Chapter II, §2. -/
@[no_expose]
noncomputable def localEquivInt : K0 R ≃+ ℤ :=
  AddEquiv.ofBijective (localDimensionHom R) (localDimensionHom_bijective R)

end LocalIntegerEquivalence
end KTheory.K0
end
