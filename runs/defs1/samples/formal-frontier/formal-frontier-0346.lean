public section

open scoped TensorProduct

namespace IsLocalRing

universe u v

section

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [IsLocalRing R]
  [Algebra K R]

/--
If a local `K`-algebra has residue field isomorphic to `K` as a `K`-algebra,
its cotangent space is the base change of its module of Kähler differentials to
the residue field.
-/
noncomputable def cotangentSpaceEquivTensorKaehlerOfResidueEquiv
    (e : ResidueField R ≃ₐ[K] K) :
    LinearEquiv (RingHom.id (ResidueField R)) (CotangentSpace R)
      (ResidueField R ⊗[R] Ω[R⁄K]) := by
  letI : Algebra.FormallyUnramified K (ResidueField R) :=
    Algebra.FormallyUnramified.of_equiv e.symm
  exact cotangentSpaceEquivTensorKaehlerOfSection (residueSection e)
    (residueSection_isSection e)

end
end IsLocalRing
end
