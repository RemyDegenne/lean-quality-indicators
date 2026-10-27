public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- Semilinear descent for the coefficientwise action on a tensor product.

The inverse is the trace-dual averaging formula; in particular, this equivalence
does not rely on an abstract effective-descent result. -/
noncomputable def fixedScalarExtensionEquiv :
    L ⊗[k] fixedSubmodule (k := k) (L := L) (R := R) ≃ₗ[L] L ⊗[k] R :=
  LinearEquiv.ofBijective (fixedScalarExtension (k := k) (L := L) (R := R))
    ⟨fun x y h => by
        simpa only [traceDualInverse_fixedScalarExtension] using congrArg
          (traceDualInverse (k := k) (L := L) (R := R)) h,
      fun x => ⟨traceDualInverse (k := k) (L := L) (R := R) x,
        fixedScalarExtension_traceDualInverse x⟩⟩

end GaloisDescent
end
