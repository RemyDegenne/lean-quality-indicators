public section

noncomputable section

namespace SymmetricAlgebra

variable (K : Type*) [CommRing K] (M : Type*) [AddCommMonoid M] [Module K M]

/-- The algebra endomorphism of a symmetric algebra that negates every generator. -/
@[expose] def antipodeAlgHom : SymmetricAlgebra K M →ₐ[K] SymmetricAlgebra K M :=
  lift (-ι K M)

end SymmetricAlgebra
end
end
