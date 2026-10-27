public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- The reconstructed scalar extension, in the orientation from the descended
algebra to the given stable subalgebra. -/
@[expose] noncomputable def reconstructionEquiv (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) : L ⊗[k] descended P ≃ₐ[L] P :=
  (AlgEquiv.ofInjective (scalarExtensionMap P) (scalarExtensionMap_injective P)).trans
    (Subalgebra.equivOfEq _ _ (baseChange_descended_eq P hP))

end GaloisDescent
end
