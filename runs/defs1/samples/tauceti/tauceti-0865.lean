public section

namespace TauCeti.FiniteBilinearModule

universe u v

variable (A : FiniteBilinearModule.{u})

/-- **The orthogonal quotient of a finite bilinear module.**  The pairing of `A` is restricted to
`H⊥` and then divided by the part of `H` lying in `H⊥`, which is degenerate for the restricted
pairing by
`TauCeti.FiniteBilinearModule.addSubgroupOf_orthogonalComplement_le_radical_restrict`.

No isotropy hypothesis is needed: `H ∩ H⊥` is always killed by the restricted pairing.  When `H`
is isotropic, so that `H ≤ H⊥`, this is the classical `H⊥ / H`.

Exposed for the same reason as `quotientOfLeRadical`, on which it is built: so that its carrier
reduces to the `Submodule` quotient and maps out of it are definable with `Submodule.liftQ`,
`Submodule.mapQ` and `Submodule.Quotient.equiv`, and so that this package is definitionally the
underlying bilinear module of `TauCeti.FiniteQuadraticModule.orthogonalQuotient`. -/
@[expose] noncomputable def orthogonalQuotient (H : AddSubgroup A) : FiniteBilinearModule :=
  (A.restrict (A.orthogonalComplement H)).quotientOfLeRadical
    (H.addSubgroupOf (A.orthogonalComplement H))
    (A.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

end TauCeti.FiniteBilinearModule
end
