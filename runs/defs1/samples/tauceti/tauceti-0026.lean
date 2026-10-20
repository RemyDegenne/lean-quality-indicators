public section

open CategoryTheory Limits

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

section Exactness

variable {R : CommRingCat.{u}}

/-- The kernel of a morphism of quasicoherent sheaves on a spectrum is the sheaf associated
with the kernel of its map on global sections. The comparison uses the counit of
`tilde.adjunction` and the canonical kernel comparison of the exact tilde functor. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tildeKernelIso
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    tilde (kernel ((moduleSpecΓFunctor (R := R)).map f)) ≅ kernel f :=
  PreservesKernel.iso (tilde.functor R) _ ≪≫
    kernel.mapIso _ _
      (@asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M))
      (@asIso _ _ _ _ N.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) N))
      ((tilde.adjunction (R := R)).counit.naturality f)

end Exactness
end
end AlgebraicGeometry
end TauCeti
end
