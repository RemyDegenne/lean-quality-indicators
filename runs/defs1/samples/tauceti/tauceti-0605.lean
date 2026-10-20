public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] {M : X.Modules} [SheafOfModules.isInvertible X M]
  {U : X.Opens} {e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U}
  {hU : Dense (U : Set X)} {D : CartierDivisor X}

/-- If `D` is the class of the inverse of the rational basis function over the domain of every
rank-one trivialization of `M`, then the rational embedding of `M` factors through an isomorphism
`M ≅ 𝒪_X(D)`. -/
def isoSheafOfRestrictEq
    (hD : ∀ (V : X.Opens) [Nonempty V]
      (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V),
      D |_ V = rationalUnitClass X V
        (-Additive.ofMul (trivializationGeneratorRationalUnit M e hU t))) :
    M ≅ D.sheaf :=
  have := isIso_sheafLift_rationalTrivializationHom hD
  asIso (D.sheafLift _ (rationalTrivializationHom_app_mem_sections hD))

end Scheme.CartierDivisor
end
end AlgebraicGeometry
end TauCeti
end
