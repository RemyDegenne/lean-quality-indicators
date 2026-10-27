@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

/-- The categorical simplicial differential from degree `n + 1` to degree `n`,
transported through `affineChainIso` to finitely supported affine chains. -/
noncomputable def affineBoundaryHom (m n : ℕ) :
    ModuleCat.of ℤ (AffineChain m (n + 1)) ⟶ ModuleCat.of ℤ (AffineChain m n) :=
  (affineChainIso m (n + 1)).inv ≫
    ((affineSSet m).chainComplex affineIntegerCoefficients).d (n + 1) n ≫
      (affineChainIso m n).hom

end Convexity.StdSimplex
end
end
