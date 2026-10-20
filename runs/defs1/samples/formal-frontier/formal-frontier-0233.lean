public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]
  (V : Type u) [AddCommGroup V] [Module K V]
  (W : Type u) [AddCommGroup W] [Module K W]

/-- The underlying zero-vector scheme is `Spec K` over itself. -/
def vectorGroupUnderlyingZeroIso [Subsingleton V] :
    (vectorGroupScheme K V).X ≅ Over.mk (𝟙 (Spec (.of K))) :=
  ((Limits.isLimitEquivIsTerminalOfIsEmpty (Over (Spec (.of K)))
    ((Grp.forget (Over (Spec (.of K)))).mapCone
      (vectorGroupBasisFan K V (Module.Basis.empty V :
        Module.Basis PEmpty.{u+1} K V))))
    (vectorGroupBasisFan_forget_isLimit K V (Module.Basis.empty V :
      Module.Basis PEmpty.{u+1} K V))).uniqueUpToIso Over.mkIdTerminal

end AlgebraicGeometry
end
end
