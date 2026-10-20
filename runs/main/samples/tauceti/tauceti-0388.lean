public section

namespace QuadraticMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

section QuotientByRadical

variable {N : Type*} [AddCommGroup N] [Module R N]

@[simp]
theorem IsometryEquiv.restrictProdRadicalOfIsCompl_symm_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : M) :
    (IsometryEquiv.restrictProdRadicalOfIsCompl Q W hW).symm x =
      (W.projectionOnto Q.radical hW.symm x, Q.radical.projectionOnto W hW x) := by
  -- The inverse isometry coerces to the inverse of its underlying `LinearEquiv`, so apply the
  -- public inverse formula for `prodEquivOfIsCompl` after exposing that coercion.
  change (W.prodEquivOfIsCompl Q.radical hW.symm).symm x = _
  exact Submodule.prodEquivOfIsCompl_symm_apply hW.symm x

end QuotientByRadical
end QuadraticMap
end
