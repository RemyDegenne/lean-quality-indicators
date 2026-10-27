public section

namespace QuadraticMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

section QuotientByRadical

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The direct sum of a complement and the radical maps to their sum in the ambient module. -/
noncomputable def IsometryEquiv.restrictProdRadicalOfIsCompl (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) :
    ((Q.restrict W).prod (0 : QuadraticMap R Q.radical P)).IsometryEquiv Q where
  toLinearEquiv := W.prodEquivOfIsCompl Q.radical hW.symm
  map_app' x := by
    -- Expose the sum map underlying the direct-sum equivalence.
    change Q (W.prodEquivOfIsCompl Q.radical hW.symm x) = _
    rw [Submodule.coe_prodEquivOfIsCompl', QuadraticMap.prod_apply,
      QuadraticMap.restrict_apply, add_comm,
      (QuadraticMap.mem_radical_iff'.mp x.2.2).2]
    simp

end QuotientByRadical
end QuadraticMap
end
