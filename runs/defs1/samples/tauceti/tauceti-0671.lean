public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The column group of a `μ`-tableau is the product, over the columns of `μ`, of the symmetric
groups of the columns. -/
def colSubgroupMulEquiv (t : YoungTableau μ) :
    colSubgroup t ≃* ∀ j, Equiv.Perm ↥(μ.col j) :=
  (MulEquiv.subgroupCongr (colSubgroup_def t)).trans <|
    (fiberSubgroupMulEquivPiPerm (colIndex t)).trans
      (MulEquiv.piCongrRight fun j => (colFiberEquiv t j).permCongrHom)

end YoungTableau
end TauCeti
end
