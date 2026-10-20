public section

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ γ : Type*} [CommRing R]

/-- A bijection of variables preserves ideal-adic restrictedness. -/
noncomputable def restrictedRenameEquiv (I : Ideal R) (e : σ ≃ υ) :
    adicallyRestrictedSubring (σ := σ) I ≃+*
      adicallyRestrictedSubring (σ := υ) I where
  toFun f := ⟨renameEquiv R e f,
    (mem_adicallyRestrictedSubring I _).2
      (isAdicallyRestricted_renameEquiv I e _
        ((mem_adicallyRestrictedSubring I _).1 f.property))⟩
  invFun f := ⟨renameEquiv R e.symm f,
    (mem_adicallyRestrictedSubring I _).2
      (isAdicallyRestricted_renameEquiv I e.symm _
        ((mem_adicallyRestrictedSubring I _).1 f.property))⟩
  left_inv f := by
    apply Subtype.ext
    exact (renameEquiv R e).left_inv f
  right_inv f := by
    apply Subtype.ext
    exact (renameEquiv R e).right_inv f
  map_mul' f g := by
    apply Subtype.ext
    exact (renameEquiv R e).map_mul f g
  map_add' f g := by
    apply Subtype.ext
    exact (renameEquiv R e).map_add f g

end MvPowerSeries
end
