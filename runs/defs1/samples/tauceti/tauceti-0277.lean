public section

namespace TauCeti

variable {G : Type*} [Group G] (N : Subgroup G) [N.Characteristic]

/-- The automorphism of the quotient `G ⧸ N` by a characteristic subgroup `N` induced by an
automorphism of `G`. -/
def _root_.MulAut.mapQuotient : MulAut G →* MulAut (G ⧸ N) where
  toFun φ := QuotientGroup.congr N N φ
    (φ.toMonoidHom_eq_coe ▸ Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]

end TauCeti
end
