public section

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K]
  (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The Galois action on `N`-torsion.** This is the restriction of
`pointGaloisAction` to the subgroup killed by `N`. -/
noncomputable def torsionGaloisAction (N : ℤ) :
    (K ≃ₐ[F] K) →*
      Multiplicative (AddAut (AddSubgroup.torsionBy ((W⁄K).toAffine.Point) N)) where
  toFun e := Multiplicative.ofAdd ((Affine.Point.mapEquiv W e).torsionByCongr N)
  -- As for `pointGaloisAction`, `1` and `e * f` unfold to `refl` and `f.trans e`.
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext P
    rw [toAdd_ofAdd, AddEquiv.torsionByCongr_apply_coe, toAdd_one, AddAut.zero_apply]
    exact DFunLike.congr_fun (Affine.Point.mapEquiv_refl W) P.1
  map_mul' e f := by
    apply Multiplicative.toAdd.injective
    ext P
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, AddAut.add_apply,
      AddEquiv.torsionByCongr_apply_coe, AddEquiv.torsionByCongr_apply_coe,
      AddEquiv.torsionByCongr_apply_coe]
    exact DFunLike.congr_fun (Affine.Point.mapEquiv_trans W f e) P.1

end WeierstrassCurve
end
