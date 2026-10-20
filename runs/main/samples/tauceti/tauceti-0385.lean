public section

open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
  (W : WeierstrassCurve F)
  (Φ : AddSubgroup ((W⁄K)⁄K).toAffine.Point) [Finite Φ]

attribute [local instance] Fintype.ofFinite

variable [W.IsElliptic]

theorem exists_baseChange_eq_veluCurve [IsGalois F K]
    (hΦ : ∀ σ : K ≃ₐ[F] K, ∀ P : (W⁄K).toAffine.Point, Affine.Point.equivBaseChangeSelf _ P ∈ Φ →
      Affine.Point.equivBaseChangeSelf _ (Multiplicative.toAdd (W.pointGaloisAction σ) P) ∈ Φ) :
    ∃ V : WeierstrassCurve F, V⁄K = Affine.veluCurve (W⁄K).toAffine Φ :=
  (mem_range_baseChange_iff_fixed _).mpr fun σ ↦ map_veluCurve W Φ (hΦ σ)

end WeierstrassCurve
end
