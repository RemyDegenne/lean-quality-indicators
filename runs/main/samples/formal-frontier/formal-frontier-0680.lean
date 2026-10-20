public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

lemma isReduced_iff_nilradical_eq_bot (Y : Scheme.{u}) :
    IsReduced Y ↔ Y.nilradical = ⊥ := by
  constructor
  · intro hred
    let _ := hred
    exact Scheme.nilradical_eq_bot
  · intro hnil
    let hred (i : Y.affineCover.I₀) : IsReduced (Y.affineCover.X i) := by
      let hredTop : _root_.IsReduced Γ(Y.affineCover.X i, ⊤) := by
        let U : Y.affineOpens :=
          ⟨(Y.affineCover.f i).opensRange, isAffineOpen_opensRange (Y.affineCover.f i)⟩
        have hU := congrArg (fun I : Y.IdealSheafData ↦ I.ideal U) hnil
        have hredU : _root_.IsReduced Γ(Y, U.1) := by
          rw [← Ideal.isRadical_bot_iff, ← Ideal.radical_eq_iff]
          simpa [Scheme.nilradical] using hU
        let _ := hredU
        exact isReduced_of_injective (IsOpenImmersion.ΓIsoTop (Y.affineCover.f i)).hom.hom
          (IsOpenImmersion.ΓIsoTop
            (Y.affineCover.f i)).commRingCatIsoToRingEquiv.injective
      let _ := hredTop
      exact isReduced_of_isAffine_isReduced (Y.affineCover.X i)
    let _ (i : Y.affineCover.I₀) : IsReduced (Y.affineCover.X i) := hred i
    exact IsReduced.of_openCover Y Y.affineCover

end AlgebraicGeometry
end
end
