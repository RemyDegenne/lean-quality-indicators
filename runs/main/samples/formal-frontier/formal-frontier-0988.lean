public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

theorem JointlySchemeTheoreticallyDominant.over_hom_ext
    {S : Scheme.{u}} {Y Z : Over S} {f : ∀ j, X j ⟶ Y.left}
    (hf : JointlySchemeTheoreticallyDominant f) {g h : Y ⟶ Z} [IsSeparated Z.hom]
    (eq : ∀ j, f j ≫ g.left = f j ≫ h.left) : g = h := by
  let X' (j : J) : Over S := Over.mk (f j ≫ Y.hom)
  let f' (j : J) : X' j ⟶ Y := Over.homMk (f j)
  have eq' (j : J) : f' j ≫ g = f' j ≫ h := by
    apply CostructuredArrow.ext
    exact eq j
  have hker : (equalizer.ι g h).left.ker = ⊥ := by
    apply le_bot_iff.mp
    rw [← hf]
    refine le_iInf fun j ↦ ?_
    simpa only [← Over.comp_left, equalizer.lift_ι, f', Over.homMk_left] using
      (equalizer.lift (f' j) (eq' j)).left.le_ker_comp (equalizer.ι g h).left
  have : IsIso (equalizer.ι g h).left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  apply CostructuredArrow.ext
  rw [← cancel_epi (equalizer.ι g h).left]
  exact congr($(equalizer.condition g h).left)

end AlgebraicGeometry
end
end
