@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Category

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem mono_iff_isIso_lift_one {N G Q : C} [GrpObj G] [MonObj Q]
    (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) :
    Mono q ↔ IsIso (hN.lift η[G] (𝟙 (𝟙_ C))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)) := by
  constructor
  · intro hq
    let : Mono q := hq
    have hunit : IsPullback η[G] (𝟙 (𝟙_ C)) q η[Q] :=
      IsPullback.of_vert_isIso_mono
        ⟨by simpa only [Category.id_comp] using IsMonHom.one_hom q⟩
    exact (IsLimit.nonempty_isLimit_iff_isIso_lift hN.isLimit).mp hunit.isLimit'
  · intro he
    let e := hN.lift η[G] (𝟙 (𝟙_ C))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)
    let : IsIso e := he
    let hterminal : IsTerminal N := isTerminalTensorUnit.ofIso (asIso e)
    refine ⟨fun {T} a b hab ↦ ?_⟩
    have hinjective : Function.Injective (IsMonHom.monoidHom q T) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro f hf
      apply Subgroup.mem_bot.mpr
      have hfq : f ≫ q = toUnit T ≫ η[Q] := hf
      calc
        f = hN.lift f (toUnit T) hfq ≫ i := (hN.lift_fst _ _ _).symm
        _ = (toUnit T ≫ e) ≫ i :=
          congrArg (fun k : T ⟶ N ↦ k ≫ i) (hterminal.hom_ext _ _)
        _ = 1 := by simp only [Category.assoc, e, hN.lift_fst, Hom.one_def]
    exact hinjective hab

end CategoryTheory.GrpObj
end
