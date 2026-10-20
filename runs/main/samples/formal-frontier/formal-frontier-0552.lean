@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w v t

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]

variable {J : Type v} [Category.{t} J]

theorem stageHomLimitMap_bijective
    (F : I ⥤ FintypeCat.{max u w})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (G : J ⥤ FintypeCat.{max u w})
    (d : Cone (G ⋙ FintypeCat.toProfinite)) (hd : IsLimit d) :
    Function.Bijective (stageHomLimitMap F c hc G d) := by
  constructor
  · intro f g h
    apply hd.hom_ext
    intro j
    have hj := congrArg
      (fun x : (G ⋙ stageHomFunctor F).sections =>
        stageHomToContinuous c (G.obj j) (x.val j)) h
    simpa only [stageHomLimitMap_toContinuous] using hj
  · intro x
    let s : ((G ⋙ FintypeCat.toProfinite) ⋙
        coyoneda.obj (Opposite.op c.pt)).sections :=
      ⟨fun j => stageHomToContinuous c (G.obj j) (x.val j), by
        intro j k arrow
        change stageHomToContinuous c (G.obj j) (x.val j) ≫
          FintypeCat.toProfinite.map (G.map arrow) =
            stageHomToContinuous c (G.obj k) (x.val k)
        have hx := x.property arrow
        change stageHomPost (F := F) (G.map arrow) (x.val j) = x.val k at hx
        exact (stageHomToContinuous_naturality c (G.map arrow) (x.val j)).symm.trans
          (congrArg (stageHomToContinuous c (G.obj k)) hx)⟩
    refine ⟨hd.homEquiv.symm
      ((compCoyonedaSectionsEquiv (G ⋙ FintypeCat.toProfinite) c.pt) s), ?_⟩
    apply (Functor.sections_ext_iff).2
    intro j
    apply (stageHomEquiv c hc (G.obj j)).injective
    change stageHomToContinuous c (G.obj j)
        ((stageHomLimitMap F c hc G d
          (hd.homEquiv.symm
            ((compCoyonedaSectionsEquiv (G ⋙ FintypeCat.toProfinite) c.pt) s))).val j) =
      stageHomToContinuous c (G.obj j) (x.val j)
    exact (stageHomLimitMap_toContinuous F c hc G d _ j).trans
      (hd.homEquiv_symm_π_app
        ((compCoyonedaSectionsEquiv (G ⋙ FintypeCat.toProfinite) c.pt) s) j)

end Profinite
end
