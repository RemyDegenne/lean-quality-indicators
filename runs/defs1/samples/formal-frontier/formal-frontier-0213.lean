public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CircleBouquet

/-- Descend maps from the original circles that agree at one. This is
`WidePushout.desc`, with `Homeomorph.ulift` on each factor. -/
def desc {I : Type v} {Y : TopCat.{max u v}} (y : Y)
    (f : I → C(Circle, Y)) (hf : ∀ i, f i 1 = y) :
    space.{u, v} I ⟶ Y :=
  WidePushout.desc (arrows := attach.{u, v} I) (TopCat.const y)
    (fun i ↦ TopCat.ofHom ((f i).comp
      (Homeomorph.ulift.{max u v, 0} (X := Circle) :
        C(ULift.{max u v} Circle, Circle))))
    (by
      intro i
      apply TopCat.ext
      intro x
      change f i 1 = y
      exact hf i)

end CircleBouquet
end
end
