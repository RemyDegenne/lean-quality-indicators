@[expose] public section

noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

variable {U : ι → Opens X} {D : Type w} [Category.{w'} D]

/-- Extend strictly compatible chart functors along an arbitrary indexed open cover.

The compatibility equations concern the two restrictions from each pairwise intersection.
This is the all-point groupoid form of May's Chapter 2, §7 argument, generalized to covers
without connectedness or intersection-closure conditions and to arbitrary target categories.
Object and morphism universes of the target are independent of the space and cover index. -/
@[no_expose]
noncomputable def descOfIsOpenCover (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j) :
    FundamentalGroupoid X ⥤ D := by
  refine
    { obj := fun x => descentObj hU F hF x.as
      map := fun {x y} p =>
        _root_.Quotient.lift (fun p : Path x.as y.as => descentPathValue hU F hF p)
          (fun _ _ hpq => descentPathValue_homotopic hU F hF hpq) p
      map_id := ?_
      map_comp := ?_ }
  · intro x
    exact descentPathValue_refl hU F hF x.as
  · intro x y z p q
    exact Path.Homotopic.Quotient.ind₂
      (fun p q => descentPathValue_trans hU F hF p q) p q

end FundamentalGroupoid
end
end
