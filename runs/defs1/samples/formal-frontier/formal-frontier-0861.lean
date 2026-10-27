@[expose] public section

open CategoryTheory

universe u v w

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι]

namespace ModuleCat

/-- The right-row functor is fully faithful at arbitrary carrier heights.
Its inverse on morphisms evaluates a row supported at the chosen index. -/
noncomputable def fullyFaithfulToRightMatrixModCat (i : ι) :
    (toRightMatrixModCat.{u, v, w} R ι).FullyFaithful where
  preimage {X Y} f := ModuleCat.ofHom (X := X) (Y := Y)
    ({ toFun := fun x ↦ f (Pi.single i x) i
       map_add' x y := by
         rw [Pi.single_add]
         exact congrFun (f.hom.map_add _ _) i
       map_smul' r x := by
         obtain ⟨r, rfl⟩ := MulOpposite.op_surjective r
         have h := congrFun
           (toRightMatrixModCat_hom_single_smul R ι f i i r
             (Pi.single i x : (toRightMatrixModCat R ι).obj X)) i
         simpa only [Pi.single_eq_same, RingHom.id_apply] using h } : X →ₗ[Rᵐᵒᵖ] Y)
  map_preimage {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    change f (Pi.single i (x j)) i = f x j
    have h := congrFun (toRightMatrixModCat_hom_single_smul R ι f j i 1 x) i
    simpa only [MulOpposite.op_one, one_smul, Pi.single_eq_same] using h
  preimage_map {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let u : (toRightMatrixModCat R ι).obj X :=
      show (toRightMatrixModCat R ι).obj X from
        @Pi.single ι (fun _ : ι ↦ (X : Type w))
          (fun _ : ι ↦ (inferInstance : Zero (X : Type w)))
          (inferInstance : DecidableEq ι) i x
    have hu : (u i : X) = x :=
      @Pi.single_eq_same ι (fun _ : ι ↦ (X : Type w))
        (fun _ : ι ↦ (inferInstance : Zero (X : Type w)))
        (inferInstance : DecidableEq ι) i x
    change (((toRightMatrixModCat R ι).map f u) i : Y) = (f x : Y)
    exact @Eq.trans (Y : Type w)
      (((toRightMatrixModCat R ι).map f u) i) (f (u i) : Y) (f x : Y)
      (toRightMatrixModCat_map_apply R ι (M := X) (N := Y) f u i)
      (congrArg (fun y : X ↦ (f y : Y)) hu)

end ModuleCat
end
