@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

section Braided

section PairRaw

@[reassoc]
theorem pairRaw_actLeft_snd
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (A : D) [MonObj A] [IsCommMonObj A] (M : Mod D A) (M' : Mod D A)
    (d : ModDualityDatum A M M') :
    (M'.X ◁ actLeft A M.X) ≫ pairRaw A M M' d =
      (α_ M'.X A M.X).inv ≫ ((β_ M'.X A).hom ▷ M.X) ≫
        (α_ A M'.X M.X).hom ≫ (A ◁ pairRaw A M M' d) ≫ μ[A] := by
  rw [← pairRaw_actRight_fst, pairRaw_slide]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end PairRaw
end Braided
end RS
end
