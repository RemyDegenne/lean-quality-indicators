@[expose] public section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

open CategoryTheory.Functor

open CategoryTheory.Preadditive

universe v v' u u'

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace Limits

section

variable {X Y : C} [HasBinaryBiproduct X Y]

/-- Every split mono `f` with a cokernel induces a binary bicone with `f` as its `inl` and
the cokernel map as its `snd`.
We will show in `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` that this binary bicone is in
fact already a biproduct. -/
@[simps]
def binaryBiconeOfIsSplitMonoOfCokernel {X Y : C} {f : X ⟶ Y} [IsSplitMono f] {c : CokernelCofork f}
    (i : IsColimit c) : BinaryBicone X c.pt where
  pt := Y
  fst := retraction f
  snd := c.π
  inl := f
  inr :=
    let c' : CokernelCofork (𝟙 Y - (𝟙 Y - retraction f ≫ f)) :=
      CokernelCofork.ofπ (Cofork.π c) (by simp)
    let i' : IsColimit c' := isCokernelEpiComp i (retraction f) (by simp)
    let i'' := isColimitCoforkOfCokernelCofork i'
    (splitEpiOfIdempotentOfIsColimitCofork C (by simp) i'').section_
  inl_fst := by simp
  inl_snd := by simp
  inr_fst := by
    dsimp only
    rw [splitEpiOfIdempotentOfIsColimitCofork_section_,
      isColimitCoforkOfCokernelCofork_desc, isCokernelEpiComp_desc]
    dsimp only [cokernelCoforkOfCofork_ofπ]
    let := epi_of_isColimit_cofork i
    apply zero_of_epi_comp c.π
    simp only [sub_comp, comp_sub, Category.comp_id, Category.assoc, IsSplitMono.id, sub_self,
      Cofork.IsColimit.π_desc_assoc, CokernelCofork.π_ofπ, IsSplitMono.id_assoc]
    apply sub_eq_zero_of_eq
    apply Category.id_comp
  inr_snd := by apply SplitEpi.id

end
end Limits
end CategoryTheory
end
end
