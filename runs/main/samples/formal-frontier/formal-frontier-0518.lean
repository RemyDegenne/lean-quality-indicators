public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

@[simp]
lemma flasqueResolutionNat_map_f_zero
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    ((flasqueResolutionNat (X := X)).asFunctor.map f).f 0 =
      (flasqueEnvelopeFunctor (X := X)).map f := by
  rfl

end TopCat.Sheaf
end
end
