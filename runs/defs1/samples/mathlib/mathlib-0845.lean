@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : ProjectiveResolution X) {n : ℕ}

/-- If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`. -/
@[simps!]
noncomputable def extAddEquivCohomologyClass :
    Ext X Y n ≃+ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  AddEquiv.symm
    { toEquiv := R.extEquivCohomologyClass.symm
      map_add' := by simp }

end CategoryTheory.ProjectiveResolution
end
