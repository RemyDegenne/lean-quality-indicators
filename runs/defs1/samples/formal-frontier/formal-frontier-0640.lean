public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

variable [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]

variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{0}]

variable [hExt : HasExt.{0} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- The positive-degree connecting isomorphism for the functorial envelope is
natural in the input sheaf. -/
@[expose] noncomputable def flasqueEnvelopeConnectingIso (q : ℕ) :
    flasqueEnvelopeQuotientFunctor (X := X) ⋙
        CategoryTheory.Sheaf.functorH
          (Opens.grothendieckTopology X) (q + 1) ≅
      CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) ((q + 1) + 1) :=
  NatIso.ofComponents
    (fun A => (flasqueEnvelopeDerivedSuccIso A q).symm)
    (fun {A B} f => by
      ext x
      exact @CategoryTheory.Abelian.Ext.covariantDimensionShift_naturality
        _ _ _ hExt _ _ (flasqueEnvelopeShortExact A)
          (flasqueEnvelopeShortExact B) (flasqueEnvelopeShortComplexMap f)
            _ (q + 1) x)

end TopCat.Sheaf
end
end
