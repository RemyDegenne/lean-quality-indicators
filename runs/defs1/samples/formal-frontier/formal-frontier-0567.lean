public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

/-- The actual degree-`n + 1` homology of global sections of the functorial
flasque resolution is the same cokernel. -/
@[expose] noncomputable def flasqueResolutionSectionsHomologyIsoCokernel'
    (F : Sheaf AddCommGrpCat X) (n : ℕ) :
    (flasqueResolutionSections F).homology (n + 1) ≅
      cokernel (((toFlasqueEnvelopeQuotient (X := X)).app
        ((flasqueEnvelopeQuotientIterate (X := X) n).obj F)).hom.app
          (op (⊤ : Opens X))) :=
  (flasqueResolutionSections F).homologyIsoSc'
      n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    flasqueResolutionSectionsHomologyIsoCokernel F n

end TopCat.Sheaf
end
end
