public section

namespace NFChoice.DirectNominalPrf.Nominal.AtomicRecanonDev

open scoped Fol

open NFChoice.Foundation

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005

open NFChoice.DirectCertificate.ClassBoundaryCoreDev006

open NFChoice.DirectCertificate.ClassBoundaryRawHandlersDev010

/-- Proof-translation construction identified upstream as `representsCvSelf`. -/
@[expose]
noncomputable def representsCvSelf (s : Fol.term LNF) :
    Theory.fst ⊢ represents s (cvPred s) :=
  by
  apply Fol.prf.allI
  exact Fol.biimpReflCertificate _ (mem (&0) (Fol.liftTerm1 s))

end NFChoice.DirectNominalPrf.Nominal.AtomicRecanonDev
end
