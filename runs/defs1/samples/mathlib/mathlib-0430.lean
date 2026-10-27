@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {T : Type u₁} [Category.{v₁} T]

variable {D : Type u₂} [Category.{v₂} D]

namespace CostructuredArrow

/-- A version of `CostructuredArrow.ofDiagEquivalence` with the roles of the first and second
projection swapped. -/
-- noncomputability is only for performance
noncomputable def ofDiagEquivalence' (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.2) X.1 :=
  (ofDiagEquivalence X).trans <|
    (ofCostructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    CostructuredArrow.mapNatIso (Over.forget X.2).rightUnitor

end CostructuredArrow
end CategoryTheory
end
